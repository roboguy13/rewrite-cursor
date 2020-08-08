{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Rewrite.Cursor where

import           Data.Set (Set, (\\))
import qualified Data.Set as S

import           Data.List (isPrefixOf)
import           Data.Maybe (fromMaybe, catMaybes)
import           Data.Foldable

import           Control.Monad.State

data Tree a = Tip | Bin (Tree a) a (Tree a)

data Crumb = L | R deriving (Eq, Ord)

-- NOTE: Cursors can only be constructed through the primitives
-- given here. This ensures that clobbered cursors never get
-- used.
--
-- TODO: Does it make sense to *also* provide "unchecked" cursors, which
-- can only be constructed externally (they won't be constructed by any
-- traversal functions inside the library)? As far as checking goes, this
-- would sort of be the opposite of the cursors currently implemented.
newtype Cursor = Cursor [Crumb] deriving (Eq, Ord)

cursorCrumbs :: Cursor -> [Crumb]
cursorCrumbs (Cursor cs) = reverse cs

-- NOTE: Do not export
addCrumb :: Cursor -> Crumb -> Cursor
addCrumb (Cursor cs) c = Cursor (c:cs)

topCursor :: Cursor
topCursor = Cursor []

-- NOTE: Do not export the data constructor
-- TODO: Should this also keep track of the current cursor (as a 'Maybe
-- Cursor')?
data Cursored a = Cursored (Tree a) (Set Cursor)

newtype CursoredM a r = CursoredM (State (Cursored a) r)
  deriving (Functor, Applicative, Monad, MonadState (Cursored a))

putMaybe :: MonadState s m => Maybe s -> m ()
putMaybe (Just x) = put x
putMaybe Nothing  = return ()


mkCursored :: Tree a -> Cursored a
mkCursored x = Cursored x mempty

runCursored :: Cursored a -> Tree a
runCursored (Cursored x _) = x

runCursoredM_ :: CursoredM a r -> Tree a -> Tree a
runCursoredM_ (CursoredM cm) = runCursored . execState cm . mkCursored

-- | Save and restore state
delimitState :: MonadState s m => m r -> m (s, r)
delimitState m = do
  oldState <- get

  r <- m
  modifiedState <- get

  put oldState
  return (modifiedState, r)


simpleRewriteAt_ :: (Tree a -> Tree a) -> Cursor -> CursoredM a (Maybe ())
simpleRewriteAt_ r cursor = do
  Cursored x0 validCursors <- get
  if cursor `S.member` validCursors
    then do
      let validCursors' = S.filter (cursor `doesNotClobber`) validCursors
          newCursored_maybe = Cursored <$> go (cursorCrumbs cursor) x0 <*> pure validCursors'

      putMaybe newCursored_maybe

      return $ void newCursored_maybe

    else return Nothing

    where
      go [] x = Just $ r x
      go (cr:crs) (Bin left _ right) =
        case cr of
          L -> go crs left
          R -> go crs right
      go _ _ = Nothing

-- NOTE: Do not export
setCursoredExpr :: Tree a -> CursoredM a ()
setCursoredExpr x = do
  Cursored _ validCursors <- get
  put (Cursored x validCursors)

cursorDescend :: (Tree a -> Maybe (Tree a)) -> CursoredM a [Cursor]
cursorDescend tr = cursorDescend' tr topCursor

cursorDescend' :: (Tree a -> Maybe (Tree a)) -> Cursor -> CursoredM a [Cursor]
cursorDescend' tr cursorSoFar = cursorDescendM go cursorSoFar
  where
    go crumb = do
      c@(Cursored x validCursors) <- get
      let x'_maybe = tr x

      setCursoredExpr (fromMaybe x x'_maybe)

      return [addCrumb cursorSoFar crumb]

-- | Apply (non-recursively) to all immediate children
cursorDescendM :: Monoid r => (Crumb -> CursoredM a r) -> Cursor -> CursoredM a r
cursorDescendM tr cursorSoFar = do
  c <- get
  case c of
    Cursored Tip _ -> return mempty
    Cursored (Bin left x right) _validCursors -> do

      (Cursored left' leftValidCursors, leftR) <- delimitState $ do
        setCursoredExpr left
        tr L

      (Cursored right' rightValidCursors, rightR) <- delimitState $ do
        setCursoredExpr right
        tr R

      let
            -- TODO: Does this need to be checked for clobbering? Probably
            -- not.
          validCursors =
            S.map (`addCrumb` L) leftValidCursors `S.union` S.map (`addCrumb` R) rightValidCursors

      put (Cursored (Bin left' x right')
                    validCursors)

      return (leftR <> rightR)

-- | Apply recursively using a bottom-up traversal pattern
cursorTransform :: (Tree a -> Maybe (Tree a)) -> CursoredM a [Cursor]
cursorTransform tr = do
  go topCursor
  where
    go cursorSoFar = do
      cursors <- cursorDescendM (\crumb -> go (addCrumb cursorSoFar crumb)) cursorSoFar

      c'@(Cursored x validCursors') <- get

      let x'_maybe = tr x
          validCursors'' =
            case x'_maybe of
              Nothing -> validCursors'
              Just x' -> S.empty --S.filter (cursorSoFar `doesNotClobber`) validCursors'

          x' = fromMaybe x x'_maybe
          cursors' =
            case x'_maybe of
              Nothing -> cursors
              Just _ -> []
      put (Cursored x' validCursors'')
      return (cursors' ++ toList (fmap (const cursorSoFar) x'_maybe))

-- NOTE: Do not export
-- | Only include cursors from the right set which are not clobbered
-- by any cursor in the left set. Similar to 'appendCursors'.
unionCursors :: Set Cursor -> Set Cursor -> Set Cursor
unionCursors as bs = as `S.union` S.filter notClobberedByAs bs
  where
    notClobberedByAs c = all (`doesNotClobber` c) as

-- | Only include cursors from the right set which are not clobbered
-- by any cursor in the left set.
appendCursors :: [Cursor] -> [Cursor] -> [Cursor]
appendCursors as bs = as ++ filter notClobberedByAs bs
  where
    notClobberedByAs c = all (`doesNotClobber` c) as

doesNotClobber :: Cursor -> Cursor -> Bool
x `doesNotClobber` y = not (x `clobbers` y)

-- | I think this forms a partial order on 'Cursor's. In fact, it also has
-- a minimal element: 'topCursor' clobbers everything.
clobbers :: Cursor -> Cursor -> Bool
x `clobbers` y = cursorCrumbs x `isPrefixOf` cursorCrumbs y
