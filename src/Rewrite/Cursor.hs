{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

{-# OPTIONS_GHC -Wall #-}

module Rewrite.Cursor where

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.List (isPrefixOf)
import           Data.Maybe (fromMaybe)
import           Data.Foldable

import           Control.Monad.State

import           Data.Data

data Tree a = Tip | Bin (Tree a) a (Tree a) deriving (Show, Data)

data Crumb = L | R deriving (Eq, Ord, Show)

-- NOTE: Cursors can only be constructed through the primitives
-- given here. This ensures that clobbered cursors never get
-- used.
--
-- TODO: Does it make sense to *also* provide "unchecked" cursors, which
-- can only be constructed externally (they won't be constructed by any
-- traversal functions inside the library)? As far as checking goes, this
-- would sort of be the opposite of the cursors currently implemented.
newtype Cursor = Cursor [Crumb] deriving (Eq, Ord, Show)

cursorCrumbs :: Cursor -> [Crumb]
cursorCrumbs (Cursor cs) = reverse cs

-- TODO: Does 'moveCursorUp' make sense conceptually? If so, how do we know
-- that it is a valid cursor?

-- moveCursorUp :: Cursor -> Cursor
-- moveCursorUp (Cursor xs) = Cursor (init xs)

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

runCursoredM_ :: Tree a -> CursoredM a r -> Tree a
runCursoredM_ t (CursoredM cm) = runCursored . execState cm $ mkCursored t

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
      go (cr:crs) (Bin left x right) =
        case cr of
          L -> Bin <$> go crs left <*> pure x <*> pure right
          R -> Bin <$> pure left <*> pure x <*> go crs right
      go _ _ = Nothing

goLeft :: (Cursor -> CursoredM a r) -> Cursor -> Tree a -> a -> Tree a -> CursoredM a r
goLeft f cursorSoFar left x right = do
  setCursoredExpr left

  r <- f (addCrumb cursorSoFar L)

  Cursored left' _leftValidCursors <- get

  setCursoredExpr (Bin left' x right)
  return r

goRight :: (Cursor -> CursoredM a r) -> Cursor -> Tree a -> a -> Tree a -> CursoredM a r
goRight f cursorSoFar left x right = do
  setCursoredExpr right

  r <- f (addCrumb cursorSoFar R)

  Cursored right' _rightValidCursors <- get

  setCursoredExpr (Bin left x right')
  return r


-- | Rewrite one time, going top-down
rewriteOneTD :: forall a. (Tree a -> Maybe (Tree a)) -> CursoredM a (Maybe Cursor)
rewriteOneTD tr = go topCursor
  where
    go :: Cursor -> CursoredM a (Maybe Cursor)
    go cursorSoFar = do
      Cursored t validCursors <- get

      case tr t of
        Just t' -> do
          put (Cursored t' (S.insert cursorSoFar $ S.filter (cursorSoFar `doesNotClobber`) validCursors))
          return (Just cursorSoFar)

        Nothing -> do
          case t of
            Tip -> return Nothing
            Bin left x right -> do
              leftC_maybe <- goLeft go cursorSoFar left x right

              case leftC_maybe of
                Just _ -> return leftC_maybe
                Nothing -> do
                  goRight go cursorSoFar left x right

-- | Rewrite one time, going bottom-up
rewriteOneBU :: forall a. (Tree a -> Maybe (Tree a)) -> CursoredM a (Maybe Cursor)
rewriteOneBU tr = go topCursor
  where
    go :: Cursor -> CursoredM a (Maybe Cursor)
    go cursorSoFar = do
      Cursored t validCursors <- get

      case t of
        Tip ->
          case tr t of
            Just t' -> do
              put (Cursored t' (S.insert cursorSoFar $ S.filter (cursorSoFar `doesNotClobber`) validCursors))
              return (Just cursorSoFar)

            Nothing -> return Nothing

        Bin left x right -> do
          leftC_maybe <- goLeft go cursorSoFar left x right

          case leftC_maybe of
            Just _ -> return leftC_maybe
            Nothing -> do
              rightC_maybe <- goRight go cursorSoFar left x right
              case rightC_maybe of
                Just _ -> return rightC_maybe
                Nothing ->
                  case tr t of
                    Just t' -> do
                      put (Cursored t' (S.insert cursorSoFar $ S.filter (cursorSoFar `doesNotClobber`) validCursors))
                      return (Just cursorSoFar)
                    Nothing -> return Nothing

-- NOTE: Do not export
setCursoredExpr :: Tree a -> CursoredM a ()
setCursoredExpr x = do
  Cursored _ validCursors <- get
  put (Cursored x validCursors)

cursorDescend :: (Tree a -> Maybe (Tree a)) -> CursoredM a [Cursor]
cursorDescend tr = cursorDescend' tr topCursor

cursorDescend' :: (Tree a -> Maybe (Tree a)) -> Cursor -> CursoredM a [Cursor]
cursorDescend' tr cursorSoFar = cursorDescendM go
  where
    go crumb = do
      Cursored x _validCursors <- get
      let x'_maybe = tr x

      setCursoredExpr (fromMaybe x x'_maybe)

      return [addCrumb cursorSoFar crumb]

-- | Apply (non-recursively) to all immediate children
cursorDescendM :: Monoid r => (Crumb -> CursoredM a r) -> CursoredM a r
cursorDescendM tr = do
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
      cursors <- cursorDescendM (\crumb -> go (addCrumb cursorSoFar crumb))

      Cursored x validCursors' <- get

      let x'_maybe = tr x
          validCursors'' =
            case x'_maybe of
              Nothing -> validCursors'
              Just _ -> S.insert cursorSoFar $ S.filter (cursorSoFar `doesNotClobber`) validCursors'

          x' = fromMaybe x x'_maybe
          cursors' =
            case x'_maybe of
              Nothing -> cursors
              Just _ -> [cursorSoFar]

      put (Cursored x' validCursors'')
      return (cursors' ++ toList (fmap (const cursorSoFar) x'_maybe))

-- NOTE: Do not export
-- | Only include cursors from the right set which are not clobbered
-- by any cursor in the left set. Similar to 'appendCursors'.
unionCursors :: Set Cursor -> Set Cursor -> Set Cursor
unionCursors as bs = S.filter notClobberedByBs as `S.union` S.filter notClobberedByAs bs
  where
    notClobberedByAs c = all (`doesNotClobber` c) as
    notClobberedByBs c = all (`doesNotClobber` c) bs

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

