module Rewrite.Cursor where

import           Data.Set (Set, (\\))
import qualified Data.Set as S

import           Data.List (isPrefixOf)
import           Data.Maybe (fromMaybe, catMaybes)
import           Data.Foldable

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
data Cursored a = Cursored (Tree a) (Set Cursor)

mkCursored :: Tree a -> Cursored a
mkCursored x = Cursored x mempty

runCursored :: Cursored a -> Tree a
runCursored (Cursored x _) = x

simpleRewriteAt_ :: (Tree a -> Tree a) -> Cursor -> Cursored a -> Maybe (Cursored a)
simpleRewriteAt_ r cursor (Cursored x0 validCursors)
  | cursor `S.member` validCursors =
      let validCursors' = S.filter (cursor `doesNotClobber`) validCursors
      in
      Cursored <$> go (cursorCrumbs cursor) x0 <*> pure validCursors'
    where
      go [] x = Just $ r x
      go (cr:crs) (Bin left _ right) =
        case cr of
          L -> go crs left
          R -> go crs right
      go _ _ = Nothing

simpleRewriteAt _ _ _ = Nothing

-- | Apply (non-recursively) to all immediate children
cursorDescend :: (Tree a -> Maybe (Tree a)) -> Cursor -> Cursored a -> (Cursored a, [Cursor])
cursorDescend tr _ c@(Cursored Tip _) = (c, [])
cursorDescend tr cursorSoFar (Cursored (Bin left x right) validCursors) =
  let trLeft_maybe  = tr left
      trRight_maybe = tr right

      trLeft_defaulted  = fromMaybe left trLeft_maybe
      trRight_defaulted = fromMaybe right trRight_maybe

      cursors =
        catMaybes
          [fmap (const (addCrumb cursorSoFar L)) trLeft_maybe
          ,fmap (const (addCrumb cursorSoFar R)) trRight_maybe
          ]

      cursorsDoNotClobber c = all (`doesNotClobber` c) cursors
  in
    (Cursored (Bin trLeft_defaulted
                   x
                   trRight_defaulted)
              (S.fromList cursors `S.union` S.filter cursorsDoNotClobber validCursors)
    ,cursors
    )


-- | Apply recursively using a bottom-up traversal pattern
cursorTransform :: (Tree a -> Maybe (Tree a)) -> Cursored a -> (Cursored a, [Cursor])
cursorTransform tr c0 =
  go topCursor c0
  where
    go cursorSoFar c@(Cursored _ validCursors) =
      let c'@(Cursored x validCursors', cursors) = cursorDescend tr cursorSoFar c
          x'_maybe = tr x
          validCursors'' =
            case x'_maybe of
              Nothing -> validCursors'
              Just x' -> S.empty --S.filter (cursorSoFar `doesNotClobber`) validCursors'

          x' = fromMaybe x x'_maybe
          cursors' =
            case x'_maybe of
              Nothing -> cursors
              Just _ -> []
      in (Cursored x' validCursors'', cursors' ++ toList (fmap (const cursorSoFar) x'_maybe))

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

