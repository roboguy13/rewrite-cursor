{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- {-# OPTIONS_GHC -Wall #-}

-- TODO: Can we make use of information about functions which provably do
-- not clobber cursors (possibly provably by construction)?

module Rewrite.Cursor
  -- (topCursor

  -- ,Cursor
  -- ,Crumb
  -- ,Cursored
  -- ,CursoredM

  -- ,mkCursored
  -- ,runCursoredM
  -- ,execCursoredM

  -- ,cursorUpLevel
  -- ,cursorUpLevelN

  -- ,simpleRewriteAt_

  -- ,cursorDescend
  -- ,cursorDescend'
  -- ,cursorDescendM

  -- ,rewriteOneTD
  -- ,doesNotClobber
  -- ,clobbers
  -- )
  where

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.Map (Map)
import qualified Data.Map as M

import           Data.List (isPrefixOf, mapAccumL)
import           Data.Maybe (fromMaybe)
import           Data.Foldable

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Data
import qualified Data.Generics.Uniplate.DataOnly as Data
import           Data.Generics.Str

import           Control.Applicative

import           Control.Arrow ((***), (&&&))

import Debug.Trace

-- | Selector index
newtype Crumb = Crumb Int deriving (Eq, Ord, Show)

newtype CrumbList = CrumbList [Crumb] deriving (Eq, Ord, Show, Semigroup, Monoid)

-- NOTE: Cursors can only be constructed through the primitives
-- given here. This ensures that clobbered cursors never get
-- used.
--
-- TODO: Does it make sense to *also* provide "unchecked" cursors, which
-- can only be constructed externally (they won't be constructed by any
-- traversal functions inside the library)? As far as checking goes, this
-- would sort of be the opposite of the cursors currently implemented.
newtype Cursor = Cursor Int deriving (Eq, Ord, Show)

getCrumbs :: CrumbList -> [Crumb]
getCrumbs (CrumbList crs) = reverse crs

-- cursorCrumbList :: Cursor -> CrumbList
-- cursorCrumbList (Cursor c) = c

-- cursorCrumbs :: Cursor -> [Crumb]
-- cursorCrumbs = getCrumbs . cursorCrumbList

-- NOTE: Do not export
addCrumb :: CrumbList -> Crumb -> CrumbList
addCrumb (CrumbList cs) c = CrumbList (cs ++ [c]) --CrumbList (c:cs)

-- Cursor ID 0 always refers to the top-level cursor
topCursor :: Cursor
topCursor = Cursor 0

-- NOTE: Do not export the data constructor
-- TODO: Should this also keep track of the current cursor (as a 'Maybe
-- Cursor')? Maybe there shouldn't be a concept of "current cursor," just
-- an internal list of valid (non-clobbered) cursors
data Cursored a =
  Cursored
    a -- Current expression
    CrumbList -- The path we have gone down to get to the current subexpression
    (Map Cursor CrumbList) -- Maps cursor IDs to absolute paths (does not include the current path)
    Int -- Fresh ID for making new cursor IDs

newtype CursoredM a r = CursoredM (State (Cursored a) r)
  deriving (Functor, Applicative, Monad, MonadState (Cursored a))

-- | Lookup relative to the current path
lookupCursor :: Cursor -> CursoredM a (Maybe CrumbList)
lookupCursor c = do
  Cursored _ crs cursors _ <- get

  let crs_list = getCrumbs crs

  case cursors M.!? c of
    Just crumbList
      | crumbs <- getCrumbs crumbList
      , crs_list `isPrefixOf` crumbs ->
          return $ Just $ CrumbList $ drop (length crs_list) crumbs
    _ -> return Nothing

-- | This assumes the @CrumbList@ is relative to the current path
insertCursor :: Cursor -> CrumbList -> CursoredM a ()
insertCursor cursor crs = do
  Cursored e path cursors cursorId <- get

  let pathCrs = crs <> path --path <> crs

  put (Cursored e path (M.insert cursor pathCrs (M.filter (pathCrs `doesNotClobber`) cursors)) cursorId)

crumbDescend :: Crumb -> CursoredM a r -> CursoredM a r
crumbDescend cr action = do
  Cursored e path cursors cursorId <- get

  put (Cursored e (addCrumb path cr) cursors cursorId)
  r <- action
  setPath path
  return r

setPath :: CrumbList -> CursoredM a ()
setPath path = do
  Cursored e _ cursors cursorId <- get
  put (Cursored e path cursors cursorId)

putMaybe :: MonadState s m => Maybe s -> m ()
putMaybe (Just x) = put x
putMaybe Nothing  = return ()

incrCursorId :: CursoredM a ()
incrCursorId = do
  Cursored e cl cursors cursorId <- get
  put (Cursored e cl cursors (cursorId+1))

-- NOTE: Do not export
newCursor :: CrumbList -> CursoredM a Cursor
newCursor crs = do
  Cursored e path cursors cursorId <- get

  let cursor = Cursor cursorId

  insertCursor cursor crs
  incrCursorId
  return cursor

mkCursored :: a -> Cursored a
mkCursored x = Cursored x mempty (M.fromList [(Cursor 0, CrumbList [])]) 1

runCursoredM :: a -> CursoredM a r -> (a, r)
runCursoredM x (CursoredM cm) =
  let (r, Cursored a _ _ _) = runState cm (mkCursored x)
  in (a, r)

execCursoredM :: a -> CursoredM a r -> a
execCursoredM x cm = fst $ runCursoredM x cm

-- | This uses absolute paths
cursorUpLevel :: Cursor -> CursoredM a Cursor
cursorUpLevel = cursorUpLevelN 1

cursorUpLevelN :: Int -> Cursor -> CursoredM a Cursor
cursorUpLevelN n c = do
  cursor_maybe <- lookupCursor c
  case cursor_maybe of
    Nothing ->
      -- We were given an invalid cursor, so we just give back an invalid
      -- cursor
      return c

    Just (CrumbList crumbList) ->
      newCursor (CrumbList (drop n crumbList))

safeIndex :: Crumb -> [a] -> Maybe a
safeIndex (Crumb 0) (x:_) = Just x
safeIndex (Crumb i) (_:xs) = safeIndex (Crumb (i-1)) xs
safeIndex _ _ = Nothing

mkCursoredAction :: (a -> a) -> CursoredM a ()
mkCursoredAction = modifyCursoredExpr

-- NOTE: Do not export
setCursoredExpr :: a -> CursoredM a ()
setCursoredExpr x = modifyCursoredExpr (const x)

getCursoredExpr :: CursoredM a a
getCursoredExpr = do
  Cursored x _ _ _ <- get
  return x

getPath :: CursoredM a CrumbList
getPath = do
  Cursored _ path _ _ <- get
  return path

delimitExprState :: CursoredM a r -> a -> CursoredM a r
delimitExprState m localExpr = do
  oldExpr <- getCursoredExpr

  setCursoredExpr localExpr
  r <- m

  setCursoredExpr oldExpr
  return r

-- NOTE: Do not export
modifyCursoredExpr :: (a -> a) -> CursoredM a ()
modifyCursoredExpr f = do
  Cursored x path validCursors i <- get
  put (Cursored (f x) path validCursors i)

simpleRewriteAt :: forall a. Data a => (a -> a) -> Cursor -> CursoredM a (Maybe ())
simpleRewriteAt tr = rewriteAt (mkCursoredAction tr)

-- simpleRewriteAtCursors :: forall a. (Monoid r, Data a) => (a -> CursoredM a r) -> Set Cursor -> CursoredM a (Set Cursor, r)
-- simpleRewriteAtCursors tr cursors = undefined

rewriteAt :: forall a r. (Data a) => CursoredM a r -> Cursor -> CursoredM a (Maybe r)
rewriteAt tr cursor = do
  crumbList_maybe <- lookupCursor cursor

  case crumbList_maybe of
    Nothing -> return Nothing

    Just crumbList -> do
      traceM ("crumbList = " ++ show (getCrumbs crumbList))
      go (getCrumbs crumbList)
  where
    go :: [Crumb] -> CursoredM a (Maybe r)
    go (cr:crs) = do
      x <- getCursoredExpr
      case safeIndex cr (Data.holes x) of
        Nothing -> return Nothing
        Just (x', rebuild) ->
          crumbDescend cr $ do
            setCursoredExpr x'
            r <- go crs
            modifyCursoredExpr rebuild
            return r
    go [] = fmap Just tr

-- | Rewrite one time, going top-down
rewriteOneTD :: forall a. Data a => (a -> Maybe a) -> CursoredM a (Maybe Cursor)
rewriteOneTD tr = go
  where
    go :: CursoredM a (Maybe Cursor)
    go = do
      x <- getCursoredExpr

      case tr x of
        Just x' -> do
          -- path <- getPath
          setCursoredExpr x'
          fmap Just (newCursor mempty)

        Nothing -> do
          path <- getPath
          let p0 = flip map (zip (map Crumb [0..]) (Data.holes x))
                  (\(cr, (x', rebuild)) -> do
                    setCursoredExpr x'
                    r <- crumbDescend cr go
                    modifyCursoredExpr rebuild
                    return r)
          foldr (\branchM acc -> do
            branch <- branchM
            case branch of
              Just r -> return (Just r)
              otherwise -> acc) (return Nothing) p0

-- cursorDescend :: Data a => (a -> Maybe a) -> CursoredM a [Cursor]
-- cursorDescend tr = cursorDescend' tr topCursor

-- cursorDescend' :: Data a => (a -> Maybe a) -> Cursor -> CursoredM a [Cursor]
-- cursorDescend' tr cursorSoFar = cursorDescendM go
--   where
--     go crumb = do
--       Cursored x _validCursors <- get
--       let x'_maybe = tr x

--       setCursoredExpr (fromMaybe x x'_maybe)

--       return [addCrumb cursorSoFar crumb]

-- -- | Apply (non-recursively) to all immediate children
-- cursorDescendM :: (Data a, Monoid r) => (Crumb -> CursoredM a r) -> CursoredM a r
-- cursorDescendM tr = do
--   Cursored e validCursors <- get

--   let (current, generate) = Data.uniplate e

--       currentWithCrumbs = zipTF current (map Crumb [0..])

--       (current', (res, validCursors')) = runWriter $ flip strMapM currentWithCrumbs $ \ (subE, crumb) -> do

--         let CursoredM act = tr crumb

--             (r, Cursored subE' newValidCursors) = runState act (Cursored subE validCursors)

--         tell (r, newValidCursors)
--         return subE'


--   put (Cursored (generate current')
--                 (unionCursors validCursors validCursors'))


--   return res





{-
cursorUpLevel :: Cursor -> CursoredM a Cursor
cursorUpLevel = cursorUpLevelN 1

-- TODO: Does this make sense?
cursorUpLevelN :: Int -> Cursor -> CursoredM a Cursor
cursorUpLevelN n c@(Cursor xs) = do
  Cursored e _ validCursors _ <- get
  if c `S.member` validCursors
    then do
      let c' = Cursor (drop n xs)
      put (Cursored e _ (S.insert c' validCursors))
      return c'
    else
      -- We were given an invalid cursor, so we just give back an invalid
      -- cursor
      return c
-}

{-
-- NOTE: Do not export
cursorPopWhen :: Crumb -> Cursor -> (Bool, Cursor)
cursorPopWhen cr0 (Cursor (cr:crs))
  | cr == cr0 = (True, Cursor crs)
cursorPopWhen _ (Cursor c) = (False, Cursor c)


-- cursorPopWhen :: Crumb -> Cursor -> (Bool, Cursor)
-- cursorPopWhen _ (Cursor []) = (False, Cursor [])

-- cursorPopWhen cr0 crs@(Cursor [cr])
--   | cr == cr0 = (True, Cursor [])
--   | otherwise = (False, crs)

-- cursorPopWhen cr0 (Cursor (cr:crs)) =
--   let (crRes, crLst) = cursorPopWhen cr0 (Cursor crs)
--   in
--   (crRes, crLst)

-- NOTE: Do not export
cursorPush :: Crumb -> Cursor -> Cursor
cursorPush cr (Cursor c) = Cursor $ cr : c

cursorPop :: Cursor -> Cursor
cursorPop (Cursor c) = Cursor (drop 1 c)

cursorStartsWith :: Cursor -> Crumb -> Bool
cursorStartsWith c cr = fst $ cursorPopWhen cr c

scopeCursorSet :: Crumb -> CursoredM a (Set Cursor)
scopeCursorSet cr = do
  Cursored e cs <- get

  let (inScope, outScope) = S.partition (`cursorStartsWith` cr) cs

  put (Cursored e (S.map cursorPop inScope))
  return outScope

unscopeCursorSet :: Crumb -> Set Cursor -> CursoredM a ()
unscopeCursorSet cr outScope = do
  Cursored e cs <- get
  let cs' = S.map (cursorPush cr) cs
  put (Cursored e (unionCursors cs' outScope))

delimitCursorSetScope :: Crumb -> CursoredM a r -> CursoredM a r
delimitCursorSetScope cr act = do
  outScopeCursors <- scopeCursorSet cr
  r <- act
  unscopeCursorSet cr outScopeCursors
  return r

-- | Save and restore state
delimitState :: MonadState s m => m r -> m (s, r)
delimitState m = do
  oldState <- get

  r <- m
  modifiedState <- get

  put oldState
  return (modifiedState, r)

delimitExprState :: CursoredM a r -> a -> CursoredM a r
delimitExprState m localExpr = do
  oldState@(Cursored oldExpr validCursors) <- get

  put (Cursored localExpr validCursors)
  r <- m

  put oldState
  return r

safeIndex :: Crumb -> [a] -> Maybe a
safeIndex (Crumb 0) (x:_) = Just x
safeIndex (Crumb i) (_:xs) = safeIndex (Crumb (i-1)) xs
safeIndex _ _ = Nothing

mkCursoredAction :: (a -> a) -> CursoredM a ()
mkCursoredAction = modifyCursoredExpr

simpleRewriteAt_ :: forall a. Data a => (a -> a) -> Cursor -> CursoredM a (Maybe ())
simpleRewriteAt_ tr = simpleRewriteAt (mkCursoredAction tr)

-- simpleRewriteAtCursors :: forall a. (Monoid r, Data a) => (a -> CursoredM a r) -> Set Cursor -> CursoredM a (Set Cursor, r)
-- simpleRewriteAtCursors tr cursors = undefined

simpleRewriteAt :: forall a r. (Data a) => CursoredM a r -> Cursor -> CursoredM a (Maybe r)
simpleRewriteAt tr cursor = do
  Cursored x0 validCursors <- get
  if cursor `S.member` validCursors
    then do
      let validCursors' = S.insert cursor $ S.filter (cursor `doesNotClobber`) validCursors

      goRes <- go (cursorCrumbs cursor) x0

      case goRes of
        Nothing -> return Nothing
        Just r -> do
          -- put (Cursored r validCursors')
          return (Just r)
          -- return (Just ())

    else return Nothing

    where
      go :: [Crumb] -> a -> CursoredM a (Maybe r)
      go (cr:crs) x =
        case safeIndex cr (Data.holes x) of
          Just (x', rebuild) ->
            delimitCursorSetScope cr $ do
              r <- go crs x'

              modifyCursoredExpr rebuild

              return r

          Nothing -> return Nothing
      go []       x = do
        flip delimitExprState x $ do
          r <- tr
          return $ Just r



-- | Functor strength for pairs
strength2 :: (a, Maybe b) -> Maybe (a, b)
strength2 = sequenceA

strength3 :: (a, b, Maybe c) -> Maybe (a, b, c)
strength3 (x, y, Nothing) = Nothing
strength3 (x, y, Just z) = Just (x, y, z)

-- strength' :: [(a, (b, c, Maybe d))] -> [Maybe (a, (b, c, d))]
-- strength' = _ . sequenceA . map (id *** strength3)

-- | Rewrite one time, going top-down
rewriteOneTD :: forall a. Data a => (a -> Maybe a) -> CursoredM a (Maybe Cursor)
rewriteOneTD tr = do
    Cursored e validCursors <- get

    let (e', validCursors', cursor) = go topCursor e validCursors

    put (Cursored e' validCursors')
    return cursor

  where
    go :: Cursor -> a -> Set Cursor -> (a, Set Cursor, Maybe Cursor)
    go cursorSoFar t validCursors =
      case tr t of
        Just t' ->
          (t'
          ,S.insert cursorSoFar $ S.filter (cursorSoFar `doesNotClobber`) validCursors
          ,Just cursorSoFar
          )

        Nothing ->

          let p0 = map (\(cr, (x, rebuild)) -> (rebuild, go (addCrumb cursorSoFar cr) x validCursors)) (zip (map Crumb [0..]) (Data.holes t))

              p = map (strength2 . fmap strength3) p0
          in
          case foldr (<|>) Nothing p of
            Just (rebuild, (x, validCursors', cursor)) ->
              (rebuild x
              ,S.insert cursor $ S.filter (cursor `doesNotClobber`) validCursors'
              ,Just cursor
              )

            Nothing ->
              (t, validCursors, Nothing)

rewriteBU :: forall a. Data a => (a -> Maybe a) -> CursoredM a (Set Cursor)
rewriteBU tr = do
    Cursored x validCursors <- get

    let (x', (validCursors', cursors)) = runState (Data.transformM go x) (validCursors, mempty)

    put $ Cursored x' validCursors'

    return cursors
  where
    go :: a -> State (Set Cursor, Set Cursor) a
    go e =
      case tr e of
        Nothing -> return e
        Just e' -> do
          (validCursors, cursors) <- get
          undefined

cursorDescend :: Data a => (a -> Maybe a) -> CursoredM a [Cursor]
cursorDescend tr = cursorDescend' tr topCursor

cursorDescend' :: Data a => (a -> Maybe a) -> Cursor -> CursoredM a [Cursor]
cursorDescend' tr cursorSoFar = cursorDescendM go
  where
    go crumb = do
      Cursored x _validCursors <- get
      let x'_maybe = tr x

      setCursoredExpr (fromMaybe x x'_maybe)

      return [addCrumb cursorSoFar crumb]

-- | Apply (non-recursively) to all immediate children
cursorDescendM :: (Data a, Monoid r) => (Crumb -> CursoredM a r) -> CursoredM a r
cursorDescendM tr = do
  Cursored e validCursors <- get

  let (current, generate) = Data.uniplate e

      currentWithCrumbs = zipTF current (map Crumb [0..])

      (current', (res, validCursors')) = runWriter $ flip strMapM currentWithCrumbs $ \ (subE, crumb) -> do

        let CursoredM act = tr crumb

            (r, Cursored subE' newValidCursors) = runState act (Cursored subE validCursors)

        tell (r, newValidCursors)
        return subE'


  put (Cursored (generate current')
                (unionCursors validCursors validCursors'))


  return res

-- NOTE: Do not export
setCursoredExpr :: a -> CursoredM a ()
setCursoredExpr x = modifyCursoredExpr (const x)

-- NOTE: Do not export
modifyCursoredExpr :: (a -> a) -> CursoredM a ()
modifyCursoredExpr f = do
  Cursored x validCursors <- get
  put (Cursored (f x) validCursors)


-}


-- -- | Apply (non-recursively) to all immediate children
-- cursorDescendM :: Monoid r => (Crumb -> CursoredM a r) -> CursoredM a r
-- cursorDescendM tr = do
--   c <- get
--   case c of
--     Cursored Tip _ -> return mempty
--     Cursored (Bin left x right) _validCursors -> do

--       (Cursored left' leftValidCursors, leftR) <- delimitState $ do
--         setCursoredExpr left
--         tr L

--       (Cursored right' rightValidCursors, rightR) <- delimitState $ do
--         setCursoredExpr right
--         tr R

--       let
--             -- TODO: Does this need to be checked for clobbering? Probably
--             -- not.
--           validCursors =
--             S.map (`addCrumb` L) leftValidCursors `S.union` S.map (`addCrumb` R) rightValidCursors

--       put (Cursored (Bin left' x right')
--                     validCursors)

--       return (leftR <> rightR)

-- cursorDescend :: (Tree a -> Maybe (Tree a)) -> CursoredM a [Cursor]
-- cursorDescend tr = cursorDescend' tr topCursor

-- cursorDescend' :: (Tree a -> Maybe (Tree a)) -> Cursor -> CursoredM a [Cursor]
-- cursorDescend' tr cursorSoFar = cursorDescendM go
--   where
--     go crumb = do
--       Cursored x _validCursors <- get
--       let x'_maybe = tr x

--       setCursoredExpr (fromMaybe x x'_maybe)

--       return [addCrumb cursorSoFar crumb]






{-
rewriteOneBU :: forall a. Data a => (a -> Maybe a) -> a -> CursoredM a (a, Maybe Cursor)
rewriteOneBU tr = go topCursor
  where
    go :: Cursor -> a -> CursoredM a (a, Maybe Cursor)
    go cursorSoFar t = do
      Cursored validCursors <- get

      case Data.holes t of
        [] ->
          case tr t of
            Just t' -> do
              put (Cursored t' (S.insert cursorSoFar $ S.filter (cursorSoFar `doesNotClobber`) validCursors))
              return $ Just cursorSoFar
-}



{-
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
-}

-- NOTE: Do not export
-- | Only include cursors from the right set which are not clobbered
-- by any cursor in the left set. Similar to 'appendCursors'.
unionCursors :: Set CrumbList -> Set CrumbList -> Set CrumbList
unionCursors as bs = S.filter notClobberedByBs as `S.union` S.filter notClobberedByAs bs
  where
    notClobberedByAs c = all (`doesNotClobber` c) as
    notClobberedByBs c = all (`doesNotClobber` c) bs

-- | Only include cursors from the right set which are not clobbered
-- by any cursor in the left set.
appendCursors :: [CrumbList] -> [CrumbList] -> [CrumbList]
appendCursors as bs = as ++ filter notClobberedByAs bs
  where
    notClobberedByAs c = all (`doesNotClobber` c) as

doesNotClobber :: CrumbList -> CrumbList -> Bool
x `doesNotClobber` y = not (x `clobbers` y)

-- | I think this forms a partial order on 'Cursor's. In fact, it also has
-- a minimal element: 'topCursor' clobbers everything.
clobbers :: CrumbList -> CrumbList -> Bool
x `clobbers` y = getCrumbs x `isPrefixOf` getCrumbs y

-- | This function is from:
-- https://wiki.haskell.org/Foldable_and_Traversable#Generalising_zipWith
zipWithTF :: forall t f a b c. -- HasCallStack =>
  (Traversable t, Foldable f) => (a -> b -> c) -> t a -> f b -> t c
zipWithTF g t f = snd (mapAccumL map_one (toList f) t)
  where
    map_one :: -- HasCallStack =>
      [b] -> a -> ([b], c)
    map_one (x:xs) y = (xs, g y x)
    map_one _ _ = error "map_one"
    {-# INLINE map_one #-}
{-# INLINE zipWithTF #-}

zipTF :: -- HasCallStack =>
  (Traversable t, Foldable f) => t a -> f b -> t (a, b)
zipTF = zipWithTF (,)
{-# INLINE zipTF #-}

