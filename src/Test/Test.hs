{-# LANGUAGE DeriveDataTypeable #-}

module Test.Test where

import           Rewrite.Cursor

import           Data.Data

import qualified Data.Generics.Uniplate.DataOnly as Data

import Debug.Trace

data Tree a = Tip | Bin (Tree a) a (Tree a) deriving (Show, Data)

buildTree :: [a] -> Tree a
buildTree xs0 = go (length xs0) xs0
  where
    go _ [] = Tip
    go len (x:xs) =
      let halfTailLen = (len-1) `quot` 2
          (left, right) = splitAt halfTailLen xs
      in
      Bin (go (length left) left) x (go (length right) right)

showTree :: Show a => Tree a -> String
showTree = unlines . go
  where
    go Tip = ["Tip"]
    go (Bin left x right) =
      show x : transformRecResult (go left)
            ++ transformRecResult (go right)

    transformRecResult [] = []
    transformRecResult (x:xs) =
      ("  " ++ x) : map ("  | " ++) xs

printTree :: Show a => Tree a -> IO ()
printTree = putStrLn . showTree

testTree :: Tree Int
testTree = buildTree [0..25]

rewrite7 :: Tree Int -> Maybe (Tree Int)
rewrite7 (Bin left 7 right) = Just $ Bin left (-1) right
rewrite7 _ = Nothing

times100 :: Tree Int -> Tree Int
times100 (Bin left x right) = Bin left (x*100) right
times100 t = t

main :: IO ()
main = do
  let Just t = runCursoredM $ do
            (t', c_maybe) <- rewriteOneTD rewrite7 testTree

            let Just c = c_maybe

            traceM (show c)

            -- c' <- cursorUpLevel c
            -- traceM (show c')

            simpleRewriteAt_ (Data.transform times100) c t'

  printTree t


