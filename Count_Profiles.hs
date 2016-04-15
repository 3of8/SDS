{-# LANGUAGE PatternGuards #-}
import Control.Monad
import Data.Foldable
import Data.List
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.IntSet as IS
import Data.IntSet (IntSet)
import qualified Data.MultiSet as MS
import Data.MultiSet (MultiSet)
import qualified Data.Sequence as Seq
import Data.Sequence (Seq, (><))

type WeakRanking = [IntSet]

subsets :: IntSet -> [IntSet]
subsets = toList . subsetsAux
  where subsetsAux s
          | Just (x, s') <- IS.maxView s = 
              let ss = subsetsAux s'
              in  ss >< fmap (IS.insert x) ss 
          | otherwise = Seq.singleton IS.empty

splits :: IntSet -> [(IntSet, IntSet)]
splits s = 
  do s' <- subsets s
     return (s', IS.difference s s')

weakRankings :: IntSet -> [WeakRanking]
weakRankings s
  | IS.null s  = [[]]
  | otherwise = 
      do (s', s'') <- splits s
         guard (not (IS.null s'))
         fmap (s':) (weakRankings s'')

factorial :: Integer -> Integer
factorial n = product [2..n]

choose :: Integer -> Integer -> Integer
n `choose` k = if 2 * k > n then product [k+1..n] `div` factorial (n-k) else product [n-k+1..n] `div` factorial k

fubiniAux :: Integer -> [Integer]
fubiniAux n = fst (go n)
  where go 0 = ([1], [1] ++ genericReplicate (n-1) 0)
        go n = case go (n - 1) of 
                 (xs, ys) -> (sum (zipWith (*) xs ys) : xs, zipWith (+) (1:ys) ys)

fubini :: Integer -> Integer
fubini = head . fubiniAux

countProfiles :: Integer -> Integer -> Integer
countProfiles n k = (fubini n + k - 1) `choose` k

profiles :: IntSet -> Int -> Set (MultiSet WeakRanking)
profiles s n = go n
  where rs = weakRankings s
        go :: Int -> Set (MultiSet WeakRanking)
        go 0 = S.singleton MS.empty
        go n = let ps = go (n - 1) in S.unions [S.map (MS.insert r) ps | r <- rs]


