{-# LANGUAGE ScopedTypeVariables #-}
import Data.List

parseLine :: String -> [[[Int]]]
parseLine s = concat $ take 1 $
  do (n :: Int, s) <- reads s
     s <- return (drop 1 $ dropWhile (/= ':') s)
     (x :: Int, s) <- reads s
     xs <- parsePrefs x s
     return (replicate n xs)
  where parsePrefs :: Int -> String -> [[[Int]]]
        parsePrefs x s =
          let s' = dropWhile (\x -> x /= '>' && x /= '~') s
              ins x (y:ys) = (x:y):ys
          in  case s' of
                [] -> return [[x]]
                (c:s) -> 
                  do (y :: Int, s) <- reads s
                     if c == '~' then fmap (ins x) (parsePrefs y s) else fmap ([x] :) (parsePrefs y s)

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = case splitAt n xs of (ys, zs) -> ys : chunksOf n zs

parseLines :: String -> [[[Int]]]
parseLines = concatMap parseLine . lines

printLine :: [[Int]] -> String
printLine = intercalate ", " . map (f . map (["a","b","c","d"]!!))
  where f [x] = x
        f xs  = "[" ++ intercalate ", " xs ++ "]"

printLines :: [[[Int]]] -> String
printLines = unlines . map printLine

pad :: [Int] -> [String] -> String
pad _ [] = ""
pad _ [x] = x
pad (n:ns) (x:xs) = x ++ replicate (padding (length x)) ' ' ++ pad ns xs
  where padding m = n - m `mod` n

foo = 
  unlines . map (pad (10 : 2 : repeat 22)) . zipWith (\i -> (f i ++)) [1..] . 
  map (zipWith (\i -> (g i ++)) [1..]) . map (map printLine) . chunksOf 4 . parseLines
  where f 1 = ["where R1", "="]
        f i = ["  and R" ++ show i, "="]
        g i = "A" ++ show i ++ ": "


