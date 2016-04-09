{-# LANGUAGE ScopedTypeVariables, PatternGuards #-}
import Control.Arrow
import Data.Char
import Data.List
import Data.Maybe

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

makeDefinitions = 
  unlines . map (pad (10 : 2 : repeat 22)) . zipWith (\i -> (f i ++)) [1..] . 
  map (zipWith (\i -> (g i ++)) [1..]) . map (map printLine) . chunksOf 4 . parseLines
  where f 1 = ["where R1", "="]
        f i = ["  and R" ++ show i, "="]
        g i = "A" ++ show i ++ ": "


manipText = "; This manipulation was obtained from "
canonicalText = "; The manipulated profile in canonical form is "

getPrefixed :: String -> [String] -> Maybe (String, [String])
getPrefixed prefix [] = Nothing
getPrefixed prefix (x:xs)
  | Just y <- stripPrefix prefix x = Just (y, xs)
  | otherwise = getPrefixed prefix xs
  
parseProfileNames :: [String] -> [String]
parseProfileNames = map (('p':) . takeWhile isDigit) . mapMaybe (stripPrefix "p")

manipulations xs =
  case foo xs of
    Nothing -> []
    Just (x, xs) -> x : manipulations xs
  where foo xs =
          do (p, xs) <- fmap (first init) $ getPrefixed manipText xs
             (p', xs) <- fmap (first init) $ getPrefixed canonicalText xs
             return ((p, p'), xs)

suppText = "; Inefficient support "

supports xs =
  case getPrefixed suppText xs of
    Just (y, xs) -> (init $ drop 13 $ dropWhile (/= ']') y) : supports xs
    Nothing -> []

the :: Maybe a -> a
the (Just x) = x
    
main' =
  do profileMap <- fmap (flip zip [(1::Int)..] . parseProfileNames . lines) (readFile "profiles_raw")
     let profile x = maybe (error ("No such profile: " ++ x)) id (lookup x profileMap)
     ms <- fmap (manipulations . lines) (readFile "mus_annotated.smt2")
     mapM_ putStrLn ["R" ++ show (profile p1) ++ "_R" ++ show (profile p2) ++ ".strategyproofness" | (p1, p2) <- ms]
     
main =
  do profileMap <- fmap (flip zip [(1::Int)..] . parseProfileNames . lines) (readFile "profiles_raw")
     let profile x = maybe (error ("No such profile: " ++ x)) id (lookup x profileMap)
     ss <- fmap (supports . lines) (readFile "mus_annotated.smt2")
     mapM_ putStrLn ["R" ++ show (profile p) ++ ".support" | p <- ss]
     


