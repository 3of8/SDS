{-# LANGUAGE OverloadedStrings #-}
import Data.Function
import Data.List
import qualified Data.Text as T

import StratWits

xs = map nub . groupBy ((==) `on` (\(x,y,_) -> (x,y))) . sort $ (
     [(29, 39, Just 1),
      (39, 29, Just 1),
      (10, 36, Just 1),
      (36, 10, Just 1),
      (36, 39, Just 1),
      (39, 36, Just 1),
      (12, 10, Just 1),
      (10, 12, Just 1),
      (12, 44, Just 1),
      (44, 12, Just 1),
      (9, 35, Just 1),
      (35, 9, Just 1),
      (18, 9, Just 1),
      (9, 18, Just 1),
      (5, 10, Just 1),
      (5, 17, Just 1),
      (17, 7, Just 1),
      (7, 43, Just 1),
      (5, 7, Just 1),
      (5, 10, Just 1),
      (10, 15, Just 1),
      (15, 10, Just 1),
      (15, 5, Just 1),
      (15, 7, Just 1),
      (15, 5, Just 1),
      (27, 13, Just 1),
      (13, 27, Just 1),
      (15, 13, Just 1),
      (13, 15, Just 1),
      (10, 19, Just 1),
      (19, 10, Just 1),
      (27, 19, Just 1),
      (19, 10, Just 1),
      (19, 27, Just 1),
      (19, 1, Just 1),
      (1, 19, Just 1),
      (33, 5, Just 1),
      (33, 22, Just 1),
      (22, 29, Just 1),
      (32, 28, Just 1),
      (28, 32, Just 1),
      (22, 32, Just 1),
      (32, 22, Just 1),
      (28, 39, Just 1),
      (1, 2, Just 1),
      (2, 1, Just 1),
      (39, 2, Just 1),
      (17, 5, Just 1),
      (5, 17, Just 1),
      (6, 42, Just 1),
      (6, 19, Just 1),
      (17, 11, Just 1),
      (42, 11, Just 1),
      (17, 3, Just 1),
      (42, 3, Just 1),
      (37, 42, Just 1),
      (37, 42, Just 2),
      (42, 24, Just 1),
      (24, 34, Just 1),
      (34, 24, Just 1),
      (34, 24, Just 1),
      (24, 34, Just 1),
      (14, 34, Just 1),
      (46, 37, Just 1),
      (46, 20, Just 1),
      (20, 21, Just 1),
      (12, 16, Just 1),
      (44, 40, Just 1),
      (9, 40, Just 1),
      (14, 16, Just 1),
      (14, 9, Just 1),
      (14, 16, Just 1),
      (44, 40, Just 1),
      (9, 40, Just 1),
      (14, 9, Just 1),
      (14, 9, Just 1),
      (23, 19, Just 1),
      (35, 21, Just 1),
      (21, 35, Just 1),
      (23, 12, Just 1),
      (23, 18, Just 1),
      (30, 21, Just 1),
      (47, 30, Just 1),
      (4, 47, Just 1),
      (4, 18, Just 1),
      (8, 26, Just 2),
      (26, 8, Just 2),
      (8, 26, Just 2),
      (4, 47, Just 1),
      (47, 30, Just 1),
      (30, 21, Just 1),
      (25, 36, Just 1),
      (36, 25, Just 1),
      (25, 36, Just 1),
      (25, 26, Just 1),
      (4, 8, Just 1),
      (30, 41, Just 1),
      (41, 31, Just 1),
      (2, 38, Just 1),
      (31, 38, Just 1),
      (45, 31, Just 2)] :: [(Integer, Integer, Maybe Integer)])

lookupWits (a,b) = [(a, b, i, prefs, sigma) | (p, q, i, prefs, sigma) <- wits, ("R" ++ show a, "R" ++ show b) == (p,q)]

wits' = concatMap (\(a,b,_) -> lookupWits (a,b)) (concat xs)

main = mapM_ putStrLn ["R" ++ show i ++ "_R" ++ show j ++ ".strategyproofness(" ++ show k ++ ")" | (i,j,Just k) <- concat xs]


thms = ["p_{2,d} + p_{2,c} \\leq p_{1,d} + p_{1,c}",
         "p_{19,a} < p_{1,a} \\myvee p_{19,a} + p_{19,b} < p_{1,a} + p_{1,b} \\myvee ( p_{19,a} = p_{1,a} \\wedge p_{19,a} + p_{19,b} = p_{1,a} + p_{1,b} )",
         "p_{1,d} + p_{1,c} < p_{2,d} + p_{2,c} \\myvee p_{1,d} + p_{1,c} + p_{1,a} < p_{2,d} + p_{2,c} + p_{2,a} \\myvee ( p_{1,d} + p_{1,c} = p_{2,d} + p_{2,c} \\wedge p_{1,d} + p_{1,c} + p_{1,a} = p_{2,d} + p_{2,c} + p_{2,a} )",
         "p_{38,c} + p_{38,a} \\leq p_{2,c} + p_{2,a}",
         "p_{8,c} < p_{4,d} \\myvee p_{8,c} + p_{8,d} < p_{4,d} + p_{4,c} \\myvee ( p_{8,c} = p_{4,d} \\wedge p_{8,c} + p_{8,d} = p_{4,d} + p_{4,c} )",
         "p_{18,c} < p_{4,c} \\myvee p_{18,c} + p_{18,b} + p_{18,a} < p_{4,c} + p_{4,b} + p_{4,a} \\myvee ( p_{18,c} = p_{4,c} \\wedge p_{18,c} + p_{18,b} + p_{18,a} = p_{4,c} + p_{4,b} + p_{4,a} )",
         "p_{47,d} + p_{47,a} \\leq p_{4,d} + p_{4,a}",
         "p_{7,c} + p_{7,a} < p_{5,c} + p_{5,a} \\myvee p_{7,c} + p_{7,a} + p_{7,d} < p_{5,c} + p_{5,a} + p_{5,d} \\myvee ( p_{7,c} + p_{7,a} = p_{5,c} + p_{5,a} \\wedge p_{7,c} + p_{7,a} + p_{7,d} = p_{5,c} + p_{5,a} + p_{5,d} )",
         "p_{10,a} < p_{5,d} \\myvee p_{10,a} + p_{10,c} + p_{10,d} < p_{5,d} + p_{5,b} + p_{5,a} \\myvee ( p_{10,a} = p_{5,d} \\wedge p_{10,a} + p_{10,c} + p_{10,d} = p_{5,d} + p_{5,b} + p_{5,a} )",
         "p_{17,c} + p_{17,a} < p_{5,c} + p_{5,a} \\myvee p_{17,c} + p_{17,a} + p_{17,d} < p_{5,c} + p_{5,a} + p_{5,d} \\myvee ( p_{17,c} + p_{17,a} = p_{5,c} + p_{5,a} \\wedge p_{17,c} + p_{17,a} + p_{17,d} = p_{5,c} + p_{5,a} + p_{5,d} )",
         "p_{19,d} < p_{6,d} \\myvee p_{19,d} + p_{19,b} < p_{6,d} + p_{6,b} \\myvee p_{19,d} + p_{19,b} + p_{19,a} < p_{6,d} + p_{6,b} + p_{6,a} \\myvee ( p_{19,d} = p_{6,d} \\wedge p_{19,d} + p_{19,b} = p_{6,d} + p_{6,b} \\wedge p_{19,d} + p_{19,b} + p_{19,a} = p_{6,d} + p_{6,b} + p_{6,a} )",
         "p_{42,c} + p_{42,a} \\leq p_{6,c} + p_{6,a}",
         "p_{43,d} < p_{7,a} \\myvee p_{43,d} + p_{43,b} < p_{7,a} + p_{7,c} \\myvee p_{43,d} + p_{43,b} + p_{43,a} < p_{7,a} + p_{7,c} + p_{7,d} \\myvee ( p_{43,d} = p_{7,a} \\wedge p_{43,d} + p_{43,b} = p_{7,a} + p_{7,c} \\wedge p_{43,d} + p_{43,b} + p_{43,a} = p_{7,a} + p_{7,c} + p_{7,d} )",
         "p_{26,a} < p_{8,d} \\myvee p_{26,a} + p_{26,b} + p_{26,d} < p_{8,d} + p_{8,b} + p_{8,a} \\myvee ( p_{26,a} = p_{8,d} \\wedge p_{26,a} + p_{26,b} + p_{26,d} = p_{8,d} + p_{8,b} + p_{8,a} )",
         "p_{18,d} + p_{18,a} < p_{9,d} + p_{9,a} \\myvee p_{18,d} + p_{18,a} + p_{18,c} < p_{9,d} + p_{9,a} + p_{9,c} \\myvee ( p_{18,d} + p_{18,a} = p_{9,d} + p_{9,a} \\wedge p_{18,d} + p_{18,a} + p_{18,c} = p_{9,d} + p_{9,a} + p_{9,c} )",
         "p_{35,b} + p_{35,a} \\leq p_{9,b} + p_{9,a}",
         "p_{40,b} + p_{40,a} \\leq p_{9,b} + p_{9,a}",
         "p_{12,b} + p_{12,d} < p_{10,c} + p_{10,a} \\myvee p_{12,b} + p_{12,d} + p_{12,a} < p_{10,c} + p_{10,a} + p_{10,d} \\myvee ( p_{12,b} + p_{12,d} = p_{10,c} + p_{10,a} \\wedge p_{12,b} + p_{12,d} + p_{12,a} = p_{10,c} + p_{10,a} + p_{10,d} )",
         "p_{15,a} + p_{15,c} < p_{10,d} + p_{10,b} \\myvee p_{15,a} + p_{15,c} + p_{15,d} < p_{10,d} + p_{10,b} + p_{10,a} \\myvee ( p_{15,a} + p_{15,c} = p_{10,d} + p_{10,b} \\wedge p_{15,a} + p_{15,c} + p_{15,d} = p_{10,d} + p_{10,b} + p_{10,a} )",
         "p_{19,a} + p_{19,c} < p_{10,d} + p_{10,b} \\myvee p_{19,a} + p_{19,c} + p_{19,d} < p_{10,d} + p_{10,b} + p_{10,a} \\myvee ( p_{19,a} + p_{19,c} = p_{10,d} + p_{10,b} \\wedge p_{19,a} + p_{19,c} + p_{19,d} = p_{10,d} + p_{10,b} + p_{10,a} )",
         "p_{36,a} + p_{36,b} \\leq p_{10,d} + p_{10,c}",
         "p_{10,a} + p_{10,c} + p_{10,d} \\leq p_{12,d} + p_{12,b} + p_{12,a}",
         "p_{16,c} + p_{16,a} < p_{12,c} + p_{12,a} \\myvee p_{16,c} + p_{16,a} + p_{16,d} < p_{12,c} + p_{12,a} + p_{12,d} \\myvee ( p_{16,c} + p_{16,a} = p_{12,c} + p_{12,a} \\wedge p_{16,c} + p_{16,a} + p_{16,d} = p_{12,c} + p_{12,a} + p_{12,d} )",
         "p_{44,b} + p_{44,a} \\leq p_{12,b} + p_{12,a}",
         "p_{15,d} + p_{15,c} < p_{13,d} + p_{13,b} \\myvee p_{15,d} + p_{15,c} + p_{15,a} < p_{13,d} + p_{13,b} + p_{13,a} \\myvee ( p_{15,d} + p_{15,c} = p_{13,d} + p_{13,b} \\wedge p_{15,d} + p_{15,c} + p_{15,a} = p_{13,d} + p_{13,b} + p_{13,a} )",
         "p_{27,a} < p_{13,a} \\myvee p_{27,a} + p_{27,c} < p_{13,a} + p_{13,b} \\myvee p_{27,a} + p_{27,c} + p_{27,d} < p_{13,a} + p_{13,b} + p_{13,d} \\myvee ( p_{27,a} = p_{13,a} \\wedge p_{27,a} + p_{27,c} = p_{13,a} + p_{13,b} \\wedge p_{27,a} + p_{27,c} + p_{27,d} = p_{13,a} + p_{13,b} + p_{13,d} )",
         "p_{9,a} < p_{14,a} \\myvee p_{9,a} + p_{9,d} < p_{14,a} + p_{14,d} \\myvee p_{9,a} + p_{9,d} + p_{9,c} < p_{14,a} + p_{14,d} + p_{14,c} \\myvee ( p_{9,a} = p_{14,a} \\wedge p_{9,a} + p_{9,d} = p_{14,a} + p_{14,d} \\wedge p_{9,a} + p_{9,d} + p_{9,c} = p_{14,a} + p_{14,d} + p_{14,c} )",
         "p_{16,c} < p_{14,d} \\myvee p_{16,c} + p_{16,d} < p_{14,d} + p_{14,c} \\myvee ( p_{16,c} = p_{14,d} \\wedge p_{16,c} + p_{16,d} = p_{14,d} + p_{14,c} )",
         "p_{34,d} + p_{34,b} + p_{34,a} \\leq p_{14,c} + p_{14,b} + p_{14,a}",
         "p_{5,d} < p_{15,a} \\myvee p_{5,d} + p_{5,b} < p_{15,a} + p_{15,c} \\myvee p_{5,d} + p_{5,b} + p_{5,a} < p_{15,a} + p_{15,c} + p_{15,d} \\myvee ( p_{5,d} = p_{15,a} \\wedge p_{5,d} + p_{5,b} = p_{15,a} + p_{15,c} \\wedge p_{5,d} + p_{5,b} + p_{5,a} = p_{15,a} + p_{15,c} + p_{15,d} )",
         "p_{7,d} + p_{7,b} < p_{15,d} + p_{15,b} \\myvee p_{7,d} + p_{7,b} + p_{7,a} < p_{15,d} + p_{15,b} + p_{15,a} \\myvee ( p_{7,d} + p_{7,b} = p_{15,d} + p_{15,b} \\wedge p_{7,d} + p_{7,b} + p_{7,a} = p_{15,d} + p_{15,b} + p_{15,a} )",
         "p_{10,d} < p_{15,a} \\myvee p_{10,d} + p_{10,b} < p_{15,a} + p_{15,c} \\myvee p_{10,d} + p_{10,b} + p_{10,a} < p_{15,a} + p_{15,c} + p_{15,d} \\myvee ( p_{10,d} = p_{15,a} \\wedge p_{10,d} + p_{10,b} = p_{15,a} + p_{15,c} \\wedge p_{10,d} + p_{10,b} + p_{10,a} = p_{15,a} + p_{15,c} + p_{15,d} )",
         "p_{13,d} + p_{13,b} \\leq p_{15,d} + p_{15,c}",
         "p_{3,c} + p_{3,a} \\leq p_{17,c} + p_{17,a}",
         "p_{5,c} + p_{5,a} \\leq p_{17,c} + p_{17,a}",
         "p_{7,c} + p_{7,a} \\leq p_{17,c} + p_{17,a}",
         "p_{11,c} + p_{11,a} \\leq p_{17,c} + p_{17,a}",
         "p_{9,d} + p_{9,a} \\leq p_{18,d} + p_{18,a}",
         "p_{1,b} + p_{1,a} \\leq p_{19,b} + p_{19,a}",
         "p_{10,b} + p_{10,d} \\leq p_{19,c} + p_{19,a}",
         "p_{27,d} + p_{27,b} \\leq p_{19,d} + p_{19,c}",
         "p_{21,c} < p_{20,a} \\myvee p_{21,c} + p_{21,b} < p_{20,a} + p_{20,c} \\myvee ( p_{21,c} = p_{20,a} \\wedge p_{21,c} + p_{21,b} = p_{20,a} + p_{20,c} )",
         "p_{35,c} < p_{21,c} \\myvee p_{35,c} + p_{35,b} + p_{35,a} < p_{21,c} + p_{21,b} + p_{21,a} \\myvee ( p_{35,c} = p_{21,c} \\wedge p_{35,c} + p_{35,b} + p_{35,a} = p_{21,c} + p_{21,b} + p_{21,a} )",
         "p_{29,a} < p_{22,d} \\myvee p_{29,a} + p_{29,c} + p_{29,d} < p_{22,d} + p_{22,b} + p_{22,a} \\myvee ( p_{29,a} = p_{22,d} \\wedge p_{29,a} + p_{29,c} + p_{29,d} = p_{22,d} + p_{22,b} + p_{22,a} )",
         "p_{32,a} < p_{22,a} \\myvee p_{32,a} + p_{32,b} < p_{22,a} + p_{22,b} \\myvee ( p_{32,a} = p_{22,a} \\wedge p_{32,a} + p_{32,b} = p_{22,a} + p_{22,b} )",
         "p_{12,c} + p_{12,a} \\leq p_{23,c} + p_{23,a}",
         "p_{18,c} + p_{18,d} \\leq p_{23,d} + p_{23,c}",
         "p_{19,d} + p_{19,b} + p_{19,a} \\leq p_{23,d} + p_{23,b} + p_{23,a}",
         "p_{34,b} < p_{24,c} \\myvee p_{34,b} + p_{34,d} < p_{24,c} + p_{24,a} \\myvee ( p_{34,b} = p_{24,c} \\wedge p_{34,b} + p_{34,d} = p_{24,c} + p_{24,a} )",
         "p_{26,d} + p_{26,c} < p_{25,d} + p_{25,b} \\myvee p_{26,d} + p_{26,c} + p_{26,a} < p_{25,d} + p_{25,b} + p_{25,a} \\myvee ( p_{26,d} + p_{26,c} = p_{25,d} + p_{25,b} \\wedge p_{26,d} + p_{26,c} + p_{26,a} = p_{25,d} + p_{25,b} + p_{25,a} )",
         "p_{36,a} < p_{25,a} \\myvee p_{36,a} + p_{36,c} < p_{25,a} + p_{25,c} \\myvee ( p_{36,a} = p_{25,a} \\wedge p_{36,a} + p_{36,c} = p_{25,a} + p_{25,c} )",
         "p_{8,d} < p_{26,a} \\myvee p_{8,d} + p_{8,b} < p_{26,a} + p_{26,b} \\myvee ( p_{8,d} = p_{26,a} \\wedge p_{8,d} + p_{8,b} = p_{26,a} + p_{26,b} )",
         "p_{13,b} + p_{13,a} \\leq p_{27,c} + p_{27,a}",
         "p_{19,d} + p_{19,c} < p_{27,d} + p_{27,b} \\myvee p_{19,d} + p_{19,c} + p_{19,a} < p_{27,d} + p_{27,b} + p_{27,a} \\myvee ( p_{19,d} + p_{19,c} = p_{27,d} + p_{27,b} \\wedge p_{19,d} + p_{19,c} + p_{19,a} = p_{27,d} + p_{27,b} + p_{27,a} )",
         "p_{32,d} < p_{28,a} \\myvee p_{32,d} + p_{32,b} < p_{28,a} + p_{28,c} \\myvee ( p_{32,d} = p_{28,a} \\wedge p_{32,d} + p_{32,b} = p_{28,a} + p_{28,c} )",
         "p_{39,a} < p_{28,a} \\myvee p_{39,a} + p_{39,c} < p_{28,a} + p_{28,b} \\myvee ( p_{39,a} = p_{28,a} \\wedge p_{39,a} + p_{39,c} = p_{28,a} + p_{28,b} )",
         "p_{39,d} < p_{29,a} \\myvee p_{39,d} + p_{39,c} < p_{29,a} + p_{29,b} \\myvee ( p_{39,d} = p_{29,a} \\wedge p_{39,d} + p_{39,c} = p_{29,a} + p_{29,b} )",
         "p_{21,b} + p_{21,a} < p_{30,b} + p_{30,a} \\myvee p_{21,b} + p_{21,a} + p_{21,d} < p_{30,b} + p_{30,a} + p_{30,d} \\myvee ( p_{21,b} + p_{21,a} = p_{30,b} + p_{30,a} \\wedge p_{21,b} + p_{21,a} + p_{21,d} = p_{30,b} + p_{30,a} + p_{30,d} )",
         "p_{41,c} < p_{30,c} \\myvee p_{41,c} + p_{41,b} + p_{41,a} < p_{30,c} + p_{30,b} + p_{30,a} \\myvee ( p_{41,c} = p_{30,c} \\wedge p_{41,c} + p_{41,b} + p_{41,a} = p_{30,c} + p_{30,b} + p_{30,a} )",
         "p_{38,b} + p_{38,d} < p_{31,d} + p_{31,b} \\myvee p_{38,b} + p_{38,d} + p_{38,c} < p_{31,d} + p_{31,b} + p_{31,a} \\myvee ( p_{38,b} + p_{38,d} = p_{31,d} + p_{31,b} \\wedge p_{38,b} + p_{38,d} + p_{38,c} = p_{31,d} + p_{31,b} + p_{31,a} )",
         "p_{22,b} + p_{22,a} < p_{32,b} + p_{32,a} \\myvee p_{22,b} + p_{22,a} + p_{22,d} < p_{32,b} + p_{32,a} + p_{32,d} \\myvee ( p_{22,b} + p_{22,a} = p_{32,b} + p_{32,a} \\wedge p_{22,b} + p_{22,a} + p_{22,d} = p_{32,b} + p_{32,a} + p_{32,d} )",
         "p_{28,a} < p_{32,d} \\myvee p_{28,a} + p_{28,c} + p_{28,d} < p_{32,d} + p_{32,b} + p_{32,a} \\myvee ( p_{28,a} = p_{32,d} \\wedge p_{28,a} + p_{28,c} + p_{28,d} = p_{32,d} + p_{32,b} + p_{32,a} )",
         "p_{5,a} < p_{33,a} \\myvee p_{5,a} + p_{5,b} < p_{33,a} + p_{33,b} \\myvee ( p_{5,a} = p_{33,a} \\wedge p_{5,a} + p_{5,b} = p_{33,a} + p_{33,b} )",
         "p_{22,d} + p_{22,c} \\leq p_{33,d} + p_{33,c}",
         "p_{24,c} < p_{34,b} \\myvee p_{24,c} + p_{24,a} + p_{24,d} < p_{34,b} + p_{34,d} + p_{34,a} \\myvee ( p_{24,c} = p_{34,b} \\wedge p_{24,c} + p_{24,a} + p_{24,d} = p_{34,b} + p_{34,d} + p_{34,a} )",
         "p_{9,a} < p_{35,a} \\myvee p_{9,a} + p_{9,b} < p_{35,a} + p_{35,b} \\myvee ( p_{9,a} = p_{35,a} \\wedge p_{9,a} + p_{9,b} = p_{35,a} + p_{35,b} )",
         "p_{21,c} + p_{21,b} + p_{21,a} \\leq p_{35,c} + p_{35,b} + p_{35,a}",
         "p_{10,d} < p_{36,a} \\myvee p_{10,d} + p_{10,c} < p_{36,a} + p_{36,b} \\myvee ( p_{10,d} = p_{36,a} \\wedge p_{10,d} + p_{10,c} = p_{36,a} + p_{36,b} )",
         "p_{25,c} + p_{25,a} < p_{36,c} + p_{36,a} \\myvee p_{25,c} + p_{25,a} + p_{25,d} < p_{36,c} + p_{36,a} + p_{36,d} \\myvee ( p_{25,c} + p_{25,a} = p_{36,c} + p_{36,a} \\wedge p_{25,c} + p_{25,a} + p_{25,d} = p_{36,c} + p_{36,a} + p_{36,d} )",
         "p_{39,d} + p_{39,c} \\leq p_{36,d} + p_{36,c}",
         "p_{42,d} < p_{37,a} \\myvee p_{42,d} + p_{42,b} < p_{37,a} + p_{37,b} \\myvee ( p_{42,d} = p_{37,a} \\wedge p_{42,d} + p_{42,b} = p_{37,a} + p_{37,b} )",
         "p_{42,d} < p_{37,c} \\myvee p_{42,d} + p_{42,b} < p_{37,c} + p_{37,d} \\myvee ( p_{42,d} = p_{37,c} \\wedge p_{42,d} + p_{42,b} = p_{37,c} + p_{37,d} )",
         "p_{2,c} + p_{2,a} < p_{39,c} + p_{39,a} \\myvee p_{2,c} + p_{2,a} + p_{2,d} < p_{39,c} + p_{39,a} + p_{39,d} \\myvee ( p_{2,c} + p_{2,a} = p_{39,c} + p_{39,a} \\wedge p_{2,c} + p_{2,a} + p_{2,d} = p_{39,c} + p_{39,a} + p_{39,d} )",
         "p_{29,a} + p_{29,b} < p_{39,d} + p_{39,c} \\myvee p_{29,a} + p_{29,b} + p_{29,d} < p_{39,d} + p_{39,c} + p_{39,a} \\myvee ( p_{29,a} + p_{29,b} = p_{39,d} + p_{39,c} \\wedge p_{29,a} + p_{29,b} + p_{29,d} = p_{39,d} + p_{39,c} + p_{39,a} )",
         "p_{36,d} + p_{36,c} < p_{39,d} + p_{39,c} \\myvee p_{36,d} + p_{36,c} + p_{36,a} < p_{39,d} + p_{39,c} + p_{39,a} \\myvee ( p_{36,d} + p_{36,c} = p_{39,d} + p_{39,c} \\wedge p_{36,d} + p_{36,c} + p_{36,a} = p_{39,d} + p_{39,c} + p_{39,a} )",
         "p_{31,d} + p_{31,b} + p_{31,a} \\leq p_{41,c} + p_{41,b} + p_{41,a}",
         "p_{3,d} < p_{42,d} \\myvee p_{3,d} + p_{3,b} < p_{42,d} + p_{42,b} \\myvee p_{3,d} + p_{3,b} + p_{3,a} < p_{42,d} + p_{42,b} + p_{42,a} \\myvee ( p_{3,d} = p_{42,d} \\wedge p_{3,d} + p_{3,b} = p_{42,d} + p_{42,b} \\wedge p_{3,d} + p_{3,b} + p_{3,a} = p_{42,d} + p_{42,b} + p_{42,a} )",
         "p_{11,d} < p_{42,c} \\myvee p_{11,d} + p_{11,b} < p_{42,c} + p_{42,a} \\myvee ( p_{11,d} = p_{42,c} \\wedge p_{11,d} + p_{11,b} = p_{42,c} + p_{42,a} )",
         "p_{24,b} + p_{24,a} \\leq p_{42,b} + p_{42,a}",
         "p_{12,b} + p_{12,a} < p_{44,b} + p_{44,a} \\myvee p_{12,b} + p_{12,a} + p_{12,d} < p_{44,b} + p_{44,a} + p_{44,d} \\myvee ( p_{12,b} + p_{12,a} = p_{44,b} + p_{44,a} \\wedge p_{12,b} + p_{12,a} + p_{12,d} = p_{44,b} + p_{44,a} + p_{44,d} )",
         "p_{40,c} + p_{40,d} \\leq p_{44,d} + p_{44,c}",
         "p_{31,c} + p_{31,d} < p_{45,b} + p_{45,a} \\myvee p_{31,c} + p_{31,d} + p_{31,b} < p_{45,b} + p_{45,a} + p_{45,c} \\myvee ( p_{31,c} + p_{31,d} = p_{45,b} + p_{45,a} \\wedge p_{31,c} + p_{31,d} + p_{31,b} = p_{45,b} + p_{45,a} + p_{45,c} )",
         "p_{20,c} + p_{20,a} \\leq p_{46,c} + p_{46,a}",
         "p_{37,a} + p_{37,c} < p_{46,d} + p_{46,b} \\myvee p_{37,a} + p_{37,c} + p_{37,d} < p_{46,d} + p_{46,b} + p_{46,a} \\myvee ( p_{37,a} + p_{37,c} = p_{46,d} + p_{46,b} \\wedge p_{37,a} + p_{37,c} + p_{37,d} = p_{46,d} + p_{46,b} + p_{46,a} )",
         "p_{30,b} + p_{30,a} \\leq p_{47,b} + p_{47,a}"] 

main' = mapM_ putStrLn 
  ["\\begin{multlined}[.9\\displaywidth] " ++ thm ++ " \\end{multlined}" ++ " \\tag{$S_{" ++ show i ++ "," ++ show j ++ "}$}\\\\"  | ((i,j,_), thm) <- zip (concat xs) thms]


