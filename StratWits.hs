module StratWits where

wits = [("R40","R41","A2",[["a", "b"], ["d"],
                     ["c"]],[("a","a"), ("d","d"),
   ("c","c"), ("b","b")]),
  ("R40","R44","A4",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("d","c"),
     ("c","d"), ("b","b")]),
  ("R41","R40","A2",[["a", "b"], ["c"],
                      ["d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R44","R40","A1",[["d"], ["c"],
                      ["a",
                        "b"]],[("c","d"), ("d","c"),
     ("a","a"), ("b","b")]),
  ("R38","R39","A4",[["a", "c"], ["d"],
                      ["b"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R39","R38","A1",[["a", "c"], ["b"],
                      ["d"]],[("a","a"), ("c","c"),
    ("d","d"), ("b","b")]),
  ("R37","R42","A3",[["d"], ["b"], ["a"],
                      ["c"]],[("a","d"), ("c","c"),
    ("b","b"), ("d","a")]),
  ("R37","R42","A4",[["d"], ["b"], ["a"],
                      ["c"]],[("a","c"), ("c","d"),
    ("b","a"), ("d","b")]),
  ("R37","R46","A1",[["b", "d"], ["a"],
                      ["c"]],[("a","d"), ("c","b"),
    ("b","c"), ("d","a")]),
  ("R37","R46","A1",[["b", "d"], ["a"],
                      ["c"]],[("a","b"), ("c","d"),
    ("b","a"), ("d","c")]),
  ("R42","R37","A3",[["c"], ["d"],
                      ["a",
                        "b"]],[("c","a"), ("d","c"),
     ("a","b"), ("b","d")]),
  ("R42","R37","A3",[["a"], ["b"],
                      ["c",
                        "d"]],[("c","c"), ("d","a"),
     ("a","d"), ("b","b")]),
  ("R46","R37","A1",[["a", "c"],
                      ["b",
                        "d"]],[("b","c"), ("d","a"),
     ("a","d"), ("c","b")]),
  ("R46","R37","A1",[["a", "c"],
                      ["b",
                        "d"]],[("b","a"), ("d","c"),
     ("a","b"), ("c","d")]),
  ("R36","R39","A1",[["c", "d"], ["a"],
                      ["b"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R39","R36","A4",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R35","R40","A2",[["a", "b"], ["c"],
                      ["d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R35","R41","A2",[["a", "b"], ["d"],
                      ["c"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R40","R35","A2",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("d","d"),
     ("c","c"), ("b","b")]),
  ("R41","R35","A2",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("d","d"),
     ("c","c"), ("b","b")]),
  ("R33","R36","A4",[["b", "d"], ["a"],
                      ["c"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R36","R33","A3",[["d"], ["a", "b"],
                      ["c"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R32","R39","A3",[["a", "c"], ["d"],
                      ["b"]],[("a","d"), ("c","b"),
    ("d","a"), ("b","c")]),
  ("R39","R32","A1",[["d"], ["a", "b"],
                      ["c"]],[("a","d"), ("c","b"),
    ("d","a"), ("b","c")]),
  ("R31","R38","A1",[["b", "d"], ["a"],
                      ["c"]],[("b","d"), ("d","b"),
    ("a","c"), ("c","a")]),
  ("R31","R41","A1",[["a", "b", "c"],
                      ["d"]],[("b","b"), ("d","c"),
    ("a","a"), ("c","d")]),
  ("R31","R45","A3",[["a", "b"], ["c"],
                      ["d"]],[("b","c"), ("d","a"),
    ("a","d"), ("c","b")]),
  ("R31","R45","A3",[["b", "d"], ["a"],
                      ["c"]],[("b","a"), ("d","b"),
    ("a","c"), ("c","d")]),
  ("R31","R45","A3",[["a", "c"], ["d"],
                      ["b"]],[("b","d"), ("d","c"),
    ("a","b"), ("c","a")]),
  ("R31","R45","A3",[["c", "d"], ["b"],
                      ["a"]],[("b","b"), ("d","d"),
    ("a","a"), ("c","c")]),
  ("R38","R31","A2",[["b", "d"], ["a"],
                      ["c"]],[("c","a"), ("d","b"),
    ("a","c"), ("b","d")]),
  ("R41","R31","A3",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("d","c"),
    ("c","d"), ("b","b")]),
  ("R45","R31","A1",[["c"], ["d"],
                      ["a",
                        "b"]],[("a","c"), ("c","d"),
     ("d","b"), ("b","a")]),
  ("R45","R31","A3",[["c"], ["d"],
                      ["a",
                        "b"]],[("a","d"), ("c","b"),
     ("d","a"), ("b","c")]),
  ("R45","R31","A2",[["c"], ["d"],
                      ["a",
                        "b"]],[("a","b"), ("c","a"),
     ("d","c"), ("b","d")]),
  ("R45","R31","A4",[["c"], ["d"],
                      ["a",
                        "b"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R30","R31","A3",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("d","c"),
    ("c","d"), ("b","b")]),
  ("R30","R41","A3",[["a", "b", "c"],
                      ["d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R30","R47","A4",[["a", "b"],
                      ["c",
                        "d"]],[("a","a"), ("d","d"),
     ("c","c"), ("b","b")]),
  ("R31","R30","A1",[["c"], ["a", "b"],
                      ["d"]],[("b","b"), ("d","c"),
    ("a","a"), ("c","d")]),
  ("R41","R30","A3",[["c"], ["a", "b"],
                      ["d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R47","R30","A1",[["a", "b"], ["d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R29","R36","A3",[["c", "d"],
                      ["a",
                        "b"]],[("a","d"), ("c","b"),
     ("d","a"), ("b","c")]),
  ("R29","R36","A4",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R29","R39","A3",[["c", "d"], ["a"],
                      ["b"]],[("a","d"), ("c","b"),
    ("d","a"), ("b","c")]),
  ("R29","R39","A4",[["c", "d"], ["a"],
                      ["b"]],[("a","a"), ("c","c"),
    ("d","d"), ("b","b")]),
  ("R36","R29","A1",[["a"], ["b"],
                      ["c",
                        "d"]],[("c","b"), ("d","a"),
     ("a","d"), ("b","c")]),
  ("R36","R29","A1",[["d"], ["c"],
                      ["a",
                        "b"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R39","R29","A4",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","d"), ("c","b"),
     ("d","a"), ("b","c")]),
  ("R39","R29","A4",[["d"], ["c"],
                      ["a",
                        "b"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R28","R32","A4",[["d"], ["a", "b"],
                      ["c"]],[("c","b"), ("d","a"),
    ("a","d"), ("b","c")]),
  ("R28","R32","A3",[["d"], ["a", "b"],
                      ["c"]],[("c","c"), ("d","a"),
    ("a","d"), ("b","b")]),
  ("R28","R38","A3",[["a", "c"], ["b"],
                      ["d"]],[("c","b"), ("d","d"),
    ("a","a"), ("b","c")]),
  ("R28","R38","A4",[["a", "c"], ["b"],
                      ["d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R28","R39","A3",[["a", "c"], ["d"],
                      ["b"]],[("c","b"), ("d","d"),
    ("a","a"), ("b","c")]),
  ("R28","R39","A4",[["a", "c"], ["d"],
                      ["b"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R32","R28","A3",[["a"], ["c"],
                      ["b",
                        "d"]],[("a","d"), ("c","b"),
     ("d","a"), ("b","c")]),
  ("R32","R28","A3",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","d"), ("c","c"),
     ("d","a"), ("b","b")]),
  ("R38","R28","A4",[["a"], ["b"],
                      ["c",
                        "d"]],[("c","b"), ("d","d"),
     ("a","a"), ("b","c")]),
  ("R38","R28","A4",[["a"], ["c"],
                      ["b",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R39","R28","A1",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("c","b"),
     ("d","d"), ("b","c")]),
  ("R39","R28","A1",[["a"], ["c"],
                      ["b",
                        "d"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R25","R26","A2",[["c", "d"],
                      ["a",
                        "b"]],[("c","b"), ("d","d"),
     ("a","a"), ("b","c")]),
  ("R25","R26","A2",[["b", "d"],
                      ["a",
                        "c"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R25","R28","A1",[["b", "d"], ["a"],
                      ["c"]],[("c","b"), ("d","d"),
    ("a","a"), ("b","c")]),
  ("R25","R28","A1",[["c", "d"], ["a"],
                      ["b"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R25","R36","A4",[["a", "c"], ["d"],
                      ["b"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R26","R25","A2",[["b", "d"], ["a"],
                      ["c"]],[("b","c"), ("d","d"),
    ("a","a"), ("c","b")]),
  ("R26","R25","A1",[["b", "d"], ["a"],
                      ["c"]],[("b","b"), ("d","d"),
    ("a","a"), ("c","c")]),
  ("R28","R25","A2",[["c", "d"],
                      ["a",
                        "b"]],[("c","b"), ("d","d"),
     ("a","a"), ("b","c")]),
  ("R28","R25","A1",[["c", "d"],
                      ["a",
                        "b"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R36","R25","A2",[["a"], ["c"],
                      ["b",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R24","R34","A3",[["b"], ["a", "d"],
                      ["c"]],[("c","b"), ("d","a"),
    ("a","d"), ("b","c")]),
  ("R24","R42","A4",[["a", "b"],
                      ["c",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R34","R24","A3",[["c"], ["a"],
                      ["b",
                        "d"]],[("a","d"), ("b","c"),
     ("c","b"), ("d","a")]),
  ("R42","R24","A2",[["b"], ["a"],
                      ["c",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R22","R29","A3",[["a", "c"], ["d"],
                      ["b"]],[("a","d"), ("c","b"),
    ("d","a"), ("b","c")]),
  ("R22","R29","A3",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("c","c"),
    ("d","d"), ("b","b")]),
  ("R22","R32","A4",[["a", "b"], ["d"],
                      ["c"]],[("a","a"), ("c","c"),
    ("d","d"), ("b","b")]),
  ("R22","R33","A2",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R29","R22","A1",[["d"], ["a", "b"],
                      ["c"]],[("a","d"), ("c","b"),
    ("d","a"), ("b","c")]),
  ("R29","R22","A2",[["d"], ["a", "b"],
                      ["c"]],[("a","a"), ("c","c"),
    ("d","d"), ("b","b")]),
  ("R32","R22","A4",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("c","c"),
     ("d","d"), ("b","b")]),
  ("R33","R22","A1",[["d"], ["c"],
                      ["a",
                        "b"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R21","R22","A2",[["d"], ["c"],
                      ["a",
                        "b"]],[("a","a"), ("d","c"),
     ("c","d"), ("b","b")]),
  ("R21","R30","A4",[["a", "b"], ["d"],
                      ["c"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R21","R33","A2",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("d","c"),
     ("c","d"), ("b","b")]),
  ("R21","R35","A3",[["a", "b", "c"],
                      ["d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R21","R47","A4",[["a", "b"],
                      ["c",
                        "d"]],[("a","a"), ("d","d"),
     ("c","c"), ("b","b")]),
  ("R22","R21","A2",[["d"], ["c"],
                      ["a",
                        "b"]],[("a","a"), ("c","d"),
     ("d","c"), ("b","b")]),
  ("R30","R21","A4",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("d","d"),
     ("c","c"), ("b","b")]),
  ("R33","R21","A1",[["d"], ["c"],
                      ["a",
                        "b"]],[("c","d"), ("d","c"),
     ("a","a"), ("b","b")]),
  ("R35","R21","A3",[["c"], ["a", "b"],
                      ["d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R47","R21","A1",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R20","R21","A3",[["c"], ["a", "b"],
                      ["d"]],[("b","d"), ("d","a"),
    ("a","c"), ("c","b")]),
  ("R20","R46","A3",[["a", "c"],
                      ["b",
                        "d"]],[("b","b"), ("d","d"),
     ("a","a"), ("c","c")]),
  ("R21","R20","A3",[["a"], ["c"],
                      ["b",
                        "d"]],[("a","d"), ("d","b"),
     ("c","a"), ("b","c")]),
  ("R46","R20","A3",[["a"], ["c"],
                      ["b",
                        "d"]],[("b","b"), ("d","d"),
     ("a","a"), ("c","c")]),
  ("R19","R23","A3",[["a", "b", "d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R19","R27","A2",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("b","c"),
    ("c","b"), ("d","d")]),
  ("R19","R27","A2",[["c", "d"], ["a"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R23","R19","A4",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R27","R19","A2",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("b","c"),
     ("c","b"), ("d","d")]),
  ("R27","R19","A4",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R18","R23","A4",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("b","b"),
     ("c","d"), ("d","c")]),
  ("R23","R18","A2",[["d"], ["c"],
                      ["a",
                        "b"]],[("a","a"), ("b","b"),
     ("c","d"), ("d","c")]),
  ("R17","R19","A4",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R17","R23","A4",[["a", "b", "d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R19","R17","A3",[["d"], ["a", "b"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R23","R17","A4",[["d"], ["a", "b"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R16","R23","A3",[["a", "c"],
                      ["b",
                        "d"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R23","R16","A3",[["a"], ["c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R15","R16","A3",[["a", "b", "d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R15","R19","A4",[["a", "c"],
                      ["b",
                        "d"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R15","R42","A3",[["c"], ["a"],
                      ["b",
                        "d"]],[("a","d"), ("b","c"),
     ("c","b"), ("d","a")]),
  ("R16","R15","A4",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R19","R15","A4",[["a"], ["c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R42","R15","A4",[["b", "d"], ["a"],
                      ["c"]],[("c","b"), ("d","a"),
    ("a","d"), ("b","c")]),
  ("R14","R16","A2",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("b","b"),
     ("c","d"), ("d","c")]),
  ("R14","R18","A4",[["a", "d"],
                      ["b",
                        "c"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R14","R34","A3",[["b"], ["a", "d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","d"), ("d","c")]),
  ("R16","R14","A2",[["d"], ["c"],
                      ["a",
                        "b"]],[("a","a"), ("b","b"),
     ("c","d"), ("d","c")]),
  ("R18","R14","A2",[["a"], ["d"], ["c"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R34","R14","A3",[["a", "b", "c"],
                      ["d"]],[("a","a"), ("b","b"),
    ("c","d"), ("d","c")]),
  ("R13","R15","A3",[["c", "d"],
                      ["a",
                        "b"]],[("a","a"), ("c","b"),
     ("b","c"), ("d","d")]),
  ("R13","R27","A4",[["a", "c"],
                      ["b",
                        "d"]],[("a","a"), ("c","b"),
     ("b","c"), ("d","d")]),
  ("R13","R27","A4",[["a", "b"],
                      ["c",
                        "d"]],[("a","a"), ("c","c"),
     ("b","b"), ("d","d")]),
  ("R15","R13","A2",[["b", "d"], ["a"],
                      ["c"]],[("a","a"), ("b","c"),
    ("c","b"), ("d","d")]),
  ("R27","R13","A3",[["a"], ["b"], ["d"],
                      ["c"]],[("a","a"), ("b","c"),
    ("c","b"), ("d","d")]),
  ("R27","R13","A1",[["a"], ["b"], ["d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R12","R16","A3",[["a"], ["c"], ["d"],
                      ["b"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R12","R23","A3",[["a", "c"],
                      ["b",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R12","R44","A2",[["a", "b"], ["d"],
                      ["c"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R16","R12","A3",[["a", "c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R23","R12","A3",[["a", "c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R44","R12","A3",[["a", "b"],
                      ["c",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R11","R17","A4",[["a", "c"],
                      ["b",
                        "d"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R11","R42","A3",[["c"], ["a"],
                      ["b",
                        "d"]],[("a","b"), ("b","a"),
     ("c","d"), ("d","c")]),
  ("R17","R11","A3",[["c"], ["a"], ["b"],
                      ["d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R42","R11","A4",[["d"], ["a", "b"],
                      ["c"]],[("c","d"), ("d","c"),
    ("a","b"), ("b","a")]),
  ("R10","R12","A3",[["a", "b", "d"],
                      ["c"]],[("a","d"), ("b","c"),
    ("c","b"), ("d","a")]),
  ("R10","R12","A4",[["a", "b", "d"],
                      ["c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R10","R15","A4",[["a"], ["c"], ["d"],
                      ["b"]],[("a","d"), ("b","c"),
    ("c","b"), ("d","a")]),
  ("R10","R15","A3",[["a"], ["c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R10","R19","A4",[["a", "c"],
                      ["b",
                        "d"]],[("a","d"), ("b","c"),
     ("c","b"), ("d","a")]),
  ("R10","R19","A3",[["a", "c"],
                      ["b",
                        "d"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R10","R36","A2",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","d"), ("b","c"),
     ("c","b"), ("d","a")]),
  ("R10","R36","A1",[["a"], ["b"],
                      ["c",
                        "d"]],[("a","a"), ("b","b"),
     ("c","c"), ("d","d")]),
  ("R12","R10","A4",[["a", "c"], ["d"],
                      ["b"]],[("c","b"), ("d","a"),
    ("a","d"), ("b","c")]),
  ("R12","R10","A4",[["b", "d"], ["a"],
                      ["c"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R15","R10","A4",[["b", "d"], ["a"],
                      ["c"]],[("a","d"), ("b","c"),
    ("c","b"), ("d","a")]),
  ("R15","R10","A4",[["a", "c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R19","R10","A4",[["b", "d"], ["a"],
                      ["c"]],[("a","d"), ("b","c"),
    ("c","b"), ("d","a")]),
  ("R19","R10","A4",[["a", "c"], ["d"],
                      ["b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R36","R10","A4",[["c", "d"],
                      ["a",
                        "b"]],[("c","b"), ("d","a"),
     ("a","d"), ("b","c")]),
  ("R36","R10","A4",[["a", "b"],
                      ["c",
                        "d"]],[("c","c"), ("d","d"),
     ("a","a"), ("b","b")]),
  ("R9","R12","A3",[["c", "d"],
                     ["a",
                       "b"]],[("a","a"), ("b","b"),
    ("c","d"), ("d","c")]),
  ("R9","R14","A2",[["a"], ["d"], ["c"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R9","R18","A2",[["a", "d"],
                     ["b",
                       "c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R9","R35","A1",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R9","R40","A1",[["a", "b"], ["c"],
                     ["d"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R9","R41","A1",[["a", "b"], ["d"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R9","R47","A4",[["c"], ["a", "b"],
                     ["d"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R12","R9","A1",[["d"], ["c"],
                     ["a",
                       "b"]],[("c","d"), ("d","c"),
    ("a","a"), ("b","b")]),
  ("R14","R9","A4",[["a", "d"], ["c"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R18","R9","A2",[["a", "d"], ["c"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R35","R9","A2",[["a", "b"],
                     ["c",
                       "d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R40","R9","A2",[["a", "b"],
                     ["c",
                       "d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R41","R9","A2",[["a", "b"],
                     ["c",
                       "d"]],[("a","a"), ("d","d"),
    ("c","c"), ("b","b")]),
  ("R47","R9","A4",[["a", "b", "c"],
                     ["d"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R8","R17","A4",[["c", "d"],
                     ["a",
                       "b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R8","R26","A3",[["a"], ["c"],
                     ["b",
                       "d"]],[("a","d"), ("b","c"),
    ("c","b"), ("d","a")]),
  ("R8","R26","A3",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","d"), ("b","b"),
    ("c","c"), ("d","a")]),
  ("R17","R8","A2",[["d"], ["c"],
                     ["a",
                       "b"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R26","R8","A4",[["d"], ["a", "b"],
                     ["c"]],[("b","c"), ("d","a"),
   ("a","d"), ("c","b")]),
  ("R26","R8","A3",[["d"], ["a", "b"],
                     ["c"]],[("b","b"), ("d","a"),
   ("a","d"), ("c","c")]),
  ("R7","R15","A4",[["b", "d"], ["a"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R7","R16","A4",[["a", "b", "d"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R7","R17","A3",[["a", "c"],
                     ["b",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R7","R43","A3",[["d"], ["a", "b"],
                     ["c"]],[("a","d"), ("b","c"),
   ("c","b"), ("d","a")]),
  ("R7","R43","A3",[["a"], ["c", "d"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R15","R7","A3",[["d"], ["a", "b"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R16","R7","A4",[["d"], ["a", "b"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R17","R7","A3",[["a"], ["c"], ["d"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R43","R7","A3",[["a"], ["c"], ["d"],
                     ["b"]],[("a","d"), ("b","c"),
   ("c","b"), ("d","a")]),
  ("R43","R7","A4",[["a"], ["c"], ["d"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R6","R15","A3",[["b", "d"], ["a"],
                     ["c"]],[("a","d"), ("b","c"),
   ("c","b"), ("d","a")]),
  ("R6","R17","A4",[["d"], ["a", "b"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R6","R19","A4",[["b", "d"], ["a"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R6","R42","A3",[["c"], ["a"],
                     ["b",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R15","R6","A3",[["a", "c"],
                     ["b",
                       "d"]],[("a","d"), ("b","c"),
    ("c","b"), ("d","a")]),
  ("R17","R6","A4",[["d"], ["b"], ["a"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R19","R6","A3",[["d"], ["b"], ["a"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R42","R6","A4",[["a", "c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R5","R7","A3",[["a"], ["c"], ["d"],
                    ["b"]],[("c","c"), ("d","d"),
  ("a","a"), ("b","b")]),
  ("R5","R10","A4",[["a", "c"], ["d"],
                     ["b"]],[("c","b"), ("d","a"),
   ("a","d"), ("b","c")]),
  ("R5","R10","A4",[["b", "d"], ["a"],
                     ["c"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R5","R12","A4",[["a", "b", "d"],
                     ["c"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R5","R15","A4",[["a"], ["c"], ["d"],
                     ["b"]],[("c","b"), ("d","a"),
   ("a","d"), ("b","c")]),
  ("R5","R17","A3",[["a", "c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R5","R33","A2",[["a"], ["b"],
                     ["c",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R5","R43","A3",[["d"], ["a", "b"],
                     ["c"]],[("c","b"), ("d","a"),
   ("a","d"), ("b","c")]),
  ("R5","R43","A3",[["a"], ["c", "d"],
                     ["b"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R5","R47","A1",[["d"], ["c"],
                     ["a",
                       "b"]],[("c","d"), ("d","c"),
    ("a","a"), ("b","b")]),
  ("R7","R5","A3",[["a", "c"], ["d"],
                    ["b"]],[("a","a"), ("b","b"),
  ("c","c"), ("d","d")]),
  ("R10","R5","A3",[["d"], ["a", "b"],
                     ["c"]],[("a","d"), ("b","c"),
   ("c","b"), ("d","a")]),
  ("R10","R5","A4",[["d"], ["a", "b"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R12","R5","A4",[["d"], ["a", "b"],
                     ["c"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R15","R5","A4",[["d"], ["a", "b"],
                     ["c"]],[("a","d"), ("b","c"),
   ("c","b"), ("d","a")]),
  ("R17","R5","A3",[["a", "c"], ["d"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R33","R5","A3",[["a", "b"],
                     ["c",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R43","R5","A3",[["a", "c"], ["d"],
                     ["b"]],[("a","d"), ("b","c"),
   ("c","b"), ("d","a")]),
  ("R43","R5","A4",[["a", "c"], ["d"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R47","R5","A3",[["c", "d"],
                     ["a",
                       "b"]],[("a","a"), ("b","b"),
    ("c","d"), ("d","c")]),
  ("R4","R8","A4",[["d"], ["c"],
                    ["a",
                      "b"]],[("a","a"), ("b","b"),
   ("c","d"), ("d","c")]),
  ("R4","R17","A4",[["c", "d"],
                     ["a",
                       "b"]],[("a","a"), ("b","b"),
    ("c","d"), ("d","c")]),
  ("R4","R18","A3",[["a", "b", "c"],
                     ["d"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R4","R47","A2",[["a", "d"], ["c"],
                     ["b"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R8","R4","A4",[["d"], ["c"],
                    ["a",
                      "b"]],[("a","a"), ("b","b"),
   ("c","d"), ("d","c")]),
  ("R17","R4","A2",[["d"], ["c"],
                     ["a",
                       "b"]],[("a","a"), ("b","b"),
    ("c","d"), ("d","c")]),
  ("R18","R4","A3",[["c"], ["a", "b"],
                     ["d"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R47","R4","A2",[["a", "d"],
                     ["b",
                       "c"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R3","R5","A4",[["a", "c"], ["d"],
                    ["b"]],[("a","a"), ("b","b"),
  ("c","c"), ("d","d")]),
  ("R3","R11","A4",[["c"], ["a"], ["b"],
                     ["d"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R3","R17","A4",[["a", "c"],
                     ["b",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R3","R37","A3",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","d"), ("b","b"),
    ("c","c"), ("d","a")]),
  ("R3","R37","A3",[["c"], ["d"],
                     ["a",
                       "b"]],[("a","b"), ("b","d"),
    ("c","a"), ("d","c")]),
  ("R3","R42","A3",[["d"], ["b"], ["a"],
                     ["c"]],[("a","a"), ("b","b"),
   ("c","c"), ("d","d")]),
  ("R5","R3","A3",[["c"], ["a"],
                    ["b",
                      "d"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R11","R3","A4",[["c"], ["a"],
                     ["b",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R17","R3","A3",[["c"], ["a"],
                     ["b",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R37","R3","A3",[["d"], ["a", "b"],
                     ["c"]],[("a","d"), ("c","c"),
   ("b","b"), ("d","a")]),
  ("R37","R3","A4",[["d"], ["a", "b"],
                     ["c"]],[("a","c"), ("c","d"),
   ("b","a"), ("d","b")]),
  ("R42","R3","A3",[["d"], ["a", "b"],
                     ["c"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R2","R13","A4",[["a"], ["b"], ["d"],
                     ["c"]],[("a","a"), ("c","c"),
   ("b","b"), ("d","d")]),
  ("R2","R27","A4",[["a", "c"],
                     ["b",
                       "d"]],[("a","a"), ("c","b"),
    ("b","c"), ("d","d")]),
  ("R2","R27","A4",[["a", "b"],
                     ["c",
                       "d"]],[("a","a"), ("c","c"),
    ("b","b"), ("d","d")]),
  ("R2","R28","A1",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","a"), ("c","b"),
    ("b","c"), ("d","d")]),
  ("R2","R28","A1",[["a"], ["c"],
                     ["b",
                       "d"]],[("a","a"), ("c","c"),
    ("b","b"), ("d","d")]),
  ("R2","R38","A1",[["a", "c"], ["b"],
                     ["d"]],[("a","a"), ("c","c"),
   ("b","b"), ("d","d")]),
  ("R2","R39","A1",[["a", "c"], ["d"],
                     ["b"]],[("a","a"), ("c","c"),
   ("b","b"), ("d","d")]),
  ("R13","R2","A4",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","a"), ("c","c"),
    ("b","b"), ("d","d")]),
  ("R27","R2","A3",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","a"), ("b","c"),
    ("c","b"), ("d","d")]),
  ("R27","R2","A1",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R28","R2","A3",[["a", "c"],
                     ["b",
                       "d"]],[("c","b"), ("d","d"),
    ("a","a"), ("b","c")]),
  ("R28","R2","A4",[["a", "c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R38","R2","A4",[["a", "c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R39","R2","A1",[["a", "c"],
                     ["b",
                       "d"]],[("a","a"), ("c","c"),
    ("d","d"), ("b","b")]),
  ("R1","R2","A1",[["c", "d"], ["a"],
                    ["b"]],[("c","c"), ("d","d"),
  ("a","a"), ("b","b")]),
  ("R1","R19","A3",[["a", "b"],
                     ["c",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R1","R25","A4",[["a"], ["c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R1","R36","A4",[["a", "c"], ["d"],
                     ["b"]],[("c","c"), ("d","d"),
   ("a","a"), ("b","b")]),
  ("R2","R1","A2",[["c", "d"],
                    ["a",
                      "b"]],[("a","a"), ("c","c"),
   ("b","b"), ("d","d")]),
  ("R19","R1","A1",[["a"], ["b"],
                     ["c",
                       "d"]],[("a","a"), ("b","b"),
    ("c","c"), ("d","d")]),
  ("R25","R1","A4",[["a", "c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")]),
  ("R36","R1","A2",[["a", "c"],
                     ["b",
                       "d"]],[("c","c"), ("d","d"),
    ("a","a"), ("b","b")])]
