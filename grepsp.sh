#!/bin/sh
grep -E -o "R[0-9]+_R[0-9]+\.strategyproofness(\\([0-9]+\\))?" SDS_Impossibility.thy | sed -r 's/R([0-9]*)_R([0-9]*)\.strategyproofness(\(([0-9]+)\))?/      (\1, \2, "\4"),/g' | sed -r 's/""/Nothing/g' | sed -r 's/"([^"]*)"/Just \1/g'
