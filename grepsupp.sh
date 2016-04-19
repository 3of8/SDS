#!/bin/sh
grep -E -o "R[0-9]+\.support" SDS_Impossibility.thy | sort | uniq | sed -r 's/R([0-9]*)\.support/\1/g' | sort -h
