#!/bin/sh
ghc -O2 -rtsopts deque2.hs && ./deque2 +RTS -K200M -RTS

