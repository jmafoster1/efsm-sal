#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jul 18 12:53:11 2020

@author: michael
"""

import antlr4
from CounterexampleLexer import CounterexampleLexer
from CounterexampleParser import CounterexampleParser
from HTMLCounterexampleListener import HTMLCounterexampleListener

root = "/home/michael/Documents/efsm-sal/coin-tea"
cfile = f"{root}/models/straight.cex"

input_stream = antlr4.FileStream(cfile)
lexer = CounterexampleLexer(input_stream)
stream =antlr4. CommonTokenStream(lexer)
parser = CounterexampleParser(stream)
tree = parser.counterexample()

with open("output.html","w") as output:
    listener = HTMLCounterexampleListener(output)
    walker = antlr4.ParseTreeWalker()
    walker.walk(listener, tree)

for e in listener.trace:
    print(e)

for e in listener.cycle:
    print(e)