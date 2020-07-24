#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jul 18 11:07:54 2020

@author: michael
"""

import pydotplus
import antlr4
from CounterexampleLexer import CounterexampleLexer
from CounterexampleParser import CounterexampleParser
from HTMLCounterexampleListener import HTMLCounterexampleListener
import os
import output as op


root = "/home/michael/Documents/efsm-sal/coin-tea"
dotfile = f"{root}/dotfiles/Coin_Tea_Broken.dot"
cfile = f"{root}/models/straight.cex"
steps = f"{root}/counterexample"

if not os.path.exists(steps):
    os.mkdir(steps)


graph = pydotplus.graphviz.graph_from_dot_file(dotfile)
graph.set_size('"10,10!"')

edges = {edge.get("id"): edge for edge in graph.get_edges()}
nodes = {node.get_name(): node for node in graph.get_nodes()}

nodes["s0"].set('color', 'red')

graph.write_png(f"{steps}/step-init.png")

nodes["s0"].set('color', 'black')



input_stream = antlr4.FileStream(cfile)
lexer = CounterexampleLexer(input_stream)
stream =antlr4. CommonTokenStream(lexer)
parser = CounterexampleParser(stream)
tree = parser.counterexample()

with open(f"{steps}/trace.html","w") as output:
    listener = HTMLCounterexampleListener(output)
    walker = antlr4.ParseTreeWalker()
    walker.walk(listener, tree)


def colorstep(e):
    print(e)
    print('tid' in e and e['tid'] != 'SINK_HOLE')

    if 'tid' in e and e['tid'] != 'SINK_HOLE':
        edges[e['tid']].set('color', 'red')
        edges[e['tid']].set('fontcolor', 'red')
        
        nodes[f"s{e['state']}"].set('color', 'red')
        
        graph.write_png(f"{steps}/step-{e['stepNo']}.png")

        [edges[t].set('color', 'black') for t in edges]
        [edges[t].set('fontcolor', 'black') for t in edges]
        [nodes[t].set('color', 'black') for t in nodes]

    
        
for e in listener.trace:
    colorstep(e)
    # print(e)

for e in listener.cycle:
    colorstep(e)
    # print(e)


with open(f"{steps}/autoviz.html", 'w') as f:
    print(op.output(listener.trace), file=f)