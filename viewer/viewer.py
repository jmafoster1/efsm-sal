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
from PIL import Image


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

init_im = Image.open(f"{steps}/step-init.png")
width, height = init_im.size


input_stream = antlr4.FileStream(cfile)
lexer = CounterexampleLexer(input_stream)
stream =antlr4. CommonTokenStream(lexer)
parser = CounterexampleParser(stream)
tree = parser.counterexample()

with open(f"{steps}/trace.html","w") as output:
    listener = HTMLCounterexampleListener(output)
    walker = antlr4.ParseTreeWalker()
    walker.walk(listener, tree)


def resize(img, width, height):
    old_im = Image.open(img)
    old_size = old_im.size
    
    new_size = (width, height)
    new_im = Image.new("RGB", new_size, color=(255, 255, 255))
    new_im.paste(old_im, (int((new_size[0]-old_size[0])/2), int((new_size[1]-old_size[1])/2)))
    new_im.save(img)

def colorstep(e):
    print(e)
    if 'tid' in e and e['tid'] != 'SINK_HOLE':
        edges[e['tid']].set('color', 'red')
        edges[e['tid']].set('fontcolor', 'red')
        nodes[f"s{e['state']}"].set('color', 'red')
        graph.write_png(f"{steps}/step-{e['stepNo']}.png")
        
        edges[e['tid']].set('color', 'black')
        edges[e['tid']].set('fontcolor', 'black')
        nodes[f"s{e['state']}"].set('color', 'black')

    else:
        dead = pydotplus.graphviz.Dot()
        node = pydotplus.graphviz.Node(name='NULL_STATE', label="err", color="red")
        dead.add_node(node)
        dead.write_png(f"{steps}/step-{e['stepNo']}.png")
        resize(f"{steps}/step-{e['stepNo']}.png", width, height)
   
        
for e in listener.trace:
    colorstep(e)
    # print(e)

for e in listener.cycle:
    colorstep(e)
    # print(e)


with open(f"{steps}/autoviz.html", 'w') as f:
    print(op.output(listener.trace + listener.cycle), file=f)