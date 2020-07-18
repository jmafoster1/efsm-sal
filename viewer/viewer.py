#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jul 18 11:07:54 2020

@author: michael
"""

import pydotplus


root = "/home/michael/Documents/efsm-sal/coin-tea"
dotfile = f"{root}/dotfiles/Coin_Tea_Broken.dot"

graph = pydotplus.graphviz.graph_from_dot_file(dotfile)

edges = {(edge.get("id"), edge) for edge in graph.get_edges()}
nodes = {(node.get_name(), node) for node in graph.get_nodes()}

print(nodes)