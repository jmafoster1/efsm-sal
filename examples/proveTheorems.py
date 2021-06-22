#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jun 19 11:34:37 2021

@author: michael
"""
import os
import re

transition_re = re.compile('definition "(\w+)" :: "transition" where')

examples = ["coin-tea", "drinks", "lift-controller", "linkedin"]

for d in examples:
    for f in os.listdir(d):
        if f.endswith("Theorems.thy"):
            newcontent = ""
            with open(f"{d}/{f}") as t:
                name = ""
                imports = ""
                for line in t:
                    if line.startswith("theory"):
                        imports = line.strip().split()[1].replace("Theorems", "")
                        imports = "_".join([x.capitalize() for x in imports.split("_")]).replace("Ltl", "LTL")
                    if line.startswith("imports"):
                        line = line.strip() + " " + imports + "\n"
                    if line.startswith("lemma"):
                        name = line.split()[1]
                    if line == "oops\n":
                        line = f"using {name} by blast\n"
                    newcontent += line
            with open(f"{d}/{f}", 'w') as t:
                print(newcontent, file=t)

for d in examples:
    for f in os.listdir(d):
        if f.startswith("XXX") and f.endswith(".thy"):
            newcontent = ""
            imports = ""
            with open(f"{d}/{f}") as t:
                for line in t:
                    if line.startswith("theory"):
                        imports = line.strip().split()[1].replace("Theorems", "").replace("XXX", "")
                        imports = "_".join([x.capitalize() for x in imports.split("_")]).replace("Ltl", "LTL")
                    if line.startswith("imports"):
                        line = line.replace("../Contexts", "EFSM.EFSM")
                        line = line.strip() + " " + imports + "\n"
                    if line != "end\n":
                        newcontent += line
                newcontent += "end"
            with open(f"{d}/{f}", 'w') as t:
                print(newcontent, file=t)
