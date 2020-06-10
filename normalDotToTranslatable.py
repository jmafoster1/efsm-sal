#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Jun 10 14:45:36 2020

@author: michael
"""

import csv
import pandas as pd
import re


varnames = {}
r = 1


def value(v):
    if v.isnumeric():
        return v
    return f"\"{v}\""


# We need the "+1" to account for the fact that dot2isabelle isn't indexing from 0 yet
def ipToGuard(ip, ix):
    i, v = ip.split("?")
    return f"i_{ix+1} = {value(v)}"

# We need the "+1" to account for the fact that dot2isabelle isn't indexing from 0 yet
def opToOutput(ip, ix):
    i, v = ip.split("!")
    return f"o_{ix+1} := {value(v)}"


def preToGuard(p):
    global r
    match = re.search("\(?(\w+)==(\w+)\)?", p)
    if match.group(1) not in varnames:
        varnames[match.group(1)] = f"r_{r}"
        r += 1
    if match:
        return f"{varnames[match.group(1)]} = {value(match.group(2))}"


def postToUpdate(ip):
    global r
    i, v = ip.split("=")
    if i not in varnames:
        varnames[i] = f"r_{r}"
        r += 1
    return f"{varnames[i]} := {value(v)}"


def toTransition(row):
    label = row['label']
    inputs = [i for i in row['input'].split(",") if i != '']
    arity = len(inputs)
    guards = [preToGuard(i.strip()) for i in row['pre'].split("&&") if i != '']
    guards += [ipToGuard(i, ix) for ix, i in enumerate(inputs)]
    outputs = [i.strip() for i in row['output'].split(",") if i != '']
    outputs = [opToOutput(op, ox) for ox, op in enumerate(outputs)]
    updates = [i.strip() for i in row['post'].split(";") if i != '']
    updates = [postToUpdate(p) for p in updates]
    return f"{label}:{arity}[{', '.join(guards)}]/{', '.join(outputs)}[{', '.join(updates)}]".replace("[]", "")


with open('/tmp/table.csv') as csv_file:
    rows = list(csv.reader(csv_file, delimiter=','))
    table = pd.DataFrame([[c.replace("\n", "") for c in row] for row in rows[1:]], columns=rows[0])

conversion = {}
for index, row in table.iterrows():
    conversion[row['label']] = toTransition(row)

newout = []
states = {}
s = 0
with open("/tmp/liftController.dot") as f:
    for line in f:
        line = line.replace("\n", "")
        match = re.search('(\w+)\[((fillcolor="gray", )?label=<(\w+))>\];', line)
        if match:
            name = match.group(1)
            fill = match.group(3) or ""
            label = match.group(4)
            if name not in states:
                states[name] = f"s{s}"
                s += 1
            newout.append(f'{states[name]}[{fill}label="{label}"];')
                
        else:
            match = re.search('(\w+)\->(\w+)\[label="(\w+)"\];', line)
            if match:
                newlabel = conversion[match.group(3)].replace("[", "&#91;")
                newlabel = newlabel.replace("]", "&#93;")
                newlabel = re.sub("(\w+)_(\d+)", r"\1<sub>\2</sub>", newlabel)
                newout.append(f"{states[match.group(1)]}->{states[match.group(2)]}[label=<<i>{newlabel}</i>>];")
            
            else:
                newout.append(line)

with open("/tmp/liftController2.dot", 'w') as f:
    print("\n".join(newout), file=f)



# We'll be able to drop this bit once dot2isabelle indexes inputs and outputs from 0
success = input("Successfully converted?[y]/n")

if success == "n":
    exit()

newout = []
with open("/tmp/XXXliftController2.thy") as f:
    for line in f:
        line = line.replace("\n", "")
        newout.append(re.sub("\(V \(I (\d+)\)\)", lambda m: '(V (I {0}))'.format(int(m.group(1)) - 1), line))

with open("/tmp/XXXliftController2.thy", 'w') as f:
    print("\n".join(newout), file=f)

