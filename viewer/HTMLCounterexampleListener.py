import antlr4
from CounterexampleParser import CounterexampleParser
from itertools import takewhile
import re

str_re = re.compile("Str\(String__([\w_]+)\)")
num_re = re.compile("Num\((-?\d+)\)")
some_re = re.compile("Some\((.*)\)")

def processValue(value):
    match = str_re.search(value)
    if match:
        return f"'{match.group(1)}'"
    match = num_re.search(value)
    return int(match.group(1))


def just(v_option):
    if v_option == "None":
        return None
    return processValue(some_re.search(v_option).group(1))


# This class defines a complete listener for a parse tree produced by CounterexampleParser.
class HTMLCounterexampleListener(antlr4.ParseTreeListener):
    
    def __init__(self, output):
        self.trace = []
        self.cycle = []
        self.incycle = False
        self.output = output
        self.steps = set()
        self.event = {}
        self.output.write('<html><head><meta charset="UTF-8"/></head><body>')
        self.output.write('<h1>COUNTEREXAMPLE</h1>')
    
    # Enter a parse tree produced by CounterexampleParser#label.
    def enterLabel(self, ctx:CounterexampleParser.LabelContext):
        label = str(ctx.AN_STRING())
        self.event['label'] = label
        # self.output.write(f"<p>Label: <strong>{label}</strong></p>")
    
    
    # Enter a parse tree produced by CounterexampleParser#action.
    def exitTransition(self, ctx:CounterexampleParser.ActionContext):
        
        if self.event['stepNo'] in self.steps:
            return
        
        self.output.write("<div>")
        self.output.write(f"<h3>Step: <strong>{self.event['stepNo']}</strong></h3>")
        
        cfstate = self.event['state']
        statestring = f"q<sub>{cfstate}</sub>" if cfstate != "NULL_STATE" else cfstate
        self.output.write(f"<p>State: {statestring}</p>")
        self.output.write(f"<p>Label: {self.event['label']}</p>")
        
        inputstring = [str(i) for i in self.event['inputs']]
        self.output.write(f"<p>Inputs: [{', '.join(inputstring)}]</p>")
        
        regstring = [f"r<sub>{r}</sub> := {self.event['regs'][r]}" for r in self.event['regs'] if self.event['regs'][r] is not None]
        self.output.write(f"<p>Registers: [{', '.join(regstring)}]</p>")

        if 'tid' in self.event:
            self.output.write(f"<p>Transition: {self.event['tid']}</p>")
        
        outputstring = [str(i) for i in self.event['outputs']]
        self.output.write(f"<p>Outputs: [{', '.join(outputstring)}]</p>")
        self.output.write("</div>")
        
        self.steps.add(self.event['stepNo'])
        
        if self.incycle:
            self.cycle.append(self.event)
        else:    
            self.trace.append(self.event)
        self.event = {}

    
    # Enter a parse tree produced by CounterexampleParser#stepHead.
    def enterStep_head(self, ctx:CounterexampleParser.LabelContext):
        self.event['stepNo'] = int(str(ctx.NUMBER()))

    # Enter a parse tree produced by CounterexampleParser#cfstate.
    def enterCfstate(self, ctx:CounterexampleParser.CfstateContext):
        self.event['state'] = str(ctx.getText().strip().replace("cfstate = ", "").replace("State__", ""))

    # Enter a parse tree produced by CounterexampleParser#ip.
    def enterIp(self, ctx:CounterexampleParser.IpContext):
        self.event['inputs'][int(str(ctx.NUMBER()))] = str(ctx.B_VALUE())


    def enterInputs(self, ctx:CounterexampleParser.InputsContext):
        self.event['inputs'] = {}

    # Exit a parse tree produced by CounterexampleParser#inputs.
    def exitInputs(self, ctx:CounterexampleParser.InputsContext):
        inputs = self.event['inputs']
        inputs = [inputs[k] for k in sorted(list(inputs))]
        inputs = list(takewhile(lambda x: x != "ValueBB", inputs))
        inputs = [processValue(i) for i in inputs]
        self.event['inputs'] = inputs

        # self.output.write(f"<p>Inputs: {inputs}</p>")


    # Enter a parse tree produced by CounterexampleParser#op.
    def enterOp(self, ctx:CounterexampleParser.OpContext):
        self.event['outputs'][int(str(ctx.NUMBER()))] = str(ctx.B_OPTION())


    # Enter a parse tree produced by CounterexampleParser#outputs.
    def enterOutputs(self, ctx:CounterexampleParser.OutputsContext):
        self.event['outputs'] = {}


    # Exit a parse tree produced by CounterexampleParser#outputs.
    def exitOutputs(self, ctx:CounterexampleParser.OutputsContext):
        outputs = self.event['outputs']
        outputs = [outputs[k] for k in sorted(list(outputs))]
        outputs = list(takewhile(lambda x: x != "OptionBB", outputs))
        outputs = [just(i) for i in outputs]
        self.event['outputs'] = outputs

        # self.output.write(f"<p>Outputs: {outputs}</p>")


    # Enter a parse tree produced by CounterexampleParser#reg.
    def enterReg(self, ctx:CounterexampleParser.RegContext):
        self.event['regs'][str(ctx.REG())] = str(ctx.B_OPTION())


    def enterRegs(self, ctx:CounterexampleParser.RegsContext):
        self.event['regs'] = {}


    # Exit a parse tree produced by CounterexampleParser#regs.
    def exitRegs(self, ctx:CounterexampleParser.RegsContext):
        regs = self.event['regs']
        regs = [(k, regs[k]) for k in sorted(list(regs))]
        regs = list(takewhile(lambda x: x[1] != "OptionBB", regs))
        regs = {r.replace("r__", ""): just(i) for r, i in regs}
        self.event['regs'] = regs

        # self.output.write(f"<p>Regs: {regs}</p>")


    # Enter a parse tree produced by CounterexampleParser#t_info.
    def enterT_id(self, ctx:CounterexampleParser.T_infoContext):
        tid = str(ctx.AN_STRING())
        self.event['tid'] = tid
        # self.output.write(f"<p>ID: <strong>{tid}</strong></p>")

    
    # Enter a parse tree produced by CounterexampleParser#cycle.
    def enterCycle(self, ctx:CounterexampleParser.T_infoContext):
        self.incycle = True
        self.output.write("<div style='padding-left: 15px'><h2>CYCLE</h2>")

    # Enter a parse tree produced by CounterexampleParser#cycle.
    def exitCycle(self, ctx:CounterexampleParser.T_infoContext):
        self.output.write("</div>")


    # Enter a parse tree produced by CounterexampleParser#counterexample.
    def enterCounterexample(self, ctx:CounterexampleParser.CounterexampleContext):
        self.output.write(f"<p>")

    # Exit a parse tree produced by CounterexampleParser#counterexample.
    def exitCounterexample(self, ctx:CounterexampleParser.CounterexampleContext):
        self.output.write("</p></body></html>")



del CounterexampleParser