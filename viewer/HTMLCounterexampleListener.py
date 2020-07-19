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
        return match.group(1)
    match = num_re.search(value)
    return int(match.group(1))


def just(v_option):
    if v_option == "None":
        return None
    return processValue(some_re.search(v_option).group(1))


# This class defines a complete listener for a parse tree produced by CounterexampleParser.
class HTMLCounterexampleListener(antlr4.ParseTreeListener):
    
    def __init__(self, output):
        self.trace = {}
        self.output = output
        self.skip = False
        self.output.write('<html><head><meta charset="UTF-8"/></head><body>')
        self.output.write('<h1>COUNTEREXAMPLE</h1>')
    
    # Enter a parse tree produced by CounterexampleParser#label.
    def enterLabel(self, ctx:CounterexampleParser.LabelContext):
        label = str(ctx.AN_STRING())
        self.trace[self.stepNo]['label'] = label
        # self.output.write(f"<p>Label: <strong>{label}</strong></p>")
    
    
    # Enter a parse tree produced by CounterexampleParser#action.
    def enterAction(self, ctx:CounterexampleParser.ActionContext):
        head = ctx.step_head();
        if int(str(head.NUMBER())) in self.trace:
            self.skip = True
        else:
            self.skip = False
        pass


    # Enter a parse tree produced by CounterexampleParser#action.
    def exitAction(self, ctx:CounterexampleParser.ActionContext):
        if self.skip:
            return
        
        self.output.write(f"<h3>Step: <strong>{self.stepNo}</strong></h3>")
        
        self.output.write(f"<p>State: {self.trace[self.stepNo]['state']}</p>")
        self.output.write(f"<p>Inputs: {self.trace[self.stepNo]['inputs']}</p>")
        self.output.write(f"<p>Registers: {self.trace[self.stepNo]['regs']}</p>")

        if 'tid' in self.trace[self.stepNo]:
            self.output.write(f"<p>Transition: {self.trace[self.stepNo]['tid']}</p>")
        self.output.write(f"<p>Outputs: {self.trace[self.stepNo]['outputs']}</p>")

    
    # Enter a parse tree produced by CounterexampleParser#stepHead.
    def enterStep_head(self, ctx:CounterexampleParser.LabelContext):
        stepNo = int(str(ctx.NUMBER()))
        self.stepNo = stepNo
        if stepNo not in self.trace:
            self.trace[stepNo] = {}
        # self.output.write(f"<h3>Step: <strong>{stepNo}</strong></h3>")


    # Enter a parse tree produced by CounterexampleParser#cfstate.
    def enterCfstate(self, ctx:CounterexampleParser.CfstateContext):
        self.trace[self.stepNo]['state'] = str(ctx.getText().strip().replace("State__", "s"))

    # Enter a parse tree produced by CounterexampleParser#ip.
    def enterIp(self, ctx:CounterexampleParser.IpContext):
        self.trace[self.stepNo]['inputs'][int(str(ctx.NUMBER()))] = str(ctx.B_VALUE())


    def enterInputs(self, ctx:CounterexampleParser.InputsContext):
        self.trace[self.stepNo]['inputs'] = {}

    # Exit a parse tree produced by CounterexampleParser#inputs.
    def exitInputs(self, ctx:CounterexampleParser.InputsContext):
        inputs = self.trace[self.stepNo]['inputs']
        inputs = [inputs[k] for k in sorted(list(inputs))]
        inputs = list(takewhile(lambda x: x != "ValueBB", inputs))
        inputs = [processValue(i) for i in inputs]
        self.trace[self.stepNo]['inputs'] = inputs

        # self.output.write(f"<p>Inputs: {inputs}</p>")


    # Enter a parse tree produced by CounterexampleParser#op.
    def enterOp(self, ctx:CounterexampleParser.OpContext):
        self.trace[self.stepNo]['outputs'][int(str(ctx.NUMBER()))] = str(ctx.B_OPTION())


    # Enter a parse tree produced by CounterexampleParser#outputs.
    def enterOutputs(self, ctx:CounterexampleParser.OutputsContext):
        self.trace[self.stepNo]['outputs'] = {}


    # Exit a parse tree produced by CounterexampleParser#outputs.
    def exitOutputs(self, ctx:CounterexampleParser.OutputsContext):
        outputs = self.trace[self.stepNo]['outputs']
        outputs = [outputs[k] for k in sorted(list(outputs))]
        outputs = list(takewhile(lambda x: x != "OptionBB", outputs))
        outputs = [just(i) for i in outputs]
        self.trace[self.stepNo]['outputs'] = outputs

        # self.output.write(f"<p>Outputs: {outputs}</p>")


    # Enter a parse tree produced by CounterexampleParser#reg.
    def enterReg(self, ctx:CounterexampleParser.RegContext):
        self.trace[self.stepNo]['regs'][str(ctx.REG())] = str(ctx.B_OPTION())


    def enterRegs(self, ctx:CounterexampleParser.RegsContext):
        self.trace[self.stepNo]['regs'] = {}


    # Exit a parse tree produced by CounterexampleParser#regs.
    def exitRegs(self, ctx:CounterexampleParser.RegsContext):
        regs = self.trace[self.stepNo]['regs']
        regs = [(k, regs[k]) for k in sorted(list(regs))]
        regs = list(takewhile(lambda x: x[1] != "OptionBB", regs))
        regs = [(r.replace("__", ""), just(i)) for r, i in regs]
        self.trace[self.stepNo]['regs'] = regs

        # self.output.write(f"<p>Regs: {regs}</p>")


    # Enter a parse tree produced by CounterexampleParser#t_info.
    def enterT_id(self, ctx:CounterexampleParser.T_infoContext):
        tid = str(ctx.AN_STRING())
        self.trace[self.stepNo]['tid'] = tid
        # self.output.write(f"<p>ID: <strong>{tid}</strong></p>")

    
    # Enter a parse tree produced by CounterexampleParser#cycle.
    def enterCycle(self, ctx:CounterexampleParser.T_infoContext):
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