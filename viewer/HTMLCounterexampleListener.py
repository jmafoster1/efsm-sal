import antlr4
from CounterexampleParser import CounterexampleParser

# This class defines a complete listener for a parse tree produced by CounterexampleParser.
class HTMLCounterexampleListener(antlr4.ParseTreeListener):
    
    def __init__(self, output):
        self.output = output
        self.output.write('<html><head><meta charset="UTF-8"/></head><body>')
        self.output.write('<h1>COUNTEREXAMPLE</h1>')
    
    # Enter a parse tree produced by CounterexampleParser#label.
    def enterLabel(self, ctx:CounterexampleParser.LabelContext):
        self.output.write(f"<p>{ctx.getText().strip()}</p>")


    # Enter a parse tree produced by CounterexampleParser#cfstate.
    def enterCfstate(self, ctx:CounterexampleParser.CfstateContext):
        self.output.write(f"<p>{ctx.getText().strip()}</p>")


    # Enter a parse tree produced by CounterexampleParser#ip.
    def enterIp(self, ctx:CounterexampleParser.IpContext):
        self.output.write(f"<p>{ctx.getText().strip()}</p>")


    # Enter a parse tree produced by CounterexampleParser#inputs.
    def enterInputs(self, ctx:CounterexampleParser.InputsContext):
        self.output.write("<p>")

    # Exit a parse tree produced by CounterexampleParser#inputs.
    def exitInputs(self, ctx:CounterexampleParser.InputsContext):
        self.output.write("</p>")


    # Enter a parse tree produced by CounterexampleParser#op.
    def enterOp(self, ctx:CounterexampleParser.OpContext):
        self.output.write(f"<p>{ctx.getText().strip()}</p>")


    # Enter a parse tree produced by CounterexampleParser#outputs.
    def enterOutputs(self, ctx:CounterexampleParser.OutputsContext):
        self.output.write("<p>")

    # Exit a parse tree produced by CounterexampleParser#outputs.
    def exitOutputs(self, ctx:CounterexampleParser.OutputsContext):
        self.output.write("</p>")


    # Enter a parse tree produced by CounterexampleParser#reg.
    def enterReg(self, ctx:CounterexampleParser.RegContext):
        self.output.write(f"<p>{ctx.getText().strip()}</p>")


    # Enter a parse tree produced by CounterexampleParser#regs.
    def enterRegs(self, ctx:CounterexampleParser.RegsContext):
        self.output.write("<p>")

    # Exit a parse tree produced by CounterexampleParser#regs.
    def exitRegs(self, ctx:CounterexampleParser.RegsContext):
        self.output.write("</p>")


    # Enter a parse tree produced by CounterexampleParser#t_info.
    def enterT_info(self, ctx:CounterexampleParser.T_infoContext):
        text = ctx.getText().replace('\n', '</br>')
        self.output.write(f"<p>{text}</p>")
    
    # Enter a parse tree produced by CounterexampleParser#t_info.
    def enterT_id(self, ctx:CounterexampleParser.T_infoContext):
        self.output.write(f"<strong>{ctx.getText().strip()}</strong>")

    
    # Enter a parse tree produced by CounterexampleParser#cycle.
    def enterCycle(self, ctx:CounterexampleParser.T_infoContext):
        self.output.write("<p><h2>CYCLE</h2>")

    # Enter a parse tree produced by CounterexampleParser#cycle.
    def exitCycle(self, ctx:CounterexampleParser.T_infoContext):
        self.output.write("</p>")


    # Enter a parse tree produced by CounterexampleParser#step.
    def enterStep(self, ctx:CounterexampleParser.StepContext):
        self.output.write("<p>")

    # Exit a parse tree produced by CounterexampleParser#step.
    def exitStep(self, ctx:CounterexampleParser.StepContext):
        self.output.write("</p>")


    # Enter a parse tree produced by CounterexampleParser#counterexample.
    def enterCounterexample(self, ctx:CounterexampleParser.CounterexampleContext):
        self.output.write(f"<p>")

    # Exit a parse tree produced by CounterexampleParser#counterexample.
    def exitCounterexample(self, ctx:CounterexampleParser.CounterexampleContext):
        self.output.write("</p></body></html>")



del CounterexampleParser