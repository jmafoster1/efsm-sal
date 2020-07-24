grammar Counterexample;

/* Parser Rules*/
step_head: 'Step 'NUMBER':\n--- Input Variables (assignments) ---\n';

label: ('label = 'AN_STRING'\n');
cfstate: (('cfstate = State__'NUMBER'\n')|('cfstate = NULL_STATE\n'));

ip: ('i('NUMBER') = 'B_VALUE'\n');
inputs: (ip+);

op: ('o('NUMBER') = 'B_OPTION'\n');
outputs: (op+);

reg: (REG' = 'B_OPTION'\n');
regs: (reg+);

t_id: 'label 'AN_STRING;
t_info: (HYPHENS T_INFO'(module instance at 'CONTEXT'\n  ('t_id'\n    else transition at 'CONTEXT'))\n'HYPHENS)|(HYPHENS T_INFO'(module instance at 'CONTEXT'\n  ('t_id'\n    transition at 'CONTEXT'))\n'HYPHENS);

action: step_head label inputs SYSTEM_VARS cfstate regs outputs;

transition: action t_info?;

cycle: action CYCLE_HEAD (transition)+;

step: transition+ | cycle;

counterexample: HEAD (step+) EOF;

/* Lexer Rules*/
HEAD: 'Counterexample:\n========================\nPath\n========================\n';
CYCLE_HEAD: '========================\nBegin of Cycle\n========================\n';

SYSTEM_VARS: '--- System Variables (assignments) ---\nba-pc!'[0-9]+' = '[0-9]+'\n';

HYPHENS: '------------------------\n';
T_INFO: 'Transition Information:\n';
CONTEXT: '[Context: 'AN_STRING', line('NUMBER'), column('NUMBER')]';

REG: 'r__'[0-9]+;

B_VALUE: ('ValueBB'|('Num('NUMBER')')|('Str('AN_STRING')'));
B_OPTION: ('OptionBB'|('Some('B_VALUE')')|'None');


NUMBER: '-'?[0-9]+;
AN_STRING: [a-zA-Z0-9_]+;
