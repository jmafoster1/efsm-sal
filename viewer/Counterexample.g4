grammar Counterexample;

/* Parser Rules*/

label: ('label = 'AN_STRING'\n');
cfstate: (('cfstate = State__'NUMBER'\n')|('cfstate = NULL_STATE\n'));

b_option: ('OptionBB'|('Some('B_VALUE')')|'None');

ip: ('i('NUMBER') = 'B_VALUE'\n');
inputs: (ip+);

op: ('o('NUMBER') = 'b_option'\n');
outputs: (op+);

reg: (REG' = 'b_option'\n');
regs: (reg+);

t_id: 'label 'AN_STRING;
t_info: (HYPHENS T_INFO'(module instance at 'CONTEXT'\n  ('t_id'\n    else transition at 'CONTEXT'))\n'HYPHENS)|(HYPHENS T_INFO'(module instance at 'CONTEXT'\n  ('t_id'\n    transition at 'CONTEXT'))\n'HYPHENS);

step: STEP_HEAD label inputs SYSTEM_VARS cfstate regs outputs (t_info | cycle | EOF);
cycle: CYCLE_HEAD (step+);

counterexample: HEAD (step+);

/* Lexer Rules*/
HEAD: 'Counterexample:\n========================\nPath\n========================\n';
CYCLE_HEAD: '========================\nBegin of Cycle\n========================\n';

STEP_HEAD: 'Step '[0-9]+':\n--- Input Variables (assignments) ---\n';

SYSTEM_VARS: '--- System Variables (assignments) ---\nba-pc!'[0-9]+' = '[0-9]+'\n';

HYPHENS: '------------------------\n';
T_INFO: 'Transition Information:\n';
CONTEXT: '[Context: 'AN_STRING', line('NUMBER'), column('NUMBER')]';

REG: 'r__'[0-9]+;

B_VALUE: ('ValueBB'|('Num('NUMBER')')|('Str('AN_STRING')'));


NUMBER: '-'?[0-9]+;
AN_STRING: [a-zA-Z0-9_]+;
