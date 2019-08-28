theory In_EFSM_Example
imports EFSM
begin

definition first :: transition where
  "first = \<lparr>Label = STR ''first'', Arity = 1, Guard=[In (I 1) [Num 5, Num 7, Num 9]], Outputs = [], Updates = [(1, V (I 1))]\<rparr>"

definition false :: transition where
  "false = \<lparr>Label = STR ''false'', Arity = 1, Guard=[In (I 1) []], Outputs = [], Updates = []\<rparr>"

definition eq_equiv :: transition where
  "eq_equiv = \<lparr>Label = STR ''eq'', Arity = 1, Guard=[In (R 1) [Num 5]], Outputs = [], Updates = []\<rparr>"

definition in_ex :: transition_matrix where
  "in_ex = {|
  ((0,1), first),
  ((1,2), false),
  ((1,2), eq_equiv)
  |}"

end