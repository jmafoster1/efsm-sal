theory Lift
  imports "../efsm-isabelle/EFSM"
begin

definition t1up :: "transition" where
"t1up \<equiv> \<lparr>
        Label = (STR ''goUp''),
        Arity = 1,
        Guard = [(Gt (V (I 0)) (L (Num 0)))],
        Outputs = [(V (I 0))],
        Updates = []
      \<rparr>"

lemma updates_t1up [simp]:"Updates t1up = []"
  by (simp add: t1up_def)

definition t2up :: "transition" where
"t2up \<equiv> \<lparr>
        Label = (STR ''goUp''),
        Arity = 1,
        Guard = [(Gt (V (I 0)) (L (Num 0)))],
        Outputs = [(Plus (V (I 0)) (L (Num (-1))))],
        Updates = []
      \<rparr>"

lemma updates_t2up [simp]:"Updates t2up = []"
  by (simp add: t2up_def)

definition t3up :: "transition" where
"t3up \<equiv> \<lparr>
        Label = (STR ''goUp''),
        Arity = 1,
        Guard = [(Eq (V (I 0)) (L (Num 0)))],
        Outputs = [(L (Num 0))],
        Updates = []
      \<rparr>"

lemma updates_t3up [simp]:"Updates t3up = []"
  by (simp add: t3up_def)

definition t1down :: "transition" where
"t1down \<equiv> \<lparr>
        Label = (STR ''goDown''),
        Arity = 1,
        Guard = [(Gt (V (I 0)) (L (Num 0)))],
        Outputs = [(V (I 0))],
        Updates = []
      \<rparr>"

definition t2down :: "transition" where
"t2down \<equiv> \<lparr>
        Label = (STR ''goDown''),
        Arity = 1,
        Guard = [(Gt (V (I 0)) (L (Num 0)))],
        Outputs = [((Plus (V (I 0)) (L (Num (-1)))))],
        Updates = []
      \<rparr>"

definition t3down :: "transition" where
"t3down \<equiv> \<lparr>
        Label = (STR ''goDown''),
        Arity = 1,
        Guard = [(Eq (V (I 0)) (L (Num 0)))],
        Outputs = [(L (Num 0))],
        Updates = []
      \<rparr>"

definition openDoors :: transition where
"openDoors \<equiv> \<lparr>
        Label = (STR ''open''),
        Arity = 0,
        Guard = [],
        Outputs = [(L (Num 1))],
        Updates = []
      \<rparr>"

definition closeDoors :: transition where
"closeDoors \<equiv> \<lparr>
        Label = (STR ''close''),
        Arity = 0,
        Guard = [],
        Outputs = [(L (Num 0))],
        Updates = []
      \<rparr>"

lemmas transitions = t1up_def t2up_def t3up_def t1down_def t2down_def t3down_def openDoors_def closeDoors_def

definition lift :: transition_matrix where
"lift \<equiv> {|
              ((0,1), t1up),
              ((1,1), t2up),
              ((1,0), t3up),
              ((0,2), t1down),
              ((2,2), t2down),
              ((2,0), t3down),
              ((0,3), openDoors),
              ((3,0), closeDoors)
         |}"

lemma possible_steps_0: "possible_steps lift 0 r STR ''goUp'' [Num 1] = {|(1, t1up)|}"
  apply (simp add: possible_steps_singleton lift_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def input2state_def)

lemma possible_steps_1_up0: "possible_steps lift 1 <> STR ''goUp'' [Num 0] = {|(0, t3up)|}"
  apply (simp add: possible_steps_singleton lift_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def)

lemma open_doors: "possible_steps lift 0 <> STR ''open'' [] = {|(3, openDoors)|}"
  apply (simp add: possible_steps_singleton lift_def)
  apply safe
  by (simp_all add: transitions apply_guards_def)

lemma "observe_trace lift 0 <> [((STR ''goUp''), [Num 1]), ((STR ''goUp''), [Num 0]), ((STR ''open''), [])] = [[Some (Num 1)], [Some (Num 0)], [Some (Num 1)]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: t1up_def apply_outputs)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_up0)
    apply (simp add: t3up_def apply_outputs)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: open_doors)
    apply (simp add: openDoors_def apply_outputs)
  by auto

end