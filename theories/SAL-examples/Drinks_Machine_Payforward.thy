theory Drinks_Machine_Payforward
  imports "../efsm-isabelle/examples/Drinks_Machine"
begin

definition "setup" :: "transition" where
"setup \<equiv> \<lparr>
        Label = (STR ''setup''),
        Arity = 0,
        Guard = [], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [(2, (L (Num 0)))]
      \<rparr>"

definition "select" :: transition where
"select \<equiv> \<lparr>
        Label = (STR ''select''),
        Arity = 1,
        Guard = [], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [
                    (1, (V (I 1))), \<comment>\<open>  Firstly set value of r1 to value of i1 \<close>
                    (2, (V (R 2)))
                  ]
      \<rparr>"

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], \<comment>\<open> This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear \<close>
        Outputs =  [(V (R 1))], \<comment>\<open> This has one output o1:=r1 where (STR ''r1'') is a variable with a value \<close>
        Updates = [
                    (1, (V (R 1))),
                    (2, Minus (V (R 2)) (L (Num 100)))
                  ]
      \<rparr>"

definition drinks :: transition_matrix where
"drinks \<equiv> {|
             ((0,1), setup),  \<comment>\<open> If we want to go from state 0 to state 1 then select will do that \<close>
             ((1,2), select), \<comment>\<open> If we want to go from state 1 to state 2 then coin will do that \<close>
             ((2,2), coin),   \<comment>\<open> If we want to go from state 2 to state 2 then drinks will do that \<close>
             ((2,1), vend)    \<comment>\<open> If we want to go from state 2 to state 1 then drinks will do that \<close>
         |}"

lemmas transitions = select_def coin_def vend_def setup_def

lemma possible_steps_0: "possible_steps drinks 0 <> (STR ''setup'') [] = {|(1, setup)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1: "possible_steps drinks 1 d (STR ''select'') [Str s] = {|(2, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_coin: "possible_steps drinks 2 d (STR ''coin'') [Num n] = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_vend: "r $ 2 = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks 2 r (STR ''vend'') [] = {|(1, vend)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def connectives value_gt_def)

lemma "observe_trace drinks 0 <> [((STR ''setup''), []), ((STR ''select''), [Str ''coke'']), ((STR ''coin''),[Num 110]), ((STR ''vend''), []), ((STR ''select''), [Str ''pepsi'']), ((STR ''coin''),[Num 90]), ((STR ''vend''), [])] = [[],[],[Some (Num 110)],[Some (Str ''coke'')],[],[Some (Num 100)],[Some (Str ''pepsi'')]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: setup_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1)
    apply (simp add: select_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_2_coin)
    apply (simp add: coin_def apply_outputs select_def setup_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply simp
     apply (rule possible_steps_2_vend)
      apply (simp add: datastate coin_def select_def setup_def value_plus_def)
     apply simp
    apply (simp add: vend_def apply_outputs coin_def select_def setup_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1)
    apply (simp add: select_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_2_coin)
    apply (simp add: coin_def apply_outputs select_def setup_def vend_def value_plus_def value_minus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply simp
     apply (rule possible_steps_2_vend)
      apply (simp add: datastate coin_def select_def setup_def vend_def value_plus_def value_minus_def)
     apply simp
    apply (simp add: vend_def apply_outputs coin_def select_def setup_def)
   apply simp
  by simp
end