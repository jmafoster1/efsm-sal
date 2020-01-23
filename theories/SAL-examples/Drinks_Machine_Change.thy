theory Drinks_Machine_Change
  imports "../efsm-isabelle/examples/Drinks_Machine"
begin

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], \<comment>\<open> This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear \<close>
        Outputs =  [(V (R 1)), (Minus (V (R 2)) (L (Num 100)))],
        Updates = [(1, (V (R 1))), (2, (V (R 2)))]
      \<rparr>"

definition drinks :: transition_matrix where
"drinks \<equiv> {|
             ((0,1), select), \<comment>\<open> If we want to go from state 0 to state 1 then select will do that \<close>
             ((1,1), coin),   \<comment>\<open> If we want to go from state 1 to state 1 then coin will do that \<close>
             ((1,2), vend)    \<comment>\<open> If we want to go from state 1 to state 2 then vend will do that \<close>
         |}"

lemmas transitions = select_def coin_def vend_def

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks 0 <> ((STR ''select'')) i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke''])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0)
  by (simp add: transitions)

lemma possible_steps_1_coin: "possible_steps drinks 1 r (STR ''coin'') [Num n'] = {|(1, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1_vend: "r $ 2 = Some (Num n) \<and> n \<ge> 100 \<Longrightarrow> possible_steps drinks 1 r (STR ''vend'') [] = {|(2, vend)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def connectives value_gt_def)

lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] = [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke''), Some (Num 0)]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: select_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_coin)
    apply (simp add: coin_def apply_outputs select_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_coin)
    apply (simp add: coin_def apply_outputs select_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply simp
     apply (rule possible_steps_1_vend)
     apply (simp add: coin_def select_def datastate value_plus_def)
     apply auto[1]
    apply (simp add: vend_def apply_outputs coin_def select_def value_minus_def value_plus_def)
   apply simp
  by simp

lemma "observe_trace drinks 0 <> 
[((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 100]), ((STR ''vend''), [])] =
[[], [Some (Num 50)], [Some (Num 150)], [Some (Str ''coke''), Some (Num 50)]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: select_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_coin)
    apply (simp add: coin_def apply_outputs select_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_coin)
    apply (simp add: coin_def apply_outputs select_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: coin_def select_def join_ir_def input2state_def finfun_update_twist value_plus_def)
     apply (rule possible_steps_1_vend)
     apply (simp add: coin_def select_def datastate)
     apply auto[1]
    apply (simp add: vend_def apply_outputs coin_def select_def value_plus_def value_minus_def)
   apply simp
  by simp

lemma possible_steps_invalid: "l \<noteq> (STR ''coin'') \<and> l \<noteq> (STR ''vend'') \<Longrightarrow> possible_steps drinks 1 d l i = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

(* Stop when we hit a spurious input *)
lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''invalid''), [Num 50])] = [[]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: select_def)
   apply simp
  apply (rule observe_trace_no_possible_step)
  by (simp add: possible_steps_invalid)

lemma invalid_input: "\<not> accepts drinks 1 d' [((STR ''invalid''), [Num 50])]"
  apply safe
  apply (rule EFSM.accepts.cases)
    apply simp
   apply simp
  apply (simp add: step_def)
  using possible_steps_invalid
  by auto

lemma invalid_valid_prefix: "rejects Drinks_Machine_Change.drinks 0 <> [(STR ''select'', [Str ''coke'']), (STR ''invalid'', [Num 50])]"
  apply (rule trace_reject_later)
  apply (simp add: possible_steps_0 select_def)
  apply (rule trace_reject_no_possible_steps)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def apply_guards_def transitions)
  by auto
end
