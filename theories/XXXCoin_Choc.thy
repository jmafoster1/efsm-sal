theory XXXCoin_Choc
imports "/home/michael/Documents/efsm-inference/formal/EFSM/EFSM"
begin

definition "init" :: "transition" where
"init \<equiv> \<lparr>
      Label = STR ''init'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (L (Num 0)))
      ]
\<rparr>"

definition "coin" :: "transition" where
"coin \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, Plus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "vend" :: "transition" where
"vend \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            Gt (V (R 1)) (L (Num 0))
      ],
      Outputs = [],
      Updates = [
            (1, Minus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "graph1" :: "transition_matrix" where
"graph1 \<equiv> {|
      ((0, 1), init),
      ((1, 1), coin),
      ((1, 2), vend)
|}"

definition "init1" :: "transition" where
"init1 \<equiv> \<lparr>
      Label = STR ''init'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (L (Num 0)))
      ]
\<rparr>"

definition "coin1" :: "transition" where
"coin1 \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, Plus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "coin2" :: "transition" where
"coin2 \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, Plus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "vend1" :: "transition" where
"vend1 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            Gt (V (R 1)) (L (Num 0))
      ],
      Outputs = [],
      Updates = [
            (1, Minus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "graph2" :: "transition_matrix" where
"graph2 \<equiv> {|
      ((0, 1), init1),
      ((1, 2), coin1),
      ((2, 2), coin2),
      ((2, 3), vend1)
|}"

lemmas transitions = init1_def coin1_def coin2_def vend1_def init_def coin_def vend_def

lemma possible_steps_graph1_init: "possible_steps graph1 0 <> STR ''init'' [] = {|(1, init)|}"
  apply (simp add: possible_steps_alt graph1_def Abs_ffilter Set.filter_def transitions)
  by auto

lemma accepts_trace_tail: "accepts_trace graph1 ((STR ''init'', []) # t) = accepts graph1 1 (<>(1 := Num 0)) t"
  apply (simp add: accepts_prim Let_def)
  by (simp add: possible_steps_graph1_init init_def)

lemma accepts_1_1: "accepts graph1 1 (<>(1 := Num 0)) t \<Longrightarrow> accepts graph2 1 (<>(1 := Num 0)) t"
  sorry

theorem Chocolate_Equivilence : "accepts_trace graph1 t \<Longrightarrow> accepts_trace graph2 t"
proof(induct t)
  case Nil
then show ?case     
  by (simp add: accepts.base)
next
case (Cons a t)
  then show ?case
    apply (case_tac "a = (STR ''init'', [])")
     defer
    \<comment> \<open>Deal with the case where first input is not "init" first as this is shorter\<close>
    apply (rule notE[of "accepts_trace graph1 (a # t)" "accepts_trace graph2 (a # t)"])
      apply (rule trace_reject_no_possible_steps_atomic[of graph1 0 "<>" a t])
      apply (simp add: possible_steps_def Abs_ffilter Set.filter_def graph1_def transitions)
      apply (metis length_0_conv less_numeral_extra(1) prod.collapse select_convs(1) select_convs(2))
     apply simp
     \<comment> \<open>Deal with the case where first input is "init"\<close>
     apply (rule accepts_single_possible_step_atomic[of graph2 0 "<>" a 1 init1 t])
      apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def graph2_def transitions)
      apply auto[1]
    apply (simp add: init1_def accepts_trace_tail)
    by (simp add: accepts_1_1)
qed
  

end
