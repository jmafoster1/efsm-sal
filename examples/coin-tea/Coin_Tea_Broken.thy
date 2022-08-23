theory Coin_Tea_Broken
  imports "Extended_Finite_State_Machines.EFSM_LTL"
begin

declare One_nat_def [simp del]
declare ltl_step_alt [simp]

text_raw\<open>\snip{cointeabroken}{1}{2}{%\<close>
definition init :: transition where
"init \<equiv> \<lparr>
          Label = (STR ''init''),
          Arity = 0,
          Guards = [],
          Outputs = [],
          Updates = [(1, (L (value.Int 0)))]
        \<rparr>"

definition coin :: transition where
"coin \<equiv> \<lparr>
          Label = (STR ''coin''),
          Arity = 0,
          Guards = [],
          Outputs = [],
          Updates = [(1, (Plus (V (R 1)) (L (value.Int 1))))]
        \<rparr>"

definition vend :: transition where
"vend \<equiv> \<lparr>
          Label = (STR ''vend''),
          Arity = 0,
          Guards = [Ge (V (R 1)) (L (value.Int 0))],
          Outputs = [L (Str ''tea'')],
          Updates = []
        \<rparr>"

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
            ((0,1), init),
            ((1,1), coin),
            ((1,2), vend)
          |}"
text_raw\<open>}%endsnip\<close>

lemmas transitions = select_def
      init_def
      coin_def
      vend_def

lemma possible_steps_init: "possible_steps drinks 0 <> STR ''init'' [] = {|(1, init)|}"
    apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks_def)
    apply safe
  by (simp_all add: init_def)

lemma possible_steps_not_init: "\<not> (a = STR ''init'' \<and> b = []) \<Longrightarrow> possible_steps drinks 0 <> a b = {||}"
    apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
    apply clarify
    by (simp add: init_def)

lemma aux1: "\<not> state_eq (Some 2)
        (make_full_observation drinks (fst (ltl_step drinks (Some 0) <> (shd t)))
          (snd (snd (ltl_step drinks (Some 0) <> (shd t)))) p (stl t))"
proof-
  show ?thesis
    apply (case_tac "shd t")
    apply simp
    apply (case_tac "a = STR ''init'' \<and> b = []")
     apply (simp add: possible_steps_init)
    by (simp add: possible_steps_not_init)
qed

lemma make_full_obs_neq: "make_full_observation drinks (fst (ltl_step drinks (Some 0) <> (shd t))) (snd (snd (ltl_step drinks (Some 0) <> (shd t))))
     p (stl t) \<noteq>
    make_full_observation drinks (Some 0) <> p t"
  apply (case_tac "ltl_step drinks (Some 0) <> (shd t)")
  apply (case_tac "shd t")
    apply simp
    apply (case_tac "aa = STR ''init'' \<and> ba = []")
   apply (simp add: possible_steps_init init_def)
  apply (metis (no_types, lifting) make_full_observation.simps(1) option.inject state.ext_inject zero_neq_one)
  apply (simp add: possible_steps_not_init)
  by (metis make_full_observation.simps(1) option.simps(3) state.ext_inject)

lemma ltl_step_none_not_init:"t \<noteq> (STR ''init'', []) \<Longrightarrow> possible_steps drinks 0 r (fst t) (snd t) = {||}"
  apply (simp add: possible_steps_def ffilter_def Set.filter_def drinks_def fset_both_sides Abs_fset_inverse)
  by (metis init_def length_0_conv less_numeral_extra(1) prod.collapse transition.ext_inject transition.surjective)

lemma step_not_init: "t \<noteq> (STR ''init'', []) \<Longrightarrow> ltl_step drinks (Some 0) r t = (None, [], r)"
  using ltl_step_none_not_init ltl_step_none
  by simp

lemma possible_steps_coin: "possible_steps drinks 1 r STR ''coin'' [] = {|(1, coin)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def)

lemma possible_steps_vend_sufficient: "n \<ge> 0 \<Longrightarrow> possible_steps drinks 1 <1 $r:= Some (value.Int n)> STR ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def apply_guards_def join_ir_def value_gt_def connectives)

lemma invalid_possible_steps_1: "shd t \<noteq> (STR ''coin'', []) \<Longrightarrow>
    shd t \<noteq> (STR ''vend'', []) \<Longrightarrow> possible_steps drinks 1 r (fst (shd t)) (snd (shd t)) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  by (metis coin_def length_0_conv prod.collapse transition.ext_inject transition.surjective vend_def)

lemma possible_steps_2: "possible_steps drinks 2 r l i = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)

lemma implode_init: "String.implode ''init'' = STR ''init''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma LTL_label_vend_not_2: "ltl_apply ((label_eq ''vend'') impl (not (ev (state_eq (Some 2))))) drinks"
  apply (rule ltl_apply)
  apply (rule valid_trace.cases)
     apply simp
    apply (simp add: implode_vend)
    apply (rule impI)
    apply (simp add: possible_steps_not_init)
   apply (rule impI)
   apply (simp add: not_ev_iff implode_vend)
   apply (rule alw)
    apply simp
   apply simp
  using valid_trace_None(1) alw_mono apply fastforce
  by simp

lemma possible_steps_0: "possible_steps drinks 0 <> l i = finsert x S' \<Longrightarrow> finsert x S' = {|(1, init)|}"
  apply (case_tac "l = STR ''init''")
   apply (case_tac "i = []")
    apply (simp add: possible_steps_init)
  using possible_steps_not_init
  by auto

lemma apply_updates_init: "apply_updates (Updates init) (\<lambda>x. None) <> = <1 $r:= Some (value.Int 0)>"
  by (simp add: init_def apply_updates_def)

(* This is supposed to break *)
lemma vend_insufficient: "possible_steps drinks 1 <1 $r:= Some (value.Int 0)> STR ''vend'' i = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
   apply (simp add: coin_def)
  apply (simp add: vend_def apply_guards_def connectives value_gt_def)
  oops

lemma LTL_init_makes_r_1_zero: "ltl_apply ((label_eq ''init'' aand input_eq []) impl nxt (check_exp (Eq (V (Rg 1)) (L (value.Int 0))))) drinks"
  apply (rule ltl_apply)
  apply (rule valid_trace.cases)
     apply simp
    apply clarsimp
    apply (simp add: implode_init possible_steps_init init_def apply_updates_def)
    apply (metis update_value value_eq_true)
   apply clarsimp
   apply (simp add: implode_init possible_steps_init)
  by simp

lemma shd_not_init: "shd t \<noteq> (STR ''init'', []) \<Longrightarrow> \<not> ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 0) <> p t)"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd t")
    apply simp
    by (simp add: possible_steps_not_init alw_not_some)
qed

lemma possible_steps_1_invalid:
  "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
   x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
   possible_steps drinks 1 <1 $r:= Some (value.Int 0)> (fst x1) (snd x1) = {||}"
  apply (simp add: possible_steps_empty drinks_def)
  apply safe
   apply (simp add: coin_def can_take)
   apply (metis prod.collapse)
  apply (simp add: vend_def apply_guards_def can_take)
  by (metis prod.collapse)

lemma invalid_gets_stuck: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
                           x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
                           \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) <1 $r:= Some (value.Int 0)> p (x1 ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: possible_steps_1_invalid alw_not_some)
qed

lemma implode_tea: "String.implode ''tea'' = STR ''tea''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma LTL_vend_no_coin: "ltl_apply ((nxt (label_eq ''vend'' aand input_eq [])) impl not (ev (state_eq (Some 2)))) drinks"
  apply (rule ltl_apply)
  apply (rule valid_trace.cases)
     apply simp
    apply simp
    apply (simp add: implode_vend not_ev_iff)
    apply clarsimp
    apply (case_tac "(l, i) = (STR ''init'', [])")
     apply (simp add: possible_steps_init init_def apply_updates_def)
     apply (thin_tac "valid_trace drinks (Some 0) <> (\<lparr>statename = Some 0, datastate = <>, action = (STR ''init'', []), output = p\<rparr> ## ta)")
     apply (rule alw)
     apply (rule valid_trace.cases)
         apply simp+
     apply (rule alw)
      apply (rule valid_trace.cases)
         apply simp+
     apply (rule alw)
      apply (rule valid_trace.cases)
         apply simp+
        apply (simp add: eq_commute possible_steps_vend_sufficient apply_outputs_def vend_def Str_def implode_tea)
        apply clarsimp
  oops (* Contradictory proof state reached since there always exists a valid trace from any state*)

lemma possible_steps_init_l_i: "(a, b) |\<in>| possible_steps drinks 0 <> l i \<Longrightarrow> l = STR ''init'' \<and> i = []"
  apply (simp add: possible_steps_def drinks_def ffilter_finsert transitions)
  apply (case_tac "l = STR ''init'' \<and> i = []")
  by auto

lemma LTL_invalid_gets_stuck_2:
  "ltl_apply (((nxt (not (label_eq ''coin'' aand input_eq []))) aand
   (nxt (not (label_eq ''vend'' aand input_eq [])))) impl
   (not (ev (state_eq (Some 2))))) drinks"
  apply (rule ltl_apply)
  apply (simp add: not_ev_iff implode_coin implode_vend)
  apply (rule valid_trace.cases)
     apply simp
    apply clarsimp
  subgoal for l i t p s' tr
    apply (insert possible_steps_init_l_i[of s' tr l i])
    apply (simp add: possible_steps_init init_def apply_updates_def)
    apply (rule alw)
     apply simp
    apply (simp add: eq_commute[of "<1 $r:= Some (value.Int 0)>"] eq_commute[of "Some 1"])
    apply clarsimp
    apply (simp add: valid_trace.simps[of drinks "Some 0"] possible_steps_init init_def apply_updates_def)
    apply (rule valid_trace.cases)
       apply simp
    using possible_steps_1_invalid apply force
     apply clarsimp
     apply (rule alw)
      apply simp
     apply (rule alw_mono[of "state_eq None"])
      apply (simp add: valid_trace_None)
     apply simp
    by simp
   apply clarsimp
   apply (rule alw)
    apply simp
   apply (rule alw_mono[of "state_eq None"])
    apply (simp add: valid_trace_None)
   apply simp
  by simp

(* Ramsay, this is the proof you want!
   I'll convert it to an Isabelle code snippet for the actual paper to make it really pretty but for
   now, just use a screenshot image or something... *)
lemma LTL_must_pay_correct: "ltl_apply ((ev (state_eq (Some 2))) impl (not (label_eq ''vend'') suntil label_eq ''coin'')) drinks"
  (* We can't do a vend immediately after doing init because this breaks it, but there's nothing
     actually stopping us from doing this! *)
  oops

lemma LTL_must_pay_correct_bracketed:
  "ltl_apply ((ev (state_eq (Some 2))) impl
    ((not (label_eq ''vend'')) suntil label_eq ''coin''))
   drinks"
  oops

lemma
"(((ev (state_eq (Some 2))) impl (not (label_eq ''vend'') suntil label_eq ''coin''))) =
 (((ev (state_eq (Some 2))) impl ((not (label_eq ''vend'')) suntil label_eq ''coin'')))"
  by simp

end
