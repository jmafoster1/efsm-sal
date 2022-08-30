theory Coin_Tea
  imports "Extended_Finite_State_Machines.EFSM_LTL"
begin

declare One_nat_def [simp del]
declare value_gt_def [simp]

text_raw\<open>\snip{cointea}{1}{2}{%\<close>
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
          Guards = [Gt (V (R 1)) (L (value.Int 0))],
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

lemma implode_init: "String.implode ''init'' = STR ''init''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma possible_steps_init: "possible_steps drinks 0 r STR ''init'' [] = {|(1, init)|}"
    apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks_def)
    apply safe
  by (simp_all add: init_def)

lemma possible_steps_not_init: "\<not> (a = STR ''init'' \<and> b = []) \<Longrightarrow> possible_steps drinks 0 r a b = {||}"
    apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
    apply clarify
  by (simp add: init_def)

lemma ltl_step_none_not_init:"t \<noteq> (STR ''init'', []) \<Longrightarrow> possible_steps drinks 0 r (fst t) (snd t) = {||}"
  apply (simp add: possible_steps_def ffilter_def Set.filter_def drinks_def fset_both_sides Abs_fset_inverse)
  by (metis init_def length_0_conv less_numeral_extra(1) prod.collapse transition.ext_inject transition.surjective)

lemma step_not_init: "t \<noteq> (STR ''init'', []) \<Longrightarrow> ltl_step drinks (Some 0) r t = (None, [], r)"
  using ltl_step_none_not_init ltl_step_none
  by (simp add: ltl_step_none_2)

lemma possible_steps_coin: "possible_steps drinks 1 r STR ''coin'' [] = {|(1, coin)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def)

lemma possible_steps_vend_insufficient: "n \<le> 0 \<Longrightarrow> possible_steps drinks 1 <1 $r:= Some (value.Int n)> STR ''vend'' [] = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def apply_guards_def join_ir_def)

lemma possible_steps_vend_sufficient: "n > 0 \<Longrightarrow> possible_steps drinks 1 <1 $r:= Some (value.Int n)> STR ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def apply_guards_def join_ir_def)

lemma possible_steps_vend: "possible_steps drinks 1 r STR ''vend'' [] |\<subseteq>| {|(2, vend)|}"
  by (simp add: possible_steps_def drinks_def ffilter_finsert transitions)

lemma invalid_possible_steps_1:
  "(l, i) \<noteq> (STR ''coin'', []) \<Longrightarrow>
   (l, i) \<noteq> (STR ''vend'', []) \<Longrightarrow>
   possible_steps drinks 1 r l i = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  by (metis coin_def length_0_conv transition.ext_inject transition.surjective vend_def)

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

lemma state_eq_alt: "alw (state_eq s) s' = alw (\<lambda>x. shd x = s) (smap (\<lambda>x. statename x) s')"
  apply standard
  apply (simp add: alw_iff_sdrop)
  by (simp add: alw_mono alw_smap)

lemma S_drinks: "S drinks = {|0, 1, 2|}"
  apply (simp add: S_def drinks_def)
  by auto

lemma "ltl_apply (alw (nxt (state_eq (Some 2)) impl (label_eq ''vend''))) drinks"
  apply (rule ltl_apply_S)
  apply (rule valid_trace.cases)
     apply simp
     apply (simp add: possible_steps_invalid_state)
    apply (rule alw_mono[of "nxt(state_eq None)"])
     apply (simp add:valid_trace_None(1) nxt_alw)
    apply simp
    apply (rule alw_mono[of "nxt(state_eq None)"])
    apply (metis alw_nxt nxt_alw valid_trace_None(1))
   apply simp
  apply (simp add: S_drinks)
  subgoal for s r t
  apply (coinduction arbitrary: s r t)
  apply (simp add: implode_vend)
  apply (erule disjE)
   apply (rule valid_trace.cases)
      apply simp
     apply clarsimp
  subgoal for r l i t p s' tr
    apply (case_tac "(l, i) = (STR ''init'', [])")
     apply (simp add: possible_steps_init)
     apply force
    by (simp add: possible_steps_not_init)
    apply clarsimp
    apply standard
     apply (metis shd_state_is_none state_eq_None_not_Some valid_trace_smap_action_None)
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
     apply (metis alw_nxt nxt_alw valid_trace_None(1))
    apply simp
   apply simp
  apply (erule disjE)
   apply (rule valid_trace.cases)
      apply simp
     apply clarsimp
  subgoal for r l i ta p s' tr
    apply (case_tac "(l, i) = (STR ''coin'', [])")
     apply (simp add: possible_steps_coin)
     apply force
    apply (case_tac "(l, i) = (STR ''vend'', [])")
    using possible_steps_vend apply fastforce
    by (simp add: invalid_possible_steps_1)
    apply clarsimp
    apply standard
     apply (metis option.distinct(1) shd_state_is_none valid_trace_smap_action_None)
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
     apply (metis alw_nxt nxt_alw valid_trace_None(1))
    apply simp
   apply simp
  apply (rule valid_trace.cases)
     apply simp
    apply clarsimp
    apply (simp add: drinks_def possible_steps_def ffilter_finsert)
   apply standard
    apply (metis option.distinct(1) shd_state_is_none stream.sel(2) valid_trace_smap_action_None)
   apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
    apply (metis alw_nxt nxt_alw stream.sel(2) valid_trace_None(1))
  by auto
  done

lemma updates_vend: "apply_updates (Updates vend) i r = r"
  by (simp add: vend_def apply_updates_def)

lemma less_than_zero_not_nxt_2:
  "n \<le> 0 \<Longrightarrow>
   statename (shd (stl (make_full_observation drinks (Some 1) <1 $r:= Some (value.Int n)> p t))) \<noteq> Some 2"
  apply (case_tac "shd t = (STR ''coin'', [])")
   apply (simp add: possible_steps_coin)
  apply (case_tac "shd t = (STR ''vend'', [])")
   apply (simp add: possible_steps_vend_insufficient)
  by (simp add: invalid_possible_steps_1 ltl_step_none_2)

lemma possible_steps_2: "possible_steps drinks 2 r (fst (shd t)) (snd (shd t)) = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)

lemma shd_not_lt_zero: "0 \<le> n \<Longrightarrow> (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $r 1) (Some (value.Int 0)) \<noteq> trilean.true) (make_full_observation drinks None <1 $r:= Some (value.Int n)> p t)"
  by simp

lemma nxt_not_lt_zero: "0 \<le> n \<Longrightarrow> nxt (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $r 1) (Some (value.Int 0)) \<noteq> trilean.true) (make_full_observation drinks None <1 $r:= Some (value.Int n)> p t)"
  by simp

lemma once_none_remains_not_lt_zero: "0 \<le> n \<Longrightarrow> alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $r 1) (Some (value.Int 0)) \<noteq> trilean.true) (make_full_observation drinks None <1 $r:= Some (value.Int n)> p t)"
  using no_updates_none
  by (simp add: alw_iff_sdrop)

lemma once_none_null_remains_not_lt_zero: "alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $r 1) (Some (value.Int 0)) \<noteq> trilean.true) (make_full_observation drinks None <> p t)"
  using no_updates_none
  by (simp add: alw_iff_sdrop)

lemma stop_at_2: "0 \<le> n \<Longrightarrow>
      alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $r 1) (Some (value.Int 0)) \<noteq> trilean.true) (make_full_observation drinks (Some 2) <1 $r:= Some (value.Int n)> p t)"
proof(coinduction)
  case alw
  then show ?case
    using ltl_step_alt once_none_remains_not_lt_zero possible_steps_2 by auto
qed

lemma next_not_lt_zero:
  "n \<ge> 0 \<Longrightarrow>
   (nxt (not
    (check_exp (Lt (V (Rg 1)) (L (value.Int 0))))
    )) (make_full_observation drinks (Some 1) <1 $r:= Some (value.Int n)> p t)"
    apply simp
    apply (case_tac "shd t = (STR ''vend'', [])")
    apply (case_tac "n = 0")
      apply (simp add: possible_steps_vend_insufficient Lt_def join_iro_def)
     apply (simp add: possible_steps_vend_sufficient updates_vend Lt_def join_iro_def)
    apply (case_tac "shd t = (STR ''coin'', [])")
   apply (simp add: possible_steps_coin datastate coin_def value_plus_def Lt_def join_iro_def apply_updates_def)
  by (simp add: Lt_def invalid_possible_steps_1 ltl_step_alt join_iro_def)

lemma not_initialised: "alw (\<lambda>xs. state_eq (Some 1) xs \<and>
              MaybeBoolInt (<) (datastate (shd xs) $r (1)) (Some (value.Int 0)) = trilean.true \<and> label_eq ''vend'' xs \<and> input_eq [] xs \<longrightarrow>
              state_eq (Some 2) (stl xs))
     (make_full_observation drinks None <> p t)"
  using once_none_always_none state_eq_None_not_Some
  by (simp add: alw_iff_sdrop)

lemma not_init: "ltl_apply (not (action_eq (''init'', []))) drinks \<Longrightarrow>
    ltl_apply (label_eq ''init'') drinks \<Longrightarrow> \<not> ltl_apply (input_eq []) drinks"
  apply (simp add: implode_init ltl_apply_def)
  using valid_trace_Some by blast

lemma step_0_vend: "fst e = STR ''vend'' \<Longrightarrow> ltl_step drinks (Some 0) r e = (None, [], r)"
  apply (rule ltl_step_none_2)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
  apply (simp add: init_def)
  by auto

lemma LTL_label_vend_not_2: "ltl_apply ((label_eq ''vend'') impl (not (ev (state_eq (Some 2))))) drinks"
  apply (rule ltl_apply)
  apply (simp add: not_ev_iff implode_vend)
  apply (rule valid_trace.cases)
     apply simp
  using possible_steps_not_init apply force
   apply clarsimp
   apply (rule alw)
    apply simp
  using valid_trace_None(1) alw_mono apply fastforce
  by simp

lemma possible_steps_0: "possible_steps drinks 0 <> l i = finsert x S' \<Longrightarrow> finsert x S' = {|(1, init)|}"
  apply (case_tac "l = STR ''init''")
   apply (case_tac "i = []")
    apply (simp add: possible_steps_init)
  using possible_steps_not_init
  by auto

lemma vend_insufficient: "possible_steps drinks 1 <1 $r:= Some (value.Int 0)> STR ''vend'' i = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
   apply (simp add: coin_def)
  by (simp add: vend_def apply_guards_def join_ir_def)

lemma updates_init: "apply_updates (Updates init) (\<lambda>x. None) <> = <1 $r:= Some (value.Int 0)>"
  by (simp add: init_def apply_updates_def)

lemma LTL_aux2: "ltl_apply ((nxt (label_eq ''vend'')) impl not (ev (state_eq (Some 2)))) drinks"
  apply (rule ltl_apply)
  apply (simp add: not_ev_iff implode_vend)
  apply (rule valid_trace.cases)
     apply simp
    apply clarsimp
  subgoal for l i ta p s' tr
    apply (case_tac "(l, i) = (STR ''init'', [])")
     prefer 2
     apply (simp add: possible_steps_not_init)
     apply (simp add: possible_steps_init init_def apply_updates_def)
     apply (rule alw, simp)
     apply (simp add: eq_commute[of "Some 1"] eq_commute[of "<1 $r:= Some (value.Int 0)>"])
    apply (rule valid_trace.cases[of drinks "Some 1"])
       apply simp
      apply clarsimp
      apply (rule alw, simp)
      apply (simp add: vend_insufficient)
     apply clarsimp
     apply (rule alw, simp)
     apply simp
    using valid_trace_None(1) alw_mono apply fastforce
    by simp
   apply clarsimp
   apply (rule alw, simp)
   apply simp
  using valid_trace_None(1) alw_mono apply fastforce
  by simp

text_raw\<open>\snip{checkinit}{1}{2}{%\<close>
lemma LTL_init_makes_r_1_zero:
  "ltl_apply ((label_eq ''init'' aand input_eq []) impl
    (nxt (check_exp (Eq (V (Rg 1)) (L (value.Int 0))))))
   drinks"
text_raw\<open>}%endsnip\<close>
  apply (rule ltl_apply)
  apply (rule valid_trace.cases)
   apply simp
  apply clarsimp
  apply (simp add: implode_init possible_steps_init init_def apply_updates_def)
  using implode_init possible_steps_init apply force
  by simp


(* This is not a true property but is good for testing the translation process *)
lemma LTL_must_pay_wrong: "ltl_apply ((not (label_eq ''vend'' suntil label_eq ''coin'')) suntil state_eq None) drinks"
  oops

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

lemma vend_gets_stuck: "stl t = (STR ''vend'', []) ## x2 \<Longrightarrow> \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) <1 $r:= Some (value.Int 0)> p ((STR ''vend'', []) ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: vend_insufficient alw_not_some)
qed

lemma possible_steps_1_invalid: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
       x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
       possible_steps drinks 1 <1 $r:= Some (value.Int 0)> (fst x1) (snd x1) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  apply safe
   apply (simp add: coin_def)
   apply (metis prod.collapse)
  by (simp add: vend_def apply_guards_def join_ir_def)

lemma invalid_gets_stuck: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
                           x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
                           \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) <1 $r:= Some (value.Int 0)> p (x1 ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: possible_steps_1_invalid alw_not_some ltl_step_alt)
qed

lemma in_possible_steps_0: "(a, b) |\<in>| possible_steps drinks 0 <> l i \<Longrightarrow> a = 1 \<and> b = init \<and> l = STR ''init'' \<and> i = []"
  apply (simp add: possible_steps_def drinks_def ffilter_finsert init_def)
  apply (case_tac "(l, i) = (STR ''init'', [])")
  by auto

lemma in_possible_steps_1_r1_0: "(a, b) |\<in>| possible_steps drinks 1 <1 $r:= Some (value.Int 0)> l i \<Longrightarrow> a=1 \<and> b=coin \<and> l=STR ''coin'' \<and> i = []"
  apply (simp add: possible_steps_def drinks_def ffilter_finsert transitions)
  apply (case_tac "(l, i) = (STR ''coin'', [])")
  by auto

lemma LTL_vend_no_coin: "ltl_apply ((nxt (label_eq ''vend'' aand input_eq [])) impl not (ev (state_eq (Some 2)))) drinks"
  apply (simp add: not_ev_iff)
  apply (rule ltl_apply)
  apply (rule valid_trace.cases)
     apply simp
    apply clarsimp
  subgoal for l i ta p s' t
    apply (insert in_possible_steps_0[of s' t l i])
    apply (rule alw)
     apply simp
    apply (simp add: eq_commute[of "Some 1"])
    apply (rule valid_trace.cases[of drinks "Some 1"])
       apply simp
      apply (simp add: implode_vend possible_steps_vend_insufficient init_def apply_updates_def)
     apply (rule alw)
      apply simp
    using alw_mono valid_trace_None(1) apply fastforce
    by simp
   apply clarsimp
   apply (rule alw, simp)
   apply simp
    using alw_mono valid_trace_None(1) apply fastforce
  by simp

lemma LTL_invalid_gets_stuck_2:
  "ltl_apply (((nxt (not (label_eq ''coin'' aand input_eq []))) aand
   (nxt (not (label_eq ''vend'' aand input_eq [])))) impl
   (not (ev (state_eq (Some 2))))) drinks"
  apply (simp add: not_ev_iff)
  apply (rule ltl_apply)
  apply (rule valid_trace.cases)
     apply simp
    apply clarsimp
  subgoal for l i ta p s' tr
    apply (insert in_possible_steps_0[of s' tr l i], simp)
    apply (rule alw, simp)
    apply simp
    apply (rule valid_trace.cases[of drinks "Some 1"])
       apply simp
      apply clarsimp
      apply (simp add: implode_vend implode_coin invalid_possible_steps_1)
     apply (rule alw, simp)
     apply simp
    using alw_mono valid_trace_None(1) apply fastforce
    by simp
   apply clarsimp
   apply (rule alw, simp)
  using alw_mono valid_trace_None(1) apply fastforce
  by simp

lemma valid_trace_prefix_if_ev_2:
    "valid_trace drinks (Some 0) <> t \<Longrightarrow>
       ev (state_eq (Some 2)) t \<Longrightarrow>
       \<exists>p t'. t = (
        \<lparr>statename = Some 0, datastate = <>, action = (STR ''init'', []), output = p\<rparr> ##
        \<lparr>statename = Some 1, datastate = <1 $r:= Some (value.Int 0)>, action = (STR ''coin'', []), output = []\<rparr> ## t'
      )"
  apply (rule_tac x="output (shd t)" in exI)
  apply (rule_tac x="stl (stl t)" in exI)
  apply (rule_tac valid_trace.cases)
     apply simp
    apply clarsimp
  subgoal for l i ta p s' tr
    apply (insert in_possible_steps_0[of s' tr l i])
    apply (simp add: init_def apply_updates_def)
    apply (rule_tac valid_trace.cases[of drinks "Some 1"])
       apply simp
      apply clarsimp
    subgoal for la ia tb a b
      apply (insert in_possible_steps_1_r1_0 [of a b la ia])
      by simp
     apply clarsimp
     apply (simp add: possible_steps_init)
    subgoal for la ia tb
      apply (simp add: ev_Stream)
      using valid_trace_None(1)[of drinks _ tb] not_ev_iff[of "state_eq (Some 2)" tb] alw_mono[of "state_eq None" tb]
      by simp
    by simp
   apply clarsimp
  subgoal for l i ta p
    using valid_trace_None(1)[of drinks _ ta] not_ev_iff[of "state_eq (Some 2)" ta] alw_mono[of "state_eq None" ta]
    by (simp add: ev_Stream)
  by simp

(* Ramsay, this is the proof you want!
   I'll convert it to an Isabelle code snippet for the actual paper to make it really pretty but for
   now, just use a screenshot image or something... *)
text_raw\<open>\snip{mustpaycorrect}{1}{2}{%\<close>
lemma LTL_must_pay_correct:
  "ltl_apply ((ev (state_eq (Some 2))) impl
    (not (label_eq ''vend'') suntil label_eq ''coin''))
   drinks"
  apply (rule ltl_apply)
  apply (simp add: implode_vend implode_coin)
  apply clarsimp
  subgoal for t
    apply (insert valid_trace_prefix_if_ev_2[of t])
    apply clarsimp
    by (simp add: suntil_Stream)
  done
text_raw\<open>}%endsnip\<close>

(* This should translate the same as LTL_must_pay_correct *)
lemma LTL_must_pay_correct_bracketed:
  "ltl_apply ((ev (state_eq (Some 2))) impl
    ((not (label_eq ''vend'')) suntil label_eq ''coin''))
   drinks"
  using LTL_must_pay_correct by blast

text_raw\<open>\snip{mustpaycorrectfull}{1}{2}{%\<close>
lemma LTL_must_pay_correct_full:
  "ltl_apply (ev (\<lambda>s. statename (shd s) = Some 2) impl
   ((\<lambda>xs. fst (action (shd xs)) \<noteq> STR ''vend'') suntil
    (\<lambda>xs. fst (action (shd xs)) = STR ''coin'')))
   drinks"
  text_raw\<open>}%endsnip\<close>
  using LTL_must_pay_correct
  using implode_coin implode_vend by auto

end
