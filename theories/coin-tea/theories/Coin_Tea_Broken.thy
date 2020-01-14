theory Coin_Tea_Broken
  imports "../../efsm-ltl/EFSM_LTL"
begin

declare One_nat_def [simp del]
declare ltl_step_alt [simp]

definition I :: "nat \<Rightarrow> vname" where
  "I n = vname.I (n-1)"
declare I_def [simp]

text_raw\<open>\snip{cointeabroken}{1}{2}{%\<close>
definition init :: transition where
"init \<equiv> \<lparr>
          Label = (STR ''init''),
          Arity = 0,
          Guard = [],
          Outputs = [],
          Updates = [(1, (aexp.L (Num 0)))]
        \<rparr>"

definition coin :: transition where
"coin \<equiv> \<lparr>
          Label = (STR ''coin''),
          Arity = 0,
          Guard = [],
          Outputs = [],
          Updates = [(1, (aexp.Plus (aexp.V (vname.R 1)) (aexp.L (Num 1))))]
        \<rparr>"

definition vend :: transition where
"vend \<equiv> \<lparr>
          Label = (STR ''vend''),
          Arity = 0,
          Guard = [Ge (aexp.V (vname.R 1)) (aexp.L (Num 0))],
          Outputs = [aexp.L (Str ''tea'')],
          Updates = []
        \<rparr>"

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
            ((0,1), init),
            ((1,1), coin),
            ((1,2), vend)
          |}"
text_raw\<open>}%endsnip\<close>

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
     apply (simp add: possible_steps_init state_eq_def)
    by (simp add: state_eq_def possible_steps_not_init)
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
  apply (simp add: state_eq_def alw_iff_sdrop)
  by (simp add: state_eq_def alw_mono alw_smap)

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

lemma possible_steps_vend_sufficient: "n > 0 \<Longrightarrow> possible_steps drinks 1 (<>(1 := Num n)) STR ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def apply_guards_def join_ir_def value_gt_def connectives)

lemma invalid_possible_steps_1: "shd t \<noteq> (STR ''coin'', []) \<Longrightarrow>
    shd t \<noteq> (STR ''vend'', []) \<Longrightarrow> possible_steps drinks 1 r (fst (shd t)) (snd (shd t)) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  by (metis coin_def length_0_conv prod.collapse transition.ext_inject transition.surjective vend_def)

lemma possible_steps_2: "possible_steps drinks 2 r (fst (shd t)) (snd (shd t)) = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)

lemma implode_init: "String.implode ''init'' = STR ''init''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma not_init: "shd t \<noteq> (STR ''init'', []) \<Longrightarrow>
    label_eq ''init'' (watch drinks t) \<Longrightarrow> \<not> input_eq [] (watch drinks t)"
  apply (simp add: label_eq_def input_eq_def implode_init watch_def)
  by (metis prod.collapse)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma LTL_label_vend_not_2: "((label_eq ''vend'') impl (not (ev (state_eq (Some 2))))) (watch drinks t)"
  apply (simp only: watch_label implode_vend not_ev_iff)
  apply (simp add: watch_def)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: state_eq_def possible_steps_not_init)
    apply (rule disjI2)
    using once_none_always_none
    unfolding state_eq_def
    by (simp add: alw_iff_sdrop)
qed

lemma possible_steps_0: "possible_steps drinks 0 <> l i = finsert x S' \<Longrightarrow> finsert x S' = {|(1, init)|}"
  apply (case_tac "l = STR ''init''")
   apply (case_tac "i = []")
    apply (simp add: possible_steps_init)
  using possible_steps_not_init
  by auto

lemma apply_updates_init: "apply_updates (Updates init) (\<lambda>x. None) <> = (<>(1 := Num 0))"
  by (simp add: init_def)

(* This is supposed to break *)
lemma vend_insufficient: "possible_steps drinks 1 (<>(1 := Num 0)) STR ''vend'' i = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
   apply (simp add: coin_def)
  apply (simp add: vend_def apply_guards connectives)
  sorry

lemma LTL_init_makes_r_1_zero: "((label_eq ''init'' aand input_eq []) impl nxt (check_exp (Eq (V (R 1)) (L (Num 0))))) (watch drinks t)"
  apply (case_tac "shd t = (STR ''init'', [])")
   apply (simp add: possible_steps_init apply_updates_init watch_def check_exp_def)
  apply clarify
  by (simp add: not_init)

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
   possible_steps drinks 1 (<>(1 := Num 0)) (fst x1) (snd x1) = {||}"
  apply (simp add: possible_steps_empty drinks_def)
  apply safe
   apply (simp add: coin_def)
   apply (metis prod.collapse)
  apply (simp add: vend_def apply_guards)
  by (metis prod.collapse)

lemma invalid_gets_stuck: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
                           x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
                           \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) (<>(1 := Num 0)) p (x1 ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: possible_steps_1_invalid alw_not_some)
qed

lemma LTL_vend_no_coin: "((nxt (label_eq ''vend'' aand input_eq [])) impl not (ev (state_eq (Some 2)))) (watch drinks t)"
  apply (simp add: not_ev_iff event_components implode_vend watch_def state_eq_def)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd t = (STR ''init'', [])")
     defer
    apply (simp add: decompose_pair)
     apply (simp add: possible_steps_not_init alw_not_some)
    apply (simp add: possible_steps_init apply_updates_init)
    apply (rule disjI2)
  proof(coinduction)
    case alw
    then show ?case
      apply (simp add: vend_insufficient)
     by (simp add: possible_steps_not_init alw_not_some)
  qed
qed

lemma LTL_invalid_gets_stuck_2:
  "(((nxt (not (label_eq ''coin'' aand input_eq []))) aand
   (nxt (not (label_eq ''vend'' aand input_eq [])))) impl
   (not (ev (state_eq (Some 2))))) (watch drinks t)"
  apply (simp add: not_ev_iff event_components)
  unfolding watch_def state_eq_def label_eq_def input_eq_def
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: implode_coin implode_vend)
    apply (case_tac "shd t = (STR ''init'', [])")
     defer
     apply (simp only: decompose_pair)
    using possible_steps_not_init alw_not_some
     apply simp
    apply (simp add: possible_steps_init apply_updates_init)
    apply (rule disjI2)
    using invalid_gets_stuck[of "shd (stl t)" "[]" "stl (stl t)"]
    by (simp add: alw_ev init_def)
qed

(* Ramsay, this is the proof you want!
   I'll convert it to an Isabelle code snippet for the actual paper to make it really pretty but for
   now, just use a screenshot image or something... *)
lemma LTL_must_pay_correct: "((ev (state_eq (Some 2))) impl (not (label_eq ''vend'') suntil label_eq ''coin'')) (watch drinks t)"
  apply clarify
  unfolding label_eq_def state_eq_def implode_vend implode_coin
  apply (simp add: watch_def)
  apply (case_tac "shd t = (STR ''init'', [])")
   defer
   apply (simp add: shd_not_init)
  apply (rule suntil.step)
   apply simp
  apply (simp add: possible_steps_init apply_updates_init)
  apply (case_tac "shd (stl t) = (STR ''coin'', [])")
   apply (simp add: suntil.base)
  apply (case_tac "shd (stl t) = (STR ''vend'', [])")
   apply (rule suntil.step)
  using LTL_vend_no_coin[of t]
  apply (simp add: event_components implode_vend state_eq_def watch_def ev_mono)
  using LTL_vend_no_coin[of t]
  apply (simp add: event_components implode_vend state_eq_def watch_def ev_mono)
  using LTL_invalid_gets_stuck_2[of t]
  by (simp add: event_components implode_vend implode_coin state_eq_def watch_def ev_mono)

end
