theory Coin_Tea
  imports "../../efsm-ltl/EFSM_LTL" "../../efsm-isabelle/AExp"
begin

declare One_nat_def [simp del]
declare value_gt_def [simp]

text_raw\<open>\snip{cointea}{1}{2}{%\<close>
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
          Guard = [GExp.Gt (aexp.V (vname.R 1)) (aexp.L (Num 0))],
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

lemma "(not (label_eq ''vend'') until (label_eq ''coin'')) (watch drinks t)"
  oops

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
          (snd (snd (ltl_step drinks (Some 0) <> (shd t)))) (stl t))"
proof-
  show ?thesis
    apply (case_tac "shd t")
    apply simp
    apply (case_tac "a = STR ''init'' \<and> b = []")
     apply (simp add: possible_steps_init state_eq_def)
    by (simp add: state_eq_def possible_steps_not_init)
qed

lemma make_full_obs_neq: "make_full_observation drinks (fst (ltl_step drinks (Some 0) <> (shd t))) (snd (snd (ltl_step drinks (Some 0) <> (shd t))))
     (stl t) \<noteq>
    make_full_observation drinks (Some 0) <> t"
  apply (case_tac "ltl_step drinks (Some 0) <> (shd t)")
  apply (case_tac "shd t")
    apply simp
    apply (case_tac "aa = STR ''init'' \<and> ba = []")
   apply (simp add: possible_steps_init init_def)
  apply (metis (no_types, lifting) make_full_observation.simps(1) option.inject state.ext_inject zero_neq_one)
  apply (simp add: possible_steps_not_init)
  by (metis make_full_observation.simps(1) option.simps(3) state.ext_inject)

lemma state_none: "((state_eq None) impl nxt (state_eq None)) (make_full_observation e s r t)"
  by (simp add: state_eq_def)

lemma shd_state_is_none: "(state_eq None) (make_full_observation e None r t)"
  by (simp add: state_eq_def)

lemma state_none_2: "(state_eq None) (make_full_observation e s r t) \<Longrightarrow> (state_eq None) (make_full_observation e s r (stl t))"
  by (simp add: state_eq_def)

lemma alw_ev: "alw f = not (ev (\<lambda>s. \<not>f s))"
  by simp

lemma state_eq_alt: "alw (state_eq s) s' = alw (\<lambda>x. shd x = s) (smap (\<lambda>x. statename x) s')"
  apply standard
  apply (simp add: state_eq_def alw_iff_sdrop)
  by (simp add: state_eq_def alw_mono alw_smap)

lemma test: "statename (shd (make_full_observation e None r t)) = None"
  by simp

lemma "alw (nxt (state_eq (Some 2)) impl (label_eq ''vend'')) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd t")
    apply (case_tac "a = STR ''init'' \<and> b = []")
     defer
     apply (simp add: possible_steps_not_init)
    oops


lemma "alw (\<lambda>s. state_eq None (stl s)) (make_full_observation drinks None <> t)"
  by (metis alw_iff_sdrop once_none_always_none sdrop_simps(2))

lemma no_possible_steps: "possible_steps e s r (fst t) (snd t) = {||} \<Longrightarrow> ltl_step e (Some s) r t = (None, [], r)"
proof -
  assume "possible_steps e s r (fst t) (snd t) = {||}"
  then have "ltl_step e (Some s) r (fst t, snd t) = (None, [], r)"
    using ltl_step.simps(2) by presburger
  then show ?thesis
    by simp
qed

lemma no_possible_steps_not_init:"t \<noteq> (STR ''init'', []) \<Longrightarrow> possible_steps drinks 0 r (fst t) (snd t) = {||}"
  apply (simp add: possible_steps_def ffilter_def Set.filter_def drinks_def fset_both_sides Abs_fset_inverse)
  by (metis init_def length_0_conv less_numeral_extra(1) prod.collapse transition.ext_inject transition.surjective)

lemma step_not_init: "t \<noteq> (STR ''init'', []) \<Longrightarrow> ltl_step drinks (Some 0) r t = (None, [], r)"
  using no_possible_steps_not_init no_possible_steps
  by simp

lemma possible_steps_coin: "possible_steps drinks 1 r STR ''coin'' [] = {|(1, coin)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def)

lemma possible_steps_vend_insufficient: "n \<le> 0 \<Longrightarrow> possible_steps drinks 1 (<>(1 := Num n)) STR ''vend'' [] = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def apply_guards_def join_ir_def)

lemma possible_steps_vend_sufficient: "n > 0 \<Longrightarrow> possible_steps drinks 1 (<>(1 := Num n)) STR ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def apply_guards_def join_ir_def)

lemma invalid_possible_steps_1:
  "shd t \<noteq> (STR ''coin'', []) \<Longrightarrow>
   shd t \<noteq> (STR ''vend'', []) \<Longrightarrow>
   possible_steps drinks 1 r (fst (shd t)) (snd (shd t)) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  by (metis coin_def length_0_conv prod.collapse transition.ext_inject transition.surjective vend_def)

lemma updates_vend: "apply_updates (Updates vend) i r = r"
  by (simp add: vend_def)

lemma less_than_zero_not_nxt_2:
  "n \<le> 0 \<Longrightarrow>
   statename (shd (stl (make_full_observation drinks (Some 1) (<>(1 := Num n)) t))) \<noteq> Some 2"
  apply (case_tac "shd t = (STR ''coin'', [])")
   apply (simp add: possible_steps_coin)
  apply (case_tac "shd t = (STR ''vend'', [])")
   apply (simp add: possible_steps_vend_insufficient)
  by (simp add: invalid_possible_steps_1 no_possible_steps)

lemma possible_steps_2: "possible_steps drinks 2 r (fst (shd t)) (snd (shd t)) = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)

lemma shd_not_lt_zero: "0 \<le> n \<Longrightarrow> (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $ 1) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None (<>(1 := Num n)) t)"
  by simp

lemma nxt_not_lt_zero: "0 \<le> n \<Longrightarrow> nxt (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $ 1) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None (<>(1 := Num n)) t)"
  by simp

lemma once_none_remains_not_lt_zero: "0 \<le> n \<Longrightarrow> alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $ 1) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None (<>(1 := Num n)) t)"
  using no_updates_none
  by (simp add: alw_iff_sdrop)

lemma once_none_null_remains_not_lt_zero: "alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $ 1) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None <> t)"
  using no_updates_none
  by (simp add: alw_iff_sdrop)

lemma stop_at_2: "0 \<le> n \<Longrightarrow>
      alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) $ 1) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks (Some 2) (<>(1 := Num n)) t)"
proof(coinduction)
  case alw
  then show ?case
    using ltl_step_alt once_none_remains_not_lt_zero possible_steps_2 by auto
qed

lemma next_not_lt_zero:
  "n \<ge> 0 \<Longrightarrow>
   (nxt (not 
    (check_exp (Lt (V (R 1)) (L (Num 0))))
    )) (make_full_observation drinks (Some 1) (<>(1 := Num n)) t)"
    apply simp
    apply (case_tac "shd t = (STR ''vend'', [])")
    apply (case_tac "n = 0")
      apply (simp add: possible_steps_vend_insufficient check_exp_def Lt_def)
     apply (simp add: possible_steps_vend_sufficient updates_vend check_exp_def Lt_def)
    apply (case_tac "shd t = (STR ''coin'', [])")
   apply (simp add: possible_steps_coin datastate coin_def value_plus_def check_exp_def Lt_def)
  by (simp add: check_exp_def Lt_def invalid_possible_steps_1 ltl_step_alt)

lemma not_initialised: "alw (\<lambda>xs. state_eq (Some 1) xs \<and>
              MaybeBoolInt (<) (datastate (shd xs) $ (1)) (Some (Num 0)) = trilean.true \<and> label_eq ''vend'' xs \<and> input_eq [] xs \<longrightarrow>
              state_eq (Some 2) (stl xs))
     (make_full_observation drinks None <> t)"
  using once_none_always_none state_eq_None_not_Some
  by (simp add: alw_iff_sdrop)

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

lemma step_0_vend: "fst e = STR ''vend'' \<Longrightarrow> ltl_step drinks (Some 0) r e = (None, [], r)"
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
  apply (simp add: init_def)
  by auto

lemma LTL_label_vend_not_2: "((label_eq ''vend'') impl (not (ev (state_eq (Some 2))))) (watch drinks t)"
  apply (simp only: watch_label implode_vend not_ev_iff)
  apply (simp add: watch_def)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: state_eq_def possible_steps_not_init)
    apply (simp add: step_0_vend)
    using once_none_always_none[of drinks]
    unfolding state_eq_def
    by (simp add: alw_iff_sdrop)
qed

lemma possible_steps_0: "possible_steps drinks 0 <> l i = finsert x S' \<Longrightarrow> finsert x S' = {|(1, init)|}"
  apply (case_tac "l = STR ''init''")
   apply (case_tac "i = []")
    apply (simp add: possible_steps_init)
  using possible_steps_not_init
  by auto

lemma vend_insufficient: "possible_steps drinks 1 (<>(1 := Num 0)) STR ''vend'' i = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
   apply (simp add: coin_def)
  by (simp add: vend_def apply_guards_def join_ir_def)

lemma updates_init: "apply_updates (Updates init) (\<lambda>x. None) <> = (<>(1 := Num 0))"
  by (simp add: init_def)

lemma LTL_aux2: "((nxt (label_eq ''vend'')) impl not (ev (state_eq (Some 2)))) (watch drinks t)"
  apply (simp add: watch_def label_eq_def implode_vend not_ev_iff)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: state_eq_def)
    apply (case_tac "shd t = (STR ''init'', [])")
     defer
    using possible_steps_not_init alw_not_some
     apply (simp add: no_possible_steps_not_init)
    using step_not_init apply auto[1]
    apply (simp add: possible_steps_init updates_init)
    apply (rule disjI2)
  proof(coinduction)
    case alw
    then show ?case
      apply (simp add: vend_insufficient)
      apply (rule disjI2)
      using alw_not_some
      by (simp add: ltl_step_alt vend_insufficient)
  qed
qed

text_raw\<open>\snip{checkinit}{1}{2}{%\<close>
lemma LTL_init_makes_r_1_zero:
  "((label_eq ''init'' aand input_eq []) impl
    (nxt (check_exp (Eq (V (R 1)) (L (Num 0))))))
   (watch drinks t)"
text_raw\<open>}%endsnip\<close>
  apply (case_tac "shd t = (STR ''init'', [])")
  using watch_def
   apply (simp add: possible_steps_init updates_init check_exp_def)
  by (simp add: not_init check_exp_def)

(* This is not a true property but is good for testing the translation process *)
lemma LTL_must_pay_wrong: "((not (label_eq ''vend'' suntil label_eq ''coin'')) suntil state_eq None) (watch drinks t)"
  oops

lemma shd_not_init: "shd t \<noteq> (STR ''init'', []) \<Longrightarrow> \<not> ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 0) <> t)"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd t")
    apply simp
    by (simp add: possible_steps_not_init alw_not_some)
qed

lemma vend_gets_stuck: "stl t = (STR ''vend'', []) ## x2 \<Longrightarrow> \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) (<>(1 := Num 0)) ((STR ''vend'', []) ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: vend_insufficient alw_not_some)
qed

lemma possible_steps_1_invalid: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
       x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
       possible_steps drinks 1 (<>(1 := Num 0)) (fst x1) (snd x1) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  apply safe
   apply (simp add: coin_def)
   apply (metis prod.collapse)
  by (simp add: vend_def apply_guards)

lemma invalid_gets_stuck: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
                           x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
                           \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) (<>(1 := Num 0)) (x1 ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: possible_steps_1_invalid alw_not_some ltl_step_alt)
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
     apply (simp add: possible_steps_not_init alw_not_some ltl_step_alt)
    apply (simp add: possible_steps_init updates_init)
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
    apply (simp add: possible_steps_init updates_init ltl_step_alt)
    apply (rule disjI2)
    apply (simp add: possible_steps_init init_def)
    using invalid_gets_stuck[of "shd (stl t)" "stl (stl t)"]
    by (simp add: alw_ev)
qed

(* This should translate the same as LTL_must_pay_correct *)
lemma LTL_must_pay_correct_bracketed:
  "((ev (state_eq (Some 2))) impl
    ((not (label_eq ''vend'')) suntil label_eq ''coin''))
   (watch drinks t)"
  oops

text_raw\<open>\snip{mustpaycorrectfull}{1}{2}{%\<close>
lemma LTL_must_pay_correct_full: 
  "(ev (\<lambda>s. statename (shd s) = Some 2) impl
   ((\<lambda>xs. fst (event (shd xs)) \<noteq> STR ''vend'') until
    (\<lambda>xs. fst (event (shd xs)) = STR ''coin'')))
   (watch drinks t)"
text_raw\<open>}%endsnip\<close>
  oops

(* Ramsay, this is the proof you want!
   I'll convert it to an Isabelle code snippet for the actual paper to make it really pretty but for
   now, just use a screenshot image or something... *)
text_raw\<open>\snip{mustpaycorrect}{1}{2}{%\<close>
lemma LTL_must_pay_correct:
  "((ev (state_eq (Some 2))) impl
    (not (label_eq ''vend'') suntil label_eq ''coin''))
   (watch drinks t)"
  apply clarify
  apply (rule suntil.step)
  using LTL_label_vend_not_2 watch_def apply auto[1]
  apply (case_tac "shd (stl t) = (STR ''coin'', [])")
   apply (simp add: label_eq_def implode_coin suntil.base watch_def)
  apply (case_tac "shd (stl t) = (STR ''vend'', [])")
   apply (rule suntil.step)
  using LTL_aux2 watch_def watch_def apply auto[1]
  using LTL_aux2 label_eq_def implode_vend watch_def apply auto[1]
  using LTL_aux2 LTL_invalid_gets_stuck_2 suntil.base by fastforce
text_raw\<open>}%endsnip\<close>

end
