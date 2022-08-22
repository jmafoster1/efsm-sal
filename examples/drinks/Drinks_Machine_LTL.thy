theory Drinks_Machine_LTL
imports "Drinks_Machine" "Extended_Finite_State_Machines.EFSM_LTL" "Extended_Finite_State_Machines.EFSM"
begin

declare One_nat_def [simp del]

lemma P_ltl_step_0:
  assumes invalid: "P (None, [], <>)"
  assumes select: "l = STR ''select'' \<longrightarrow> P (Some 1, [], <1 $r:= Some (hd i), 2 $r:= Some (value.Int 0)>)"
  shows "P (ltl_step drinks (Some 0) <> (l, i))"
proof-
  have length_i: "\<exists>d. (l, i) = (STR ''select'', [d]) \<Longrightarrow> length i = 1"
    by (induct i, auto)
  have length_i_2: "\<forall>d. i \<noteq> [d] \<Longrightarrow> length i \<noteq> 1"
    by (induct i, auto)
  show ?thesis
    apply (case_tac "\<exists>d. (l, i) = (STR ''select'', [d])")
     apply (simp add: possible_steps_0 length_i select_def apply_updates_def)
    using select apply auto[1]
    by (simp add: possible_steps_0_invalid length_i_2 invalid)
qed

lemma P_ltl_step_1:
  assumes invalid: "P (None, [], r)"
  assumes coin: "l = STR ''coin'' \<longrightarrow> P (Some 1, [value_plus (r $r 2) (Some (hd i))], registers_update r 2 (value_plus (r $r 2) (Some (i ! 0))))"
  assumes vend_fail: "value_gt (Some (value.Int 100)) (r $r 2) = trilean.true \<longrightarrow> P (Some 1, [],r)"
  assumes vend: "\<not>? value_gt (Some (value.Int 100)) (r $r 2) = trilean.true \<longrightarrow> P (Some 2, [r$r1], r)"
  shows "P (ltl_step drinks (Some 1) r (l, i))"
proof-
  have length_i: "\<And>s. \<exists>d. (l, i) = (s, [d]) \<Longrightarrow> length i = 1"
    by (induct i, auto)
  have length_i_2: "\<forall>d. i \<noteq> [d] \<Longrightarrow> length i \<noteq> 1"
    by (induct i, auto)
  show ?thesis
    apply (case_tac "\<exists>d. (l, i) = (STR ''coin'', [d])")
     apply (simp add: possible_steps_1_coin length_i coin_def apply_outputs_def apply_updates_def)
    using coin apply auto[1]
    apply (case_tac "(l, i) = (STR ''vend'', [])")
     apply (case_tac "\<exists>n. r $r 2 = Some (value.Int n)")
      apply clarsimp
      apply (case_tac "n \<ge> 100")
       apply (simp add: drinks_vend_sufficient vend_def apply_updates_def apply_outputs_def)
       apply (metis registers_upd_triv possible_steps_2_vend vend vend_ge_100)
      apply (simp add: drinks_vend_insufficient vend_fail_def apply_updates_def apply_outputs_def)
      apply (metis MaybeBoolInt.simps(1) registers_upd_triv not_less value_gt_def vend_fail)
     apply (simp add: drinks_vend_invalid invalid)
    by (simp add: drinks_no_possible_steps_1 length_i_2 invalid)
qed

lemma LTL_r2_not_always_gt_100: "not (alw (check_exp (Gt (V (Rg 2)) (L (value.Int 100))))) (watch drinks i)"
  using value_gt_def by auto

lemma drinks_step_2_none: "ltl_step drinks (Some 2) r e = (None, [], r)"
  by (simp add: drinks_end ltl_step_none_2)

lemma one_before_two_2:
  "alw (\<lambda>x. statename (shd (stl x)) = Some 2 \<longrightarrow> statename (shd x) = Some 1) (make_full_observation drinks (Some 2) r [r $r 1] x2a)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: drinks_step_2_none)
    by (metis (mono_tags, lifting) alw_mono nxt.simps once_none_nxt_always_none option.distinct(1))
qed

lemma one_before_two_aux:
  assumes "\<exists> p r i. j = nxt (make_full_observation drinks (Some 1) r p) i"
  shows "alw (\<lambda>x. nxt (state_eq (Some 2)) x \<longrightarrow> state_eq (Some 1) x) j"
  using assms apply(coinduct)
  apply simp
  apply clarify
  apply standard
   apply simp
  apply simp
  apply (case_tac "shd (stl i)")
  apply (simp del: ltl_step.simps)
  apply (rule P_ltl_step_1)
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (state_eq None)"])
      apply (simp add: once_none_nxt_always_none)
     apply simp
    apply auto[1]
   apply auto[1]
  apply simp
  by (simp add: one_before_two_2)

lemma LTL_nxt_2_means_vend:
  "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd i")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_0)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (state_eq None)"])
      apply (simp add: once_none_nxt_always_none)
    using one_before_two_aux by auto
qed

lemma costsMoney_aux:
  assumes "\<exists>p r i. j = (nxt (make_full_observation drinks (Some 1) r p) i)"
  shows "alw (\<lambda>xs. nxt (state_eq (Some 2)) xs \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (value.Int 100))) xs) j"
  using assms apply coinduct
  apply clarsimp
  apply (case_tac "shd (stl i)")
  apply (simp del: ltl_step.simps)
  apply (rule P_ltl_step_1)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (state_eq None)"])
      apply (simp add: once_none_nxt_always_none)
     apply simp
    apply auto[1]
   apply auto[1]
  apply simp
  apply standard
  apply (rule disjI2)
  apply (rule alw_mono[of "nxt (state_eq None)"])
   apply (metis (no_types, lifting) drinks_step_2_none fst_conv make_full_observation.sel(2) nxt.simps nxt_alw once_none_always_none_aux)
  by simp

(* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma LTL_costsMoney:
  "(alw (nxt (state_eq (Some 2)) impl (check_exp (Ge (V (Rg 2)) (L (value.Int 100)))))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (cases "shd i")
    subgoal for l ip
      apply (case_tac "l = STR ''select'' \<and> length ip = 1")
       defer
       apply (simp add: possible_steps_0_invalid)
       apply (rule disjI2)
       apply (rule alw_mono[of "nxt (state_eq None)"])
        apply (simp add: once_none_nxt_always_none)
       apply (simp add: )
      apply (simp add: possible_steps_0 select_def)
      apply (rule disjI2)
      apply (simp only: nxt.simps[symmetric])
      using costsMoney_aux by auto
    done
qed

lemma LTL_costsMoney_aux:
  "(alw (not (check_exp (Ge (V (Rg 2)) (L (value.Int 100)))) impl (not (nxt (state_eq (Some 2)))))) (watch drinks i)"
  by (metis (no_types, lifting) LTL_costsMoney alw_mono)

lemma implode_select: "String.implode ''select'' = STR ''select''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemmas implode_labels = implode_select implode_coin implode_vend

lemma LTL_neverReachS2:"((((((label_eq ''select'' aand input_eq [Str ''coke''])))
                    aand
                    (nxt (((label_eq ''coin'' aand input_eq [value.Int 100])))))
                    aand
                    (nxt (nxt((label_eq ''vend'' aand (input_eq []))))))
                    impl
                    (nxt (nxt (nxt (state_eq (Some 2))))))
                    (watch drinks i)"
  apply (simp add: implode_labels)
  apply (cases i)
  apply clarify
  apply simp
  apply (simp add: possible_steps_0 select_def)
  apply (case_tac "shd x2", clarify)
  apply (simp add: possible_steps_1_coin coin_def value_plus_def finfun_update_twist apply_updates_def)
  apply (case_tac "shd (stl x2)", clarify)
  by (simp add: drinks_vend_sufficient )

lemma ltl_step_not_select:
  "\<nexists>i. e = (STR ''select'', [i]) \<Longrightarrow>
   ltl_step drinks (Some 0) r e = (None, [], r)"
  apply (cases e, clarify)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def select_def)
  by (cases e, case_tac b, auto)

lemma ltl_step_select:
  "ltl_step drinks (Some 0) <> (STR ''select'', [i]) = (Some 1, [], <1 $r:= Some i, 2 $r:= Some (value.Int 0)>)"
  apply (rule  ltl_step_some[of _ _ _ _ _ _ select])
    apply (simp add: possible_steps_0)
   apply (simp add: select_def)
  by (simp add: select_def finfun_update_twist apply_updates_def)

lemma ltl_step_not_coin_or_vend:
  "\<nexists>i. e = (STR ''coin'', [i]) \<Longrightarrow>
    e \<noteq> (STR ''vend'', []) \<Longrightarrow>
    ltl_step drinks (Some 1) r e = (None, [], r)"
  apply (cases e)
  apply (simp del: ltl_step.simps)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
  by (case_tac e, case_tac b, auto)

lemma ltl_step_coin:
  "\<exists>p r'. ltl_step drinks (Some 1) r (STR ''coin'', [i]) = (Some 1, p, r')"
  by (simp add: possible_steps_1_coin)

lemma alw_tl:
  "alw \<phi> (make_full_observation e (Some 0) <> [] xs) \<Longrightarrow>
    alw \<phi>
     (make_full_observation e (fst (ltl_step e (Some 0) <> (shd xs))) (snd (snd (ltl_step e (Some 0) <> (shd xs))))
       (fst (snd (ltl_step e (Some 0) <> (shd xs)))) (stl xs))"
  by auto

lemma stop_at_none:
  "alw (\<lambda>xs. output (shd (stl xs)) = [Some (EFSM.Str drink)] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (value.Int 100))) xs)
            (make_full_observation drinks None r p t)"
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: no_output_none_nxt)
  by simp

lemma drink_costs_money_aux:
  assumes "\<exists>p r t. j = make_full_observation drinks (Some 1) r p t"
  shows "alw (\<lambda>xs. output (shd (stl xs)) = [Some (EFSM.Str drink)] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (value.Int 100))) xs) j"
  using assms apply coinduct
  apply clarsimp
  apply (case_tac "shd t")
  apply (simp del: ltl_step.simps)
  apply (rule P_ltl_step_1)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply (simp add: Str_def value_plus_never_string)
    apply auto[1]
   apply auto[1]
  apply simp
  apply standard
  apply (rule disjI2)
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: drinks_step_2_none no_output_none_if_empty nxt_alw)
  by simp

lemma LTL_drinks_cost_money:
  "alw (nxt (output_eq [Some (Str drink)]) impl (check_exp (Ge (V (Rg 2)) (L (value.Int 100))))) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd t")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_0)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply simp
    using drink_costs_money_aux
    apply simp
    by blast
qed

lemma steps_1_invalid:
      "\<nexists>i. (a, b) = (STR ''coin'', [i]) \<Longrightarrow>
       \<nexists>i. (a, b) = (STR ''vend'', []) \<Longrightarrow>
       possible_steps drinks 1 r a b = {||}"
  apply (simp add: possible_steps_empty drinks_def transitions can_take_transition_def can_take_def)
  by (induct b, auto)

lemma output_vend_aux:
  assumes "\<exists>p r t. j = make_full_observation drinks (Some 1) r p t"
  shows "alw (\<lambda>xs. label_eq ''vend'' xs \<and> output (shd (stl xs)) = [Some d] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (value.Int 100))) xs) j"
  using assms apply coinduct
  apply clarsimp
  apply (case_tac "shd t")
  apply (simp add: implode_vend del: ltl_step.simps)
  apply (rule P_ltl_step_1)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply auto[1]
   apply auto[1]
  apply simp
  apply standard
  apply (rule disjI2)
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: drinks_step_2_none no_output_none_if_empty nxt_alw)
  by simp

text_raw\<open>\snip{outputVend}{1}{2}{%\<close>
lemma LTL_output_vend:
  "alw (((label_eq ''vend'') aand (nxt (output_eq [Some d]))) impl
         (check_exp (Ge (V (Rg 2)) (L (value.Int 100))))) (watch drinks t)"
text_raw\<open>}%endsnip\<close>
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: implode_vend)
    apply (case_tac "shd t")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_0)
     apply simp
    apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply simp
    subgoal for a b
      using output_vend_aux[of "(make_full_observation drinks (Some 1)
              <1 $r:= Some (hd b), 2 $r:= Some (value.Int 0)> [] (stl t))" d]
      using implode_vend by auto
    done
qed

text_raw\<open>\snip{outputVendUnfolded}{1}{2}{%\<close>
lemma LTL_output_vend_unfolded:
  "alw (\<lambda>xs. (label (shd xs) = STR ''vend'' \<and>
             nxt (\<lambda>s. output (shd s) = [Some d]) xs) \<longrightarrow>
              \<not>? value_gt (Some (value.Int 100)) (datastate (shd xs) $r 2) = trilean.true)
     (watch drinks t)"
  text_raw\<open>}%endsnip\<close>
  apply (insert LTL_output_vend[of d t])
  by (simp add: implode_vend)

lemma possible_steps_invalid_state: "s \<ge> 2 \<Longrightarrow> possible_steps drinks s r l i = {||}"
  by (simp add: possible_steps_def drinks_def ffilter_finsert)

lemma all_possible_steps_drinks:
  "(x |\<in>| possible_steps drinks s r l i) \<Longrightarrow>
   (x \<in> {(1, select), (1, coin), (1, vend_fail), (2, vend)})"
  apply (simp add: possible_steps_def drinks_def)
  by auto

lemma valid_trace_simps: "valid_trace e a2 r a4 =
(
  (\<exists>s l i p t.
     (a4 = \<lparr>statename = Some s, datastate = r, action = (l, i), output = p\<rparr> ## t \<and>
     a2 = Some s \<and>
     ((\<exists>(s', tr)|\<in>|possible_steps e s r l i.
         evaluate_outputs tr i r = output (shd t) \<and>
         Some s' = statename (shd t) \<and>
         evaluate_updates tr i r = datastate (shd t) \<and> valid_trace e (Some s') (evaluate_updates tr i r) t) \<or>
     possible_steps e s r l i = {||} \<and> [] = output (shd t) \<and> valid_trace e None r t) \<or>
     a4 = t \<and>
     a2 = None \<and>
     smap (\<lambda>x. (statename x, datastate x, output x)) t = sconst (None, r, [])
  )
  )
)"
  apply (simp add: valid_trace.simps[of e a2 r a4])
  apply standard
   apply blast
  by blast (* ~10s *)

lemma in_possible_steps_0: "(s', tr) |\<in>| possible_steps drinks 0 r l i \<Longrightarrow> ((s', tr) = (1, select))"
  apply (simp add: possible_steps_def drinks_def)
  by auto

lemma ex_possible_steps_0: "(\<exists>a b. (a, b) \<in> fset (possible_steps drinks 0 r l i)) = (possible_steps drinks 0 r l i = {|(1, select)|})"
  apply (simp add: possible_steps_def drinks_def ffilter_finsert select_def)
  by auto

lemma ex_possible_steps_1: "(\<exists>a b. (a, b) \<in> fset (possible_steps drinks 1 r l i)) = (
  possible_steps drinks 1 r l i = {|(1, coin)|} \<or>
  possible_steps drinks 1 r l i = {|(1, vend_fail)|} \<or>
  possible_steps drinks 1 r l i = {|(2, vend)|}
)"
  apply (case_tac "l=STR ''coin'' \<and> length i = 1")
   apply (simp add: possible_steps_1_coin)
  apply (case_tac "l=STR ''vend'' \<and> i = []")
   apply (case_tac "r $r 2")
    apply (simp add: drinks_vend_invalid fempty_not_finsert)
  subgoal for a
    apply (cases a)
    subgoal for n
      apply (case_tac "n \<ge> 100")
       apply (simp add: drinks_vend_sufficient)
      using drinks_vend_insufficient by force
    using drinks_vend_invalid apply auto[1]
    using drinks_vend_invalid by auto[1]
  using drinks_no_possible_steps_1 by auto

lemma coin_label: "possible_steps drinks 1 r l i = {|(1, coin)|} \<Longrightarrow> l = STR ''coin''"
  apply (simp add: possible_steps_def drinks_def ffilter_finsert transitions)
  apply (case_tac "STR ''coin'' = l \<and> length i = 1")
   apply simp
  apply (simp add: ffilter_finsert)
  apply (case_tac "STR ''vend'' = l \<and> i = [] \<and> value_gt (Some (value.Int 100)) (r $r 2) = trilean.true")
   apply simp
  apply (simp add: ffilter_finsert)
  apply (case_tac "STR ''vend'' = l \<and> i = [] \<and> \<not>? value_gt (Some (value.Int 100)) (r $r 2) = trilean.true")
  by auto

lemma vend_fail_label: "possible_steps drinks 1 r l i = {|(1, vend_fail)|} \<Longrightarrow> l = STR ''vend''"
  apply (simp add: possible_steps_def drinks_def ffilter_finsert transitions)
  apply (case_tac "STR ''coin'' = l \<and> length i = 1")
   apply simp
  apply (simp add: ffilter_finsert)
  apply (case_tac "STR ''vend'' = l \<and> i = [] \<and> value_gt (Some (value.Int 100)) (r $r 2) = trilean.true")
   apply simp
  apply (simp add: ffilter_finsert)
  apply (case_tac "STR ''vend'' = l \<and> i = [] \<and> \<not>? value_gt (Some (value.Int 100)) (r $r 2) = trilean.true")
  by auto

lemma value_gt_true_int: "(value_gt (Some (value.Int n)) (r $r m) = trilean.true) = (\<exists>n'. r $r m = Some (value.Int n') \<and> n' < n)"
  apply (simp add: value_gt_def)
  apply (cases "r $r m")
   apply simp
  subgoal for a
    apply (cases a)
    by auto
  done

lemma possible_steps_1_invalid: "\<not> (STR ''coin'' = l \<and> length i = 1) \<Longrightarrow>
       \<not> (STR ''vend'' = l \<and> i = [] \<and> value_gt (Some (value.Int 100)) (r $r 2) = trilean.true) \<Longrightarrow>
       \<not> (STR ''vend'' = l \<and> i = [] \<and> \<not>? value_gt (Some (value.Int 100)) (r $r 2) = trilean.true) \<Longrightarrow>
      possible_steps drinks 1 r l i = {||}"
  by (simp add: possible_steps_def drinks_def ffilter_finsert transitions)

lemma smap_sconst_alw: "smap f s = sconst c \<Longrightarrow> alw (\<lambda>x. f (shd x) = c) s"
  by (simp add: alw_iff_sdrop smap_alt)

lemma smap_output: "smap (\<lambda>x. (statename x, datastate x, output x)) t = sconst (None, r, []) \<Longrightarrow> alw (output_eq []) t"
  apply (insert smap_sconst_alw[of "(\<lambda>x. (statename x, datastate x, output x))" t "(None, r, [])"])
  by (simp add: alw_mono)

lemma alw_nxt_alw: "alw f s \<Longrightarrow> alw (nxt f) s"
  using nxt_alw by auto

lemma "ltl_apply (alw (\<lambda>xs. (label (shd xs) = STR ''vend'' \<and>
             nxt (\<lambda>s. output (shd s) = [Some d]) xs) \<longrightarrow>
              \<not>? value_gt (Some (value.Int 100)) (datastate (shd xs) $r 2) = trilean.true)) drinks"
  apply (rule ltl_apply_all_states_registers)
  subgoal for s r t
    apply (coinduction arbitrary: s r t)
    apply simp
    apply (case_tac "s=Some 0")
     apply clarsimp
    subgoal for r t
      apply (rule valid_trace.cases)
         apply simp
        apply (simp add: fBex_def Bex_def)
        apply clarsimp
        apply (case_tac "possible_steps drinks 0 r l i = {|(1, select)|}")
      using drinks_0_rejects apply auto[1]
      using ex_possible_steps_0 apply blast
      by auto
    apply (case_tac "s=Some 1")
     apply clarsimp
    subgoal for r t
      apply (rule valid_trace.cases)
         apply simp
        apply (case_tac "STR ''coin'' = l \<and> length i = 1")
         apply auto[1]
        apply (case_tac "STR ''vend'' = l \<and> i = [] \<and> value_gt (Some (value.Int 100)) (r $r 2) = trilean.true")
         apply (simp add: value_gt_true_int)
         apply (erule exE)
         apply (simp add: drinks_vend_insufficient vend_fail_def)
         apply auto[1]
        apply (case_tac "STR ''vend'' = l \<and> i = [] \<and> \<not>? value_gt (Some (value.Int 100)) (r $r 2) = trilean.true")
         apply auto[1]
        apply (simp add: possible_steps_1_invalid)
       apply auto[1]
      by simp
      apply (rule valid_trace.cases)
       apply simp
      apply (simp add:possible_steps_invalid_state)
     apply auto[1]
    apply simp
    apply standard
    using smap_output apply fastforce
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (output_eq [])"])
    using smap_output alw_nxt_alw apply blast
    by simp
  done

end
