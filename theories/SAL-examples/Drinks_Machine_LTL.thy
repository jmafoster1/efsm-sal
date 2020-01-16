theory Drinks_Machine_LTL
imports "../efsm-isabelle/examples/Drinks_Machine" "../efsm-ltl/EFSM_LTL"
begin

declare One_nat_def [simp del]

lemma LTL_r2_not_always_gt_100: "not (alw (check_exp (Gt (V (Rg 2)) (L (Num 100))))) (watch drinks i)"
  apply (simp add: not_alw_iff watch_def)
  apply (rule ev.base)
  by (simp add: check_exp_def value_gt_def)

lemma possible_steps_select_wrong_arity: "a = STR ''select'' \<Longrightarrow>
       length b \<noteq> 1 \<Longrightarrow>
       possible_steps drinks 0 <> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma possible_steps_0_not_select: "a \<noteq> STR ''select'' \<Longrightarrow>
       possible_steps drinks 0 <> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma statename_smap: "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) s =
       alw (nxt (\<lambda>x. shd x = (Some 2)) impl (\<lambda>x. shd x = (Some 1))) (smap statename s)"
  by (simp add: state_eq_def alw_iff_sdrop)

lemma "alw (\<lambda>xs. shd (stl xs) = Some 2 \<longrightarrow> shd xs = Some 1)
            (smap statename (make_full_observation drinks (Some 1) r p i))"
proof(coinduction arbitrary: r p)
  case alw
  then show ?case
    apply (case_tac "shd i")
    apply (case_tac "a \<noteq> STR ''vend''")
     apply (case_tac "a \<noteq> STR ''coin''")
      apply (case_tac "possible_steps drinks 1 r a b = {||}")
       apply simp
       apply (rule disjI2, rule alw_mono[of "\<lambda>x. shd (stl x) = None"])
        apply (simp add: smap_statename_None Linear_Temporal_Logic_on_Streams.alw_sconst)
       apply simp
    using drinks_1_rejects apply auto[1]
     apply (case_tac "length b \<noteq> 1")
      apply (case_tac "possible_steps drinks 1 r a b = {||}")
       apply simp
       apply (rule disjI2, rule alw_mono[of "\<lambda>x. shd (stl x) = None"])
        apply (simp add: smap_statename_None Linear_Temporal_Logic_on_Streams.alw_sconst)
       apply simp
    using drinks_1_rejects apply auto[1]
     apply (simp del: make_full_observation.simps)
     apply standard
      apply simp
     apply (simp add: possible_steps_1_coin coin_def finfun_update_twist apply_outputs_def)
     apply (rule disjI1)
     apply (case_tac b)
      apply simp
     apply clarify
     apply (cases i)
     apply simp
     apply (rule_tac x="r(2 $:= value_plus (r $ 2) (Some aa))" in exI)
     apply (rule_tac x=p in exI)
    oops


lemma LTL_nxt_2_means_vend: "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) (watch drinks i)"
  apply (simp only: statename_smap watch_def)
  apply simp
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd i")
    apply (case_tac "a \<noteq> STR ''select''")
     apply (simp add: possible_steps_0_not_select)
     apply (rule disjI2, rule alw_mono[of "\<lambda>x. shd (stl x) = None"])
      apply (simp add: smap_statename_None Linear_Temporal_Logic_on_Streams.alw_sconst)
     apply simp
    apply (case_tac "length b \<noteq> 1")
     apply (simp add: possible_steps_select_wrong_arity)
     apply (rule disjI2, rule alw_mono[of "\<lambda>x. shd (stl x) = None"])
      apply (simp add: smap_statename_None Linear_Temporal_Logic_on_Streams.alw_sconst)
     apply simp
    apply (simp add: possible_steps_0 select_def)
    apply (rule disjI2)
    oops

lemma LTL_costsMoney_aux: "(alw (not (check_exp (Gt (V (Rg 2)) (L (Num 100)))) impl (not (nxt (state_eq (Some 2)))))) (watch drinks i)"
  oops

  (* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma LTL_costsMoney: "(alw (nxt (state_eq (Some 2)) impl (check_exp (Gt (V (Rg 2)) (L (Num 100)))))) (watch drinks i)"
  oops

(* neverReachS2: THEOREM drinks |- label=select AND I(1) = STR(String_coke) AND
                                X(label=coin AND I(1) = NUM(100)) AND
                                X(X(label=vend AND I=InputSequence !empty)) => X(X(X(cfstate=State_2)));;*)
lemma LTL_neverReachS2:"(((((label_eq ''select'') aand (check_exp (Eq (V (Ip 1)) (L (Str ''coke'')))))
                    aand
                    (nxt ((label_eq ''coin'') aand (check_exp (Eq (V (Ip 1)) (L (Num 100)))))))
                    aand
                    (nxt (nxt((label_eq ''vend'' aand (input_eq []))))))
                    impl
                    (nxt (nxt (nxt (state_eq (Some 2))))))
                    (watch drinks i)"
  oops

end