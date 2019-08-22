theory Drinks_Machine_LTL
imports Drinks_Machine "../EFSM_LTL"
begin

declare One_nat_def [simp del]

lemma LTL_r2_not_always_gt_100: "not (alw (check_inx rg 2 value_gt (Some (Num 100)))) (watch drinks i)"
  apply (simp add: not_alw_iff watch_def)
  apply (rule ev.base)
  by (simp add: value_gt_def)

lemma possible_steps_select_wrong_arity: "a = STR ''select'' \<Longrightarrow>
       length b \<noteq> 1 \<Longrightarrow>
       possible_steps drinks 0 Map.empty a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma possible_steps_0_not_select: "a \<noteq> STR ''select'' \<Longrightarrow>
       possible_steps drinks 0 Map.empty a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma LTL_nxt_2_means_vend: "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: watch_def)
    apply (case_tac "shd i")
    apply simp
    apply (case_tac "a = STR ''select''")
     apply (case_tac "length b = 1")
      apply (simp add: possible_steps_0)
      defer
      apply (simp add: possible_steps_select_wrong_arity)
      apply (metis (no_types, lifting) once_none_always_none state_eq_def alw.cases alw.coinduct option.distinct(1))
     apply (simp add: possible_steps_0_not_select)
     apply (metis (no_types, lifting) once_none_always_none state_eq_def alw.cases alw.coinduct option.distinct(1))
    apply standard
     apply (simp add: state_eq_def)
    apply (rule disjI2)
    oops

lemma LTL_costsMoney_aux: "(alw ((not (check_inx rg 2 value_gt (Some (Num 100)))) impl (not (nxt (state_eq (Some 2)))))) (watch drinks i)"
  oops

  (* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma LTL_costsMoney: "(alw ((nxt (state_eq (Some 2))) impl ((check_inx rg 2 value_gt (Some (Num 100)))))) (watch drinks i)"
  oops

(* neverReachS2: THEOREM drinks |- label=select AND I(1) = STR(String_coke) AND
                                X(label=coin AND I(1) = NUM(100)) AND
                                X(X(label=vend AND I=InputSequence !empty)) => X(X(X(cfstate=State_2)));;*)
lemma LTL_neverReachS2:"(((((label_eq ''select'') aand (check_inx ip 1 value_eq (Some (Str ''coke''))))
                    aand
                    (nxt ((label_eq ''coin'') aand (check_inx ip 1 value_eq (Some (Num 100))))))
                    aand
                    (nxt (nxt((label_eq ''vend'' aand (input_eq []))))))
                    impl
                    (nxt (nxt (nxt (state_eq (Some 2))))))
                    (watch drinks i)"
  oops

end