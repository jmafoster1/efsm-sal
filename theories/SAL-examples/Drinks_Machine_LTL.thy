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

lemma drinks_no_possible_steps_1:
  assumes not_coin: "\<not> (a = STR ''coin'' \<and> length b = 1)"
  and not_vend: "\<not> (a = STR ''vend'' \<and> b = [])"
shows "possible_steps drinks 1 r a b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
  apply safe
    apply (metis label_coin not_coin transition.select_convs(2) transitions(2))
  using arity_vend_fail label_vend_fail not_vend apply auto[1]
  using arity_vend label_vend not_vend by auto

lemma apply_updates_vend: "apply_updates (Updates vend) (join_ir [] r) r = r"
  by (simp add: vend_def)

lemma drinks_step_2_none: "ltl_step drinks (Some 2) r e = (None, [], r)"
  by (simp add: drinks_end ltl_step_none)

lemma one_before_two_2: "alw (\<lambda>x. statename (shd (stl x)) = Some 2 \<longrightarrow> statename (shd x) = Some 1) (make_full_observation drinks (Some 2) r [r $ 1] x2a)"
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply standard
    apply (simp add: drinks_end ltl_step_none)
    apply (rule disjI2)
    apply (simp add: drinks_step_2_none)
    by (metis (mono_tags, lifting) alw_mono nxt.simps once_none_nxt_always_none option.simps(3) state_eq_def)
qed

lemma one_before_two_aux:
  assumes "\<exists> p r i. j = nxt (make_full_observation drinks (Some 1) r p) i"
  shows "alw (\<lambda>x. nxt (state_eq (Some 2)) x \<longrightarrow> state_eq (Some 1) x) j"
  using assms apply(coinduct)
  apply (simp add: state_eq_def)
  apply clarify
  apply standard
   apply simp
  subgoal for x p r i
    apply (cases i, simp)
    subgoal for x1 x2
    apply (cases x2, simp)
      subgoal for x1a x2a
        apply (cases x1a, simp)
        apply (case_tac "possible_steps drinks 1 r a b = {||}")
         apply simp
        apply (rule disjI2)
        apply (metis (mono_tags, lifting) alw_iff_sdrop once_none_always_none option.distinct(1) sdrop_simps(2) state_eq_def)
        apply simp
        apply (case_tac "SOME x. x |\<in>| possible_steps drinks 1 r a b")
        apply simp
        subgoal for a b s' t
          apply (case_tac "a = STR ''coin'' \<and> length b = 1")
           apply (simp add: possible_steps_1_coin)
           apply (metis stream.sel(2))
          apply (case_tac "a = STR ''vend'' \<and> b = []")
           defer
           apply (simp add: drinks_no_possible_steps_1)
          apply (cases "r $ 2")
           apply (simp add: drinks_vend_invalid)
          subgoal for v
            apply (cases v)
             defer
           apply (simp add: drinks_vend_invalid)
            subgoal for n
              apply (case_tac "n < 100")
               apply (simp add: drinks_vend_insufficient)
               apply (metis stream.sel(2))
              apply (rule disjI2)
              apply (simp add: drinks_vend_sufficient apply_updates_vend)
              apply clarify
              by (simp add: vend_def apply_outputs_def one_before_two_2)
            done
          done
        done
      done
    done
  done

(* Here is the lemma with quantified variables that I am trying to prove *)
lemma "alw (\<lambda>x. nxt (state_eq (Some 2)) x \<longrightarrow> state_eq (Some 1) x)
            (nxt (make_full_observation drinks (Some 1) r p) i)"
  using one_before_two_aux by blast

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
    apply (simp add: alw_smap state_eq_def[symmetric])
    apply (simp only: nxt.simps[symmetric])
    using one_before_two_aux by blast
qed

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