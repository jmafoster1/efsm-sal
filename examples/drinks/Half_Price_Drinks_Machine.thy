theory Half_Price_Drinks_Machine
imports Drinks_Machine "Extended_Finite_State_Machines.EFSM_LTL"
begin

declare One_nat_def [simp del]

definition "half_price_vend = vend\<lparr>Guards:=[Ge (V (R 2)) (L (value.Int 50))]\<rparr>"

lemmas transitions = Drinks_Machine.transitions half_price_vend_def

text_raw\<open>\snip{drinksdef}{1}{2}{%\<close>
definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), select),
          ((1,1), coin),
          ((1,1), vend_fail),
          ((1,2), half_price_vend)
         |}"
text_raw\<open>}%endsnip\<close>

lemma valid_prefix: "\<exists>p. valid_prefix e (Some 0) <> p \<and> (\<forall>t. \<not> \<phi> (shift p t)) \<Longrightarrow> \<not> ltl_apply \<phi> e"
  apply (simp add: ltl_apply_def)
  using valid_prefix_ex_valid_trace by blast

lemma possible_steps_0: "possible_steps drinks 0 <> STR ''select'' [d] = {|(1, select)|}"
  by (simp add: possible_steps_def drinks_def ffilter_finsert select_def)

lemma possible_steps_1: "possible_steps drinks 1 r STR ''coin'' [c] = {|(1, coin)|}"
  by (simp add: possible_steps_def drinks_def ffilter_finsert transitions)

lemma possible_steps_2: "r $r 2 = Some (value.Int n) \<Longrightarrow> n \<ge> 50 \<Longrightarrow> n < 100 \<Longrightarrow> possible_steps drinks 1 r STR ''vend'' [] = {|(1, vend_fail), (2, half_price_vend)|}"
  by (simp add: possible_steps_def drinks_def ffilter_finsert transitions value_gt_def)

lemma "let x=[
    \<lparr>statename=Some 0, datastate = <>, action=(STR ''select'', [d]), output = p\<rparr>,
    \<lparr>statename=Some 1, datastate = <1 $r:= Some d, 2 $r:= Some (value.Int 0)>, action=(STR ''coin'', [value.Int 90]), output = []\<rparr>,
    \<lparr>statename=Some 1, datastate = <1 $r:= Some d, 2 $r:= Some (value.Int 90)>, action=(STR ''vend'', []), output = [Some (value.Int 90)]\<rparr>,
    \<lparr>statename=Some 2, datastate = <1 $r:= Some d, 2 $r:= Some (value.Int 90)>, action=(STR ''vend'', []), output = [Some d]\<rparr>
  ] in valid_prefix drinks (Some 0) <> x \<and> (\<forall>t. \<not> alw (\<lambda>xs. label (shd xs) = STR ''vend'' \<and> nxt (output_eq [Some d]) xs \<longrightarrow>
                      \<not>? value_gt (Some (value.Int 100)) (datastate (shd xs) $r 2) = trilean.true) (shift x t))"
  apply simp
  apply standard
   apply (rule valid_prefix.step_some)
   apply (simp add: possible_steps_0 select_def apply_updates_def)
   apply (rule valid_prefix.step_some)
   apply (simp add: possible_steps_1 coin_def apply_updates_def apply_outputs_def value_plus_def registers_update_twist)
   apply (rule valid_prefix.step_some)
   apply (simp add: possible_steps_2 half_price_vend_def apply_outputs_def apply_updates_def vend_def registers_update_twist)
   apply (rule valid_prefix.step_none)
     apply (simp add: possible_steps_def drinks_def ffilter_finsert)
    apply simp
   apply simp
  apply (rule allI)
  apply (simp add: not_alw_iff)
  apply (rule ev.step, simp)
  apply (rule ev.step, simp)
  by (rule ev.base, simp add: value_gt_def)

lemma "\<not>ltl_apply (alw (\<lambda>xs. (label (shd xs) = STR ''vend'' \<and>
             nxt (\<lambda>s. output (shd s) = [Some d]) xs) \<longrightarrow>
              \<not>? value_gt (Some (value.Int 100)) (datastate (shd xs) $r 2) = trilean.true)) drinks"
  apply (rule valid_prefix)
  apply (rule_tac x="[
    \<lparr>statename=Some 0, datastate = <>, action=(STR ''select'', [d]), output = p\<rparr>,
    \<lparr>statename=Some 1, datastate = <1 $r:= Some d, 2 $r:= Some (value.Int 0)>, action=(STR ''coin'', [value.Int 90]), output = []\<rparr>,
    \<lparr>statename=Some 1, datastate = <1 $r:= Some d, 2 $r:= Some (value.Int 90)>, action=(STR ''vend'', []), output = [Some (value.Int 90)]\<rparr>,
    \<lparr>statename=Some 2, datastate = <1 $r:= Some d, 2 $r:= Some (value.Int 90)>, action=(STR ''vend'', []), output = [Some d]\<rparr>
  ]" in exI)
  apply standard
   apply (rule valid_prefix.step_some)
   apply (simp add: possible_steps_0 select_def apply_updates_def)
   apply (rule valid_prefix.step_some)
   apply (simp add: possible_steps_1 coin_def apply_updates_def apply_outputs_def value_plus_def registers_update_twist)
   apply (rule valid_prefix.step_some)
   apply (simp add: possible_steps_2 half_price_vend_def apply_outputs_def apply_updates_def vend_def registers_update_twist)
   apply (rule valid_prefix.step_none)
     apply (simp add: possible_steps_def drinks_def ffilter_finsert)
    apply simp
   apply simp
  apply (rule allI)
  apply (simp add: not_alw_iff)
  apply (rule ev.step, simp)
  apply (rule ev.step, simp)
  by (rule ev.base, simp add: value_gt_def)

end