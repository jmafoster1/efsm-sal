theory Lift_Controller_LTL
imports liftController3 "EFSM.EFSM_LTL"
begin

declare One_nat_def [simp del]

lemma possible_steps_0: "possible_steps lift 0 r STR ''continit'' [] = {|(9, continit)|}"
  apply (simp add: possible_steps_singleton set_eq_iff lift_def)
  apply clarify
  apply (case_tac "a=0")
  by (auto simp add: continit_def)

lemma ltl_step_0_invalid: "e \<noteq> (STR ''continit'', []) \<Longrightarrow> ltl_step lift (Some 0) r e = (None, [], r)"
  apply (cases e)
  apply (simp del: ltl_step.simps)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def continit_def can_take)
  by auto

lemma implode_motorstop [simp]: "String.implode ''motorstop'' = STR ''motorstop''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_opendoor [simp]: "String.implode ''opendoor'' = STR ''opendoor''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma no_motor_stop: "s \<notin> {1, 2, 3, 4} \<Longrightarrow> possible_steps lift s r STR ''motorstop'' i = {||}"
  apply (simp add: possible_steps_empty lift_def)
  by (simp add: transitions)

lemma no_open_door: "s \<notin> {5, 6, 7, 8} \<Longrightarrow> possible_steps lift s r STR ''opendoor'' i = {||}"
  apply (simp add: possible_steps_empty lift_def)
  by (simp add: transitions)

lemma possible_steps_9_invalid: "(l, i) \<noteq> (STR ''return'', []) \<Longrightarrow> possible_steps lift 9 r l i = {||}"
  apply (simp add: possible_steps_empty lift_def)
  by (simp add: transitions can_take)

lemma possible_steps_9_invalid_r4: 
  assumes "r $ 4 \<notin> {Some (Num 1), Some (Num 2), Some (Num 3), Some (Num 4)}"
  shows "possible_steps lift 9 r l i = {||}"
  apply (simp add: possible_steps_empty lift_def)
  apply (simp add: transitions can_take)
  using assms by simp

declare nxt.simps [simp del]

lemma not_nxt: "nxt (not f) s \<Longrightarrow> \<not> nxt f s"
  by (simp add: nxt.simps)

lemma no_step_empty_out:
"possible_steps lift s r (fst (shd t)) (snd (shd t)) = {||} \<Longrightarrow>
fst (shd t) = STR ''opendoor'' \<Longrightarrow>
 \<not> nxt (output_eq [Some (Num n)]) (make_full_observation lift (Some s) r p t)"
    apply (rule not_nxt)
  apply (rule nxt_mono[of "output_eq []"])
   apply (case_tac "shd t")
   apply (simp add: nxt.simps)
  by simp

lemma return:
"r $ 4 = Some (Num n) \<Longrightarrow>
n \<in> {1, 2, 3, 4} \<Longrightarrow>
possible_steps lift 9 r (STR ''return'') [] = {|(nat n, return n)|}"
  apply (simp add: possible_steps_singleton lift_def set_eq_iff)
  apply clarsimp
  apply (case_tac "a=9")
   apply (simp add: transitions)
  by auto

lemma ltl_step_floor_invalid:
"n \<in> {1, 2, 3, 4} \<Longrightarrow>
fst e \<noteq> STR ''up'' \<Longrightarrow>
 fst e \<noteq> STR ''down'' \<Longrightarrow>
 fst e \<noteq> STR ''motorstop'' \<Longrightarrow>
ltl_step lift (Some n) r e = (None, [], r)"
  apply (cases e)
  apply (simp del: ltl_step.simps)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def)
  apply (simp add: transitions)
  by auto

lemma up_4: "fst e = STR ''up'' \<Longrightarrow> ltl_step lift (Some 4) r e = (None, [], r)"
  apply (cases e)
  apply (simp del: ltl_step.simps)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def)
  by (simp add: transitions)

lemma ltl_step_lift_deterministic:
  "ltl_step lift (Some n) r e = (Some aa, b, c) \<Longrightarrow>
   \<exists>t. possible_steps lift n r (fst e) (snd e) = {|(aa, t)|}"
  apply (insert deterministic_lift)
  apply (case_tac e)
  apply (simp only: deterministic_def size_le_1)
  by fastforce

lemma ltl_step_floor:
  "fst e \<noteq> STR ''motorstop'' \<Longrightarrow>
   n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<Longrightarrow>
   ltl_step lift (Some n) r e = (Some aa, b, c) \<Longrightarrow>
   aa \<in> {1, 2, 3, 4}"
  apply (cases e)
  apply (insert ltl_step_lift_deterministic[of n r e aa b c])
  apply simp
  apply (erule exE)
  apply simp
  apply (simp add: possible_steps_singleton set_eq_iff)
  apply (erule_tac x=n in allE)
  subgoal for a ba t
  apply (erule_tac x=aa in allE)
    apply (erule_tac x=t in allE)
    apply (case_tac "((n, aa), t) \<in> fset lift")
     defer apply simp
    apply simp
    apply (erule conjE)+
    apply (simp add: lift_def)
    apply (case_tac "n=1")
     apply (simp, metis motorstop1_def transition.select_convs(1))
    apply (case_tac "n=2")
     apply (simp, metis transition.select_convs(1) transitions(4))
    apply (case_tac "n=3")
     apply (simp, metis transition.select_convs(1) transitions(3))
    by (simp, metis transition.select_convs(1) transitions(2))
  done

lemma must_stop_to_open_aux2:
    assumes "\<exists> n r p t. j = (make_full_observation lift (Some n) r p t) \<and> (n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4)"
    shows "
       ((\<lambda>s. statename (shd s) \<noteq> Some 5 \<and>
             statename (shd s) \<noteq> Some 6 \<and> statename (shd s) \<noteq> Some 7 \<and> statename (shd s) \<noteq> Some 8) until
        (\<lambda>s. label (shd s) = STR ''motorstop'')) j"
  using assms apply coinduct
  apply (erule exE)+
  apply (case_tac "fst (shd t) = STR ''motorstop''")
   apply simp
  apply (erule conjE)
  apply (rule disjI2)
  apply simp
  apply standard apply auto[1]
  apply standard apply auto[1]
  apply standard apply auto[1]
  apply standard apply auto[1]
  apply (case_tac "ltl_step lift (Some n) r (shd t)")
  apply (case_tac a)
   apply simp
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "state_eq None"])
  using once_none_always_none apply blast
   apply simp
  apply simp
  subgoal for x n r p t a b c aa
    using ltl_step_floor[of "shd t" n r aa b c]
    by auto
  done

lemma must_stop_to_open_aux3:
    assumes "\<exists> n r p t. j = (make_full_observation lift (Some n) r p t) \<and> (n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4)"
    shows "
       ((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Num n)]))) until (\<lambda>s. label (shd s) = STR ''motorstop'')) j"
  using assms apply coinduct
  apply (erule exE)+
  apply (case_tac "fst (shd t) = STR ''motorstop''")
   apply simp
  apply (erule conjE)
  apply (rule disjI2)
  apply simp
  apply standard
   apply (simp add: nxt.simps ltl_step_floor_invalid)
  apply (case_tac "ltl_step lift (Some na) r (shd t)")
  apply (case_tac a)
   apply simp
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "nxt (output_eq [])"])
    apply (simp add: no_output_none_nxt)
   apply (simp add: nxt.simps)
  apply simp
  subgoal for x n r p t a b c aa
    using ltl_step_floor[of "shd t" n r aa b c]
    by auto
  done

lemma must_stop_to_open_aux1:
    assumes "\<exists> s r p t. j = (make_full_observation lift (Some 9) r p t)"
    shows "((\<lambda>s. statename (shd s) \<noteq> Some 5 \<and>
          statename (shd s) \<noteq> Some 6 \<and> statename (shd s) \<noteq> Some 7 \<and> statename (shd s) \<noteq> Some 8) until
     (\<lambda>s. label (shd s) = STR ''motorstop'')) j"
  using assms apply coinduct
  apply (erule exE)+
  apply (case_tac "shd t")
  apply (case_tac "label (shd x) = STR ''return'' \<and> inputs (shd x) = []")
   defer
   apply (rule disjI2)
   apply (simp add: possible_steps_9_invalid)
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "state_eq None"])
  using once_none_always_none apply blast
   apply simp
  apply simp
  apply (case_tac "r $ 4 \<notin> {Some (Num 1), Some (Num 2), Some (Num 3), Some (Num 4)}")
   apply (simp add: possible_steps_9_invalid_r4)
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "state_eq None"])
  using once_none_always_none apply blast
   apply simp
  apply (case_tac "\<exists>n. r $ 4 = Some (Num n) \<and> n \<in> {int 1, int 2, int 3, int 4}")
   defer apply auto[1]
  apply (erule exE)
  apply (case_tac "possible_steps lift 9 r (STR ''return'') [] = {|(nat n, return n)|}")
   defer apply (simp add: return)
  apply simp
  apply (rule disjI2)
  apply (rule must_stop_to_open_aux2)
  apply (rule_tac x="nat n" in exI)
  by auto

lemma possible_steps_opendoor_invalid_state:
  "sa \<noteq> 5 \<Longrightarrow>
   sa \<noteq> 6 \<Longrightarrow>
   sa \<noteq> 7 \<Longrightarrow>
   sa \<noteq> 8 \<Longrightarrow>
   possible_steps lift sa ra STR ''opendoor'' b = {||}"
  apply (simp add: possible_steps_empty lift_def)
  by (simp add: transitions)

lemma combine:
"((p aand p') until  q) s \<Longrightarrow>
 (p until q) s \<Longrightarrow>
 (p' until q) s"
  by (simp add: until_mono)

lemma alw_conj: "alw p s \<Longrightarrow> alw q s \<Longrightarrow> alw (p aand q) s"
  by (simp add: alw_iff_sdrop)

lemma must_stop_to_open_aux1a:
    assumes "\<exists> s r p t. j = (make_full_observation lift (Some 9) r p t)"
    shows "((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Num n)]))) until (label_eq ''motorstop'')) j"
  using assms apply coinduct
  apply (erule exE)+
  apply (case_tac "shd t")
  apply (case_tac "label (shd x) = STR ''return'' \<and> inputs (shd x) = []")
   defer
   apply (rule disjI2)
   apply (simp add: possible_steps_9_invalid nxt.simps)
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "nxt (output_eq [])"])
  using no_output_none_nxt apply blast
   apply (simp add: nxt.simps)
  apply (case_tac "r $ 4 \<notin> {Some (Num 1), Some (Num 2), Some (Num 3), Some (Num 4)}")
   apply (simp add: possible_steps_9_invalid_r4)
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "nxt (output_eq [])"])
  using no_output_none_nxt apply blast
   apply (simp add: nxt.simps)
  apply (case_tac "\<exists>n. r $ 4 = Some (Num n) \<and> n \<in> {int 1, int 2, int 3, int 4}")
   defer apply auto[1]
  apply (erule exE)
  apply (case_tac "possible_steps lift 9 r (STR ''return'') [] = {|(nat na, return na)|}")
  defer apply (simp add: return)
  apply simp
  apply (rule disjI2)
  subgoal for x r p t a b na
    using must_stop_to_open_aux3[of "(make_full_observation lift (Some (nat na)) (apply_updates [] (join_ir [] r) r) [] (stl t))" n]
    apply (simp add: nxt.simps)
    by fastforce
  done

lemma aux_aux:
"((\<lambda>xs. statename (shd xs) \<notin> {Some o1, Some o2, Some o3, Some o4} \<and>
         \<not> (label_eq ''opendoor'' xs \<and> nxt (output_eq [Some (Num n)]) xs)) until
   label_eq ''motorstop'')
   (watch lift t)"
  apply (case_tac "shd t \<noteq> (STR ''continit'', [])")
   apply (rule alw_implies_until)
   apply (cases "shd t")
   apply coinduction
   apply (simp add: ltl_step_0_invalid nxt.simps del: ltl_step.simps)
   apply (rule disjI2, rule alw_mono[of "state_eq None aand nxt (output_eq [])"])
    apply (rule alw_conj)
  using once_none_always_none apply blast
  using no_output_none_nxt apply blast
   apply (simp add: nxt.simps)
  apply (rule UNTIL.step)
   apply simp
  apply (simp add: possible_steps_0)
  using must_stop_to_open_aux1a[of "(make_full_observation lift (Some 9) (apply_updates (Updates continit) Map.empty <>)
       (apply_outputs (Outputs continit) Map.empty) (stl t))" n]
  apply (simp add: nxt.simps)


  sorry

lemma aux:
  "((\<lambda>s. statename (shd s) \<notin> {Some o1, Some o2, Some o3, Some o4}) until (label_eq ''motorstop'')) (watch lift t) \<Longrightarrow>
   ((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Num n)]))) until (label_eq ''motorstop'')) (watch lift t)"
  using combine[of
"(\<lambda>s. statename (shd s) \<notin> {Some o1, Some o2, Some o3, Some o4})"
"(not (label_eq ''opendoor'' aand nxt (output_eq [Some (Num n)])))"
"(label_eq ''motorstop'')"
"(watch lift t)"
    ]
aux_aux by simp

declare nxt.simps [simp]

(* We cannot open the door until we have stopped the motor (not global)*)
lemma must_stop_to_open:
  shows "((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Num n)]))) until (label_eq ''motorstop'')) (watch lift t)"
  apply (rule UNTIL.step)
   apply (case_tac "shd t")
  apply (simp del: ltl_step.simps add: ltl_step_0_invalid)
  apply (case_tac "shd t = (STR ''continit'', [])")
   defer
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "nxt (output_eq [])"])
    apply (simp add: ltl_step_0_invalid)
  using no_output_none_nxt apply blast
   apply simp
  apply (simp add: possible_steps_0 continit_def apply_updates_def)
  using must_stop_to_open_aux1a[of "(make_full_observation lift (Some 9) <1 $:= Some (EFSM.Str ''true'')> [] (stl t))"]
  by fastforce

(* We can use the never_on_a_floor lemma maybe *)
(* We could also use the \<exists> technique as above and do a case tac for every state. That might work actually. *)

end