theory Lift_Controller_LTL
imports Lift_Controller "Extended_Finite_State_Machines.EFSM_LTL"
begin

declare One_nat_def [simp del]

lemma possible_steps_0: "possible_steps lift 0 r STR ''continit'' [] = {|(9, continit)|}"
  apply (simp add: possible_steps_singleton set_eq_iff lift_def)
  apply clarify
  apply (case_tac "a=0")
  by (auto simp add: continit_def)

lemma ltl_step_0: "ltl_step lift (Some 0) r (STR ''continit'', []) = (Some 9, [], r(1 $:= Some (Str ''true'')))"
  by (simp add: possible_steps_0 continit_def apply_updates_def)

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
  assumes "r $ 4 \<notin> {Some (value.Int 1), Some (value.Int 2), Some (value.Int 3), Some (value.Int 4)}"
  shows "possible_steps lift 9 r l i = {||}"
  apply (simp add: possible_steps_empty lift_def)
  apply (simp add: transitions can_take value_eq_true)
  using assms by simp

declare nxt.simps [simp del]

lemma not_nxt: "nxt (not f) s \<Longrightarrow> \<not> nxt f s"
  by (simp add: nxt.simps)

lemma no_step_empty_out:
"possible_steps lift s r (fst (shd t)) (snd (shd t)) = {||} \<Longrightarrow>
fst (shd t) = STR ''opendoor'' \<Longrightarrow>
 \<not> nxt (output_eq [Some (Str ''true''), Some (value.Int n)]) (make_full_observation lift (Some s) r p t)"
    apply (rule not_nxt)
  apply (rule nxt_mono[of "output_eq []"])
   apply (case_tac "shd t")
   apply (simp add: nxt.simps)
  by simp

lemma return:
"r $ 4 = Some (value.Int n) \<Longrightarrow>
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
       ((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Str ''true''), Some (value.Int n)]))) until (\<lambda>s. label (shd s) = STR ''motorstop'')) j"
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
  apply (case_tac "r $ 4 \<notin> {Some (value.Int 1), Some (value.Int 2), Some (value.Int 3), Some (value.Int 4)}")
   apply (simp add: possible_steps_9_invalid_r4)
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "state_eq None"])
  using once_none_always_none apply blast
   apply simp
  apply (case_tac "\<exists>n. r $ 4 = Some (value.Int n) \<and> n \<in> {int 1, int 2, int 3, int 4}")
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
    assumes "\<exists> r p t. j = (make_full_observation lift (Some 9) r p t)"
    shows "((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Str ''true''), Some (value.Int n)]))) until (label_eq ''motorstop'')) j"
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
  apply (case_tac "r $ 4 \<notin> {Some (value.Int 1), Some (value.Int 2), Some (value.Int 3), Some (value.Int 4)}")
   apply (simp add: possible_steps_9_invalid_r4)
   apply (rule disjI2)
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "nxt (output_eq [])"])
  using no_output_none_nxt apply blast
   apply (simp add: nxt.simps)
  apply (case_tac "\<exists>n. r $ 4 = Some (value.Int n) \<and> n \<in> {int 1, int 2, int 3, int 4}")
   defer apply auto[1]
  apply (erule exE)
  apply (case_tac "possible_steps lift 9 r (STR ''return'') [] = {|(nat na, return na)|}")
  defer apply (simp add: return)
  apply simp
  apply (rule disjI2)
  subgoal for x r p t a na
    using must_stop_to_open_aux3[of "(make_full_observation lift (Some (nat na)) (apply_updates [] (join_ir [] r) r) [] (stl t))" n]
    apply (simp add: nxt.simps)
    by fastforce
  done

(* We cannot open the door until we have stopped the motor (not global)*)
(* This does not hold globally *)
lemma must_stop_to_open:
  shows "((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Str ''true''), Some (value.Int n)]))) until (label_eq ''motorstop'')) (make_full_observation lift (Some 0) r p t)"
  apply (rule UNTIL.step)
   apply (case_tac "shd t")
  apply (simp del: ltl_step.simps add: ltl_step_0_invalid nxt.simps)
  apply (case_tac "shd t = (STR ''continit'', [])")
   defer
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "nxt (output_eq [])"])
    apply (simp add: ltl_step_0_invalid nxt.simps)
  using no_output_none_nxt apply blast
   apply (simp add: nxt.simps)
  apply (simp add: possible_steps_0 continit_def apply_updates_def)
  using must_stop_to_open_aux1a[of "(make_full_observation lift (Some 9) (r(1 $:= Some (EFSM.Str ''true''))) [] (stl t))"]
  by fastforce

lemma must_stop_to_open: "((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Str ''true''), Some (value.Int n)]))) until (label_eq ''motorstop'')) (watch lift t)"
oops

(* THIS IS NOT TRUE *)
lemma must_stop_to_open_false: "alw ((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Str ''true''), Some (value.Int n)]))) until (label_eq ''motorstop'')) (watch lift i)"
  oops

lemma ltl_step_9_invalid: "\<not>(\<exists>n. r $ 4 = Some (value.Int n) \<and> n \<in> {1, 2, 3, 4}) \<Longrightarrow> ltl_step lift (Some 9) r e = (None, [], r)"
  apply (cases e)
  apply (simp del: ltl_step.simps)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def)
  apply (simp add: transitions can_take value_eq_true)
  by auto

declare ltl_step.simps [simp del]

lemma label_motorstop:
"(ffilter (\<lambda>((origin, dest), t). Label t = STR ''motorstop'') lift) =
{|((f4, o4), motorstop4),
  ((f3, o3), motorstop3),
  ((f2, o2), motorstop2),
  ((f1, o1), motorstop1)
|}"
  apply (simp add: lift_def Abs_ffilter set_eq_iff)
  apply clarify
   apply (simp add: transitions)
  apply (case_tac "a=1")
   apply (simp add: transitions)
   apply auto[1]
  apply (case_tac "a=2")
   apply (simp add: transitions)
   apply auto[1]
  apply (case_tac "a=3")
   apply (simp add: transitions)
   apply auto[1]
  apply (case_tac "a=4")
   apply (simp add: transitions)
  by auto

lemma ltl_step_motorstop:
"r $ 1 = Some (EFSM.Str ''true'') \<Longrightarrow>
 n \<in> {1, 2, 3, 4} \<Longrightarrow>
 ltl_step lift (Some n) r (STR ''motorstop'', [EFSM.Str ''true'', EFSM.Str ''true'']) = (Some (n + 4), [Some (value.Int 0), Some (value.Int n), Some (Str ''true'')], r)"
  apply (rule ltl_step_singleton)
  apply (rule_tac x="motorstop n" in exI)
  apply (simp add: apply_updates_def apply_outputs_def)
   apply (simp add: possible_steps_alt3 split_label label_motorstop)
   apply (simp add: Abs_ffilter set_eq_iff)
  apply clarify
   apply (case_tac "a=1")
    apply simp
    apply standard
     apply (simp add: transitions can_take)
   apply (simp add: transitions can_take apply_guards_def)
   apply (case_tac "a=2")
    apply standard
     apply (simp add: transitions can_take)
    apply (simp add: transitions can_take apply_guards_def)
   apply (case_tac "a=3")
    apply standard
     apply (simp add: transitions can_take)
    apply (simp add: transitions can_take apply_guards_def)
  apply (simp add: transitions can_take apply_guards_def)
  by auto

lemma ltl_step_motorstop_invalid_r1:
"r $ 1 \<noteq> Some (EFSM.Str ''true'') \<Longrightarrow>
 n \<in> {1, 2, 3, 4} \<Longrightarrow>
 ltl_step lift (Some n) r (STR ''motorstop'', [EFSM.Str ''true'', EFSM.Str ''true'']) = (None, [], r)"
  apply (rule ltl_step_none)
  apply (rule possible_steps_empty_guards_false)
  apply (simp add: label_motorstop)
  by (simp add: can_take transitions apply_guards_def Str_def value_eq_true)

lemma alw_must_stop_to_open_end:
  "alw ((\<lambda>xs. label (shd xs) = STR ''opendoor'' \<longrightarrow> \<not> nxt (output_eq [Some (Str ''true''), Some (value.Int n)]) xs) until
            (\<lambda>s. label (shd s) = STR ''motorstop''))
        (make_full_observation lift None r [] t)"
  apply (rule alw_mono[of "alw (output_eq [])"])
   apply (simp add: no_output_none_if_empty)
  apply (rule alw_implies_until)
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (meson alw_nxt nxt_alw)
  by (simp add: nxt.simps)


(* This is the lemma I'm having trouble with *)
(* That's because it's not true!*)
lemma alw_must_stop_to_open:
    assumes "\<exists>s r p t. j = (make_full_observation lift (Some s) r p t) \<and> s \<notin> {5, 6, 7, 8}"
    shows "alw ((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Str ''true''), Some (value.Int n)]))) until (label_eq ''motorstop'')) j"
  using assms apply coinduct

  apply (erule exE)
  apply (case_tac "s=9")

  apply simp
  apply standard
  using must_stop_to_open_aux1a apply simp
   apply (erule exE)+
    apply (case_tac "\<exists>n. r $ 4 = Some (value.Int n) \<and> n \<in> {1, 2, 3, 4}")
    prefer 2
     apply (case_tac "shd t")
  using ltl_step_9_invalid apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "alw (output_eq [])"])
    apply (simp add: no_output_none_if_empty)
     apply (rule alw_implies_until)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (meson alw_nxt nxt_alw)
     apply (simp add: nxt.simps)
    apply (case_tac "shd t = (STR ''return'', [])")
      prefer 2
      apply (case_tac "shd t")
      apply (simp add:  possible_steps_9_invalid ltl_step.simps alw_must_stop_to_open_end)
     apply (simp add: nxt.simps)
     apply (erule exE)+
    apply (simp add: ltl_step.simps return apply_updates_def)
    apply (case_tac "\<exists>ta. stl t = ta")
      prefer 2 apply simp
     apply fastforce

    apply (case_tac "s = 0")
     apply simp
     apply standard
    using must_stop_to_open apply auto[1]
     apply (erule exE)+
     apply (case_tac "shd t = (STR ''continit'', [])")
      apply (simp add: ltl_step_0)
      apply fastforce
     apply (simp add: ltl_step_0_invalid alw_must_stop_to_open_end)

    apply (case_tac "s \<in> {1, 2, 3, 4}")
     apply simp
     apply standard
    using must_stop_to_open_aux3 apply fastforce
     apply (erule conjE)
     apply (erule exE)+
     apply (case_tac "shd t = (STR ''motorstop'', [EFSM.Str ''true'', EFSM.Str ''true''])")
      apply (case_tac "r $ 1 \<noteq> Some (EFSM.Str ''true'')")
       apply (simp add: ltl_step_motorstop_invalid_r1 alw_must_stop_to_open_end)
      apply (simp add: ltl_step_motorstop)
      apply (rule disjI2)
    oops

lemma bad_step:
  assumes "ltl_step lift (Some s) r (shd t) = (None, [], r)"
shows "((ev (nxt ((label_eq ''opendoor '') aand (nxt (output_eq [Some(Str ''true''), Some n]))))) impl
       ((not (nxt (label_eq ''opendoor ''))) until(((label_eq ''motorstop'') or (nxt (output_eq [Some(Str ''true''), Some n]))))))
      (make_full_observation lift (Some s) r p t)"
proof-
  have aux: "\<not>ev (nxt (\<lambda>xs. label_eq ''opendoor '' xs \<and> nxt (output_eq [Some (EFSM.Str ''true''), Some n]) xs))
     (\<lparr>statename = Some s, datastate = r, action = shd t, output = p\<rparr> ## make_full_observation lift None r [] (stl t))"
    apply (simp add: not_ev_iff)
    apply (rule alw_mono[of "nxt (nxt (output_eq []))"])
     apply (simp add: no_output_none_nxt nxt.simps nxt_alw)
    by (simp add: nxt.simps)
  show ?thesis
    using assms
    by (simp add: make_full_observation.ctr[of lift "Some s"] aux)
qed

declare nxt.simps [simp]

lemma ltl_step_9_invalid_label:
"e \<noteq> (STR ''return'', []) \<Longrightarrow>
  ltl_step lift (Some 9) r e = (None, [], r)"
  apply (case_tac e, simp)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def)
  by (simp add: transitions can_take)

lemma opendoor_9: "ltl_step lift (Some 9) r (STR ''opendoor'', b) = (None, [], r)"
  apply (rule ltl_step_none)
  by (simp add: possible_steps_empty lift_def transitions)

lemma opendoor_invalid: "s \<notin> {5, 6, 7, 8} \<Longrightarrow> ltl_step lift (Some s) r (STR ''opendoor'', b) = (None, [], r)"
  apply (rule ltl_step_none)
  by (simp add: possible_steps_empty lift_def transitions)

lemma opendoor_invalid_nat: "s \<notin> {5, 6, 7, 8} \<Longrightarrow> ltl_step lift (Some (nat s)) r (STR ''opendoor'', b) = (None, [], r)"
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def transitions)
  by auto

lemma not_ev: "ev p s \<Longrightarrow> alw (not p) s \<Longrightarrow> False"
  by (metis alw_iff_sdrop sdrop_wait)

lemma stop_at_None: "alw (\<lambda>xs. label (shd (stl xs)) = a \<longrightarrow> output (shd (stl (stl xs))) \<noteq> [Some (EFSM.Str ''true''), Some n])
        (make_full_observation lift None r [] s)"
  apply (rule alw_mono[of "alw (output_eq [])"])
   apply (simp add: no_output_none_if_empty)
  by fastforce

lemma ev_step: "ev p s = p s \<or> ev p (stl s)"
  using ev.simps by auto

lemma prem_ignore_fst:
  "a \<noteq> STR ''opendoor'' \<Longrightarrow>
 ev (\<lambda>a. label (shd (stl a)) = STR ''opendoor'' \<and> output_eq [Some (EFSM.Str ''true''), Some n] (stl (stl a)))
        (ss ## make_full_observation lift (Some s') r' p' ((a, b) ## x2)) =
 ev (\<lambda>a. label (shd (stl a)) = STR ''opendoor'' \<and> output_eq [Some (EFSM.Str ''true''), Some n] (stl (stl a)))
        (make_full_observation lift (Some s') r' p' ((a, b) ## x2))"
  apply standard
   apply (simp add: ev_Stream)
  by auto

lemma prem_stop_at_none_scons: "\<not> ev (\<lambda>a. label (shd (stl a)) = STR ''opendoor'' \<and> output_eq [Some (EFSM.Str ''true''), Some n] (stl (stl a)))
        (ss ## make_full_observation lift None r [] t)"
  apply (simp add: not_ev_iff)
  apply (coinduction)
  by (simp add: ltl_step.simps stop_at_None)

lemma prem_stop_at_none: "\<not> ev (\<lambda>a. label (shd (stl a)) = STR ''opendoor'' \<and> output_eq [Some (EFSM.Str ''true''), Some n] (stl (stl a)))
        (make_full_observation lift None r [] t)"
  apply (simp add: not_ev_iff)
  apply (rule alw_mono[of "alw (output_eq [])"])
   apply (simp add: no_output_none_if_empty)
  by fastforce

lemma label_up:
"ffilter (\<lambda>((origin, dest), t). Label t = STR ''up'') lift = {|
    ((f3, f4), up34stop),
    ((f2, f3), up23stop),
    ((f2, f3), up23),
    ((f1, f2), up12stop),
    ((f1, f2), up12)
|}"
  apply (simp add: Abs_ffilter lift_def set_eq_iff)
  apply clarify
  apply (case_tac "a=1")
   apply (simp add: transitions) apply auto[1]
  apply (case_tac "a=2")
   apply (simp add: transitions) apply auto[1]
  apply (case_tac "a=3")
   apply (simp add: transitions) apply auto[1]
  apply (case_tac "a=4")
   apply (simp add: transitions) apply auto[1]
  apply (simp add: transitions)
  by auto

lemma not_motorstop: "Label (motorstop n) = l \<and> can_take_transition (motorstop n) i r \<Longrightarrow>
(l, i) = (STR ''motorstop'', [EFSM.Str ''true'', EFSM.Str ''true''])"
  apply (simp add: can_take apply_guards_def value_eq_true)
  apply clarsimp
  apply (case_tac "r $ 1 = Some (EFSM.Str ''true'')")
   apply (case_tac "i ! 0 = (EFSM.Str ''true'')")
    apply (case_tac "i ! 1 = (EFSM.Str ''true'')")
     apply simp
     apply (case_tac i) apply simp
     apply (case_tac list) apply simp
  by auto

lemma not_motorstop_step_state:
  "s \<in> {1, 2, 3, 4} \<Longrightarrow>
   e \<noteq> (STR ''motorstop'', [EFSM.Str ''true'', EFSM.Str ''true'']) \<Longrightarrow>
   ltl_step lift (Some s) r e = (Some s', p, r') \<Longrightarrow>
   s' \<in> {1, 2, 3, 4}"
  using ltl_step_lift_deterministic[of s r e s' p r']
  apply simp
  apply (erule exE)
  apply (simp add: possible_steps_alt3 Abs_ffilter lift_def set_eq_iff)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=t in allE)
  apply (erule disjE)
   apply simp
   apply (erule conjE)
   apply (erule disjE)
    apply (simp add: motorstop1_def)
  using not_motorstop apply auto[1]
   apply auto[1]
  apply (erule disjE)
   apply simp
   apply (erule conjE)
   apply (erule disjE)
    apply (simp add: motorstop2_def)
  using not_motorstop apply auto[1]
   apply auto[1]
  apply (erule disjE)
   apply simp
   apply (erule conjE)
   apply (erule disjE)
    apply (simp add: motorstop3_def)
  using not_motorstop apply auto[1]
   apply auto[1]
   apply simp
   apply (erule conjE)
   apply (erule disjE)
    apply (simp add: motorstop4_def)
  using not_motorstop by auto

lemma ltl_step_state_none: "(ltl_step lift (Some s) r e = (None, b, c)) \<Longrightarrow> b = [] \<and> c = r"
  apply (cases e)
  apply (simp add: ltl_step.simps Let_def)
  apply (case_tac "possible_steps lift s r a ba = {||}")
   apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps lift s r a ba")
  by simp

lemma opendoor_moving:
  "s \<in> {1, 2, 3, 4} \<Longrightarrow> ltl_step lift (Some s) r (STR ''opendoor'', ba) = (None, [], r)"
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def)
  apply (simp add: transitions)
  by auto

lemma label_opendoor: "ffilter (\<lambda>((origin, dest), t). Label t = STR ''opendoor'') lift =
       {|((5, 5), opendoor1), ((6, 6), opendoor2), ((7, 7), opendoor3), ((8, 8), opendoor4)|}"
  apply (simp add: Abs_ffilter set_eq_iff lift_def)
  apply clarify
  apply (case_tac "a=5")
   apply (simp add: transitions)
   apply auto[1]
  apply (case_tac "a=6")
   apply (simp add: transitions)
   apply auto[1]
  apply (case_tac "a=7")
   apply (simp add: transitions)
   apply auto[1]
  apply (case_tac "a=8")
   apply (simp add: transitions)
   apply auto[1]
  apply (simp add: transitions)
  by auto

lemma ltl_step_opendoor:
  "s \<in> {5, 6, 7, 8} \<Longrightarrow> ltl_step lift (Some s) r (STR ''opendoor'', [EFSM.Str ''true'']) = (Some s, [Some (Str ''true''), Some (value.Int (s-4))], r)"
  apply (rule ltl_step_some[of _ _ _ _ _ s "opendoor (s-4)"])
    apply (simp add: possible_steps_alt3 split_label label_opendoor transitions Abs_ffilter set_eq_iff)
    apply (simp add: can_take)
    apply clarify
    apply auto[1]
   apply (simp add: apply_outputs_def)
  by (simp add: apply_updates_def)

lemma possible_steps_lift_fset:
  "possible_steps lift s r STR ''opendoor'' b \<noteq> {||} \<Longrightarrow>
   \<exists>s' t. possible_steps lift s r STR ''opendoor'' b = {|(s', t)|}"
  by (meson deterministic_alt_aux deterministic_def deterministic_lift possible_steps_alt)

lemma can_take_opendoors:
"can_take_transition (opendoor (int (s - 4))) i r = (i=[Str ''true''])"
  apply (simp add: can_take)
  by (case_tac i, auto)

lemma output_opendoors:
  "value.Int (int (s - 4)) \<noteq> n \<Longrightarrow>
  fst e = STR ''opendoor'' \<Longrightarrow>
  fst (snd (ltl_step lift (Some s) r e)) \<noteq> [Some (EFSM.Str ''true''), Some n]"
  apply (cases e)
  apply (simp add: ltl_step.simps)
  apply (case_tac "possible_steps lift s r STR ''opendoor'' b = {||}")
   apply simp
  apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps lift s r STR ''opendoor'' b")
  apply simp
  subgoal for l i s' t
    apply (insert possible_steps_lift_fset[of s r i])
    apply simp
    apply (erule exE)+
    apply (simp add: possible_steps_singleton set_eq_iff can_take[symmetric])
    apply (erule_tac x=s in allE)
    apply (erule_tac x=s' in allE)
    apply (erule_tac x=t in allE)
    apply (simp add: lift_def)
    apply (erule conjE)+
    apply (erule disjE, simp add: transitions)+
     apply (simp add: can_take apply_outputs_def)
    apply (erule disjE, simp add: transitions)+
     apply (simp add: can_take apply_outputs_def)
    apply (erule disjE, simp add: transitions)+
     apply (simp add: can_take apply_outputs_def)
    apply (erule disjE, simp add: transitions)+
     apply (simp add: can_take apply_outputs_def)
    apply (erule disjE, simp add: transitions)+
    apply (simp add: can_take apply_outputs_def)
    by (simp add: transitions)
  done

lemma ltl_step_ocd_invalid:
  "e \<noteq> (STR ''opendoor'', [EFSM.Str ''true'']) \<Longrightarrow>
   e \<noteq> (STR ''startsearch'', [EFSM.Str ''true'', EFSM.Str ''false'']) \<Longrightarrow>
   s \<in> {5, 6, 7, 8} \<Longrightarrow>
   ltl_step lift (Some s) r e = (None, [], r)"
  apply (cases e, simp)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty lift_def)
  apply (erule disjE)
   apply (simp add: can_take transitions apply_guards_def)
   apply (case_tac b, simp)
   apply (case_tac list, simp)
    apply auto[1]
  apply simp
  apply (erule disjE)
   apply (simp add: can_take transitions apply_guards_def)
   apply (case_tac b, simp)
   apply (case_tac list, simp)
    apply auto[1]
  apply simp
  apply (erule disjE)
   apply (simp add: can_take transitions apply_guards_def)
   apply (case_tac b, simp)
   apply (case_tac list, simp)
    apply auto[1]
  apply simp
   apply (simp add: can_take transitions apply_guards_def)
   apply (case_tac b, simp)
   apply (case_tac list, simp)
  by auto

lemma possible_steps_origin: "possible_steps e s r l i = possible_steps (ffilter (\<lambda>((origin, dest), t). origin = s) e) s r l i"
  apply (simp add: possible_steps_def)
  apply (rule arg_cong[of _ _ "fimage (\<lambda>((origin, dest), t). (dest, t))"])
  apply (simp add: ffilter_def Abs_fset_inverse)
  apply (rule arg_cong[of _ _ Abs_fset])
  by auto

lemma possible_steps_label: "possible_steps e s r l i = possible_steps (ffilter (\<lambda>((origin, dest), t). Label t = l) e) s r l i"
  apply (simp add: possible_steps_def)
  apply (rule arg_cong[of _ _ "fimage (\<lambda>((origin, dest), t). (dest, t))"])
  apply (simp add: ffilter_def Abs_fset_inverse)
  apply (rule arg_cong[of _ _ Abs_fset])
  by auto

lemma fimage_member: "(x |\<in>| fimage f s) = (\<exists>x'. x' |\<in>| s \<and> f x' = x)"
  by auto

lemma ltl_step_startsearch:
  assumes "s \<in> {5, 6, 7, 8}"
  shows "ltl_step lift (Some s) r (STR ''startsearch'', [EFSM.Str ''true'', EFSM.Str ''false'']) = (Some 9, [], r)"
proof-
  have possible_s: "s \<in> {5, 6, 7, 8} = (s = 5 \<or> s = 6 \<or> s = 7 \<or> s = 8)"
    by simp
  (*Takes ~30s*)
  have startsearch: "ffilter (\<lambda>((origin, dest), t). Label t = STR ''startsearch'') lift =
  {|((5, 9), startsearch),
    ((6, 9), startsearch),
    ((7, 9), startsearch),
    ((8, 9), startsearch)|}"
    apply standard
    defer
     apply (simp add: lift_def)
    apply (rule fsubsetI)
    apply (simp only: ffmember_filter)
    apply (case_tac "x |\<in>| lift")
     defer apply simp
    apply simp
    apply (case_tac x)
    apply simp
    apply (simp add: lift_def)
    apply clarsimp
    apply (simp add: transitions)
    subgoal for s s' t
      apply (case_tac "t = startsearch")
       apply auto[1]
      by auto
    done
  have ffilter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and>
         Label t = STR ''startsearch'' \<and>
         Suc (Suc 0) = Arity t \<and> apply_guards (Guards t) (join_ir [EFSM.Str ''true'', EFSM.Str ''false''] r))
     {|((5, 9), startsearch), ((6, 9), startsearch), ((7, 9), startsearch), ((8, 9), startsearch)|} =
    ffilter (\<lambda>((origin, dest), t). origin = s) {|((5, 9), startsearch), ((6, 9), startsearch), ((7, 9), startsearch), ((8, 9), startsearch)|}"
    apply standard
     apply auto[1]
    apply (rule fsubsetI)
    apply (case_tac x)
    apply clarsimp
    apply (case_tac "bc = startsearch")
     apply (simp add: apply_guards_def)
    by simp
  show ?thesis
    apply (rule ltl_step_some[of _ _ _ _ _ 9 startsearch])
    defer apply simp
     apply (simp add: apply_updates_def)
    using possible_s assms
    apply (simp add: possible_steps_label[of lift] startsearch)
    apply (simp add: possible_steps_def)
    apply standard
     apply auto[1]
    apply (rule fsubsetI)
    by (simp add: fimage_member apply_guards_def)
qed

lemma possible_steps_lift: "possible_steps lift s r a ba \<noteq> {||} \<Longrightarrow>
       \<exists>aa t. possible_steps lift s r a ba = {|(aa, t)|}"
  using deterministic_alt deterministic_lift possible_steps_alt by blast

lemma ltl_step_Some_lift: "(ltl_step lift (Some s) r e = (Some aa, b, c)) =
       (\<exists>t. possible_steps lift s r (fst e) (snd e) = {|(aa, t)|} \<and> evaluate_outputs t (snd e) r = b \<and> evaluate_updates t (snd e) r = c)"
  apply standard
   prefer 2 apply (simp add: ltl_step_singleton)
  apply (cases e)
  apply (simp add: ltl_step.simps Let_def)
  apply (case_tac "possible_steps lift s r a ba = {||}")
   apply simp
  apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps lift s r a ba")
  apply simp
  apply (rule_tac x=baa in exI)
  using possible_steps_lift by fastforce

lemma ltl_step_floor_output:
  "s \<in> {1, 2, 3, 4} \<Longrightarrow> fst (snd (ltl_step lift (Some s) r e)) \<noteq> [Some (EFSM.Str ''true''), Some n]"
  apply (case_tac "ltl_step lift (Some s) r e")
  apply simp
  apply (case_tac a)
   apply (metis list.simps(3) ltl_step_state_none)
  apply (simp add: ltl_step_Some_lift)
  apply (erule_tac exE)
  apply (erule conjE)+
  apply (simp add: possible_steps_singleton set_eq_iff)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=aa in allE)
  apply (erule_tac x=t in allE)
  apply simp
  apply (erule conjE)+
  subgoal for a b c aa t
    apply (simp add: eq_commute[of "evaluate_outputs t (snd e) r" b])
    apply (simp add: lift_def apply_outputs_def Str_def)
    apply (erule disjE)
     apply (simp add: transitions)
     apply (erule disjE, simp)
     apply (erule disjE, simp)
     apply simp
    apply (erule disjE)
     apply (simp add: transitions)
    apply (erule disjE)
     apply (simp add: transitions)
     apply (erule disjE, simp)
     apply auto[1]
     apply (erule disjE)
     apply (simp add: transitions)
     apply (erule disjE)
     apply (simp add: transitions)
     apply (erule disjE, simp)
     apply auto[1]
     apply (simp add: transitions)
     apply (erule disjE, simp)
    by auto
  done

lemma invalid_state:
  "s \<noteq> 0 \<Longrightarrow>
   s \<noteq> 5 \<and> s \<noteq> 6 \<and> s \<noteq> 7 \<and> s \<noteq> 8 \<Longrightarrow>
   s \<noteq> 1 \<and> s \<noteq> 2 \<and> s \<noteq> 3 \<and> s \<noteq> 4 \<Longrightarrow>
   s \<noteq> 9 \<Longrightarrow>
   ltl_step lift (Some s) r e = (None, [], r)"
  apply (cases e, simp, rule ltl_step_none)
  by (simp add: possible_steps_empty lift_def)

text_raw\<open>\snip{alwMustStopToOpenAux}{1}{2}{%\<close>
lemma alw_must_stop_to_open_aux:
  assumes "\<exists>s r p t. j= make_full_observation lift (Some s) r p t"
  shows "((ev (nxt ((label_eq ''opendoor'') aand
              (nxt (output_eq [Some(Str ''true''), Some n]))))) impl
         ((not (nxt (label_eq ''opendoor'' aand
          (nxt (output_eq [Some(Str ''true''), Some n]))))) until
         (((label_eq ''motorstop'') or (nxt (output_eq [Some(Str ''true''), Some n])))))) j"
text_raw\<open>}%endsnip\<close>
proof-
  {assume "(ev (nxt ((label_eq ''opendoor'') aand (nxt (output_eq [Some(Str ''true''), Some n]))))) j \<and>
           (\<exists>s r p t. j= make_full_observation lift (Some s) r p t)"
   hence "((not (nxt (label_eq ''opendoor'' aand (nxt (output_eq [Some(Str ''true''), Some n]))))) until(((label_eq ''motorstop'') or (nxt (output_eq [Some(Str ''true''), Some n]))))) j"
     apply coinduct
     apply simp
     apply (erule conjE)
     apply (erule exE)+
     apply (case_tac "(shd (stl t)) = (STR ''motorstop'', [Str ''true'', Str ''true''])")
     apply (simp add: UNTIL.base)

     apply (case_tac "s=0")
      apply (case_tac "shd t = (STR ''continit'', [])")
       apply (simp add: ltl_step_0 make_full_observation.ctr[of lift "Some 0"])
       apply (case_tac "stl t", case_tac x1)
       apply (simp add: opendoor_invalid ev_Stream)
       apply (erule disjE)
        apply clarify
        apply (simp add: make_full_observation.ctr[of lift "Some 9"] opendoor_invalid)
       apply auto[1]
      apply (simp add: make_full_observation.ctr[of lift "Some 0"] ltl_step_0_invalid ev_Stream prem_stop_at_none)
      apply (simp add: ltl_step.simps)

     apply (case_tac "s \<in> {5, 6, 7, 8}")
     subgoal for x s r p t
       apply (case_tac "shd t = (STR ''opendoor'', [Str ''true''])")
        apply (simp add: ltl_step_opendoor ev_Stream make_full_observation.ctr[of lift "Some s" r p t])
        apply (case_tac "value.Int (int (s - 4)) = n")
         apply simp
        apply (erule disjE)
       using output_opendoors apply blast
       using output_opendoors apply blast
       apply (case_tac "(shd t) = (STR ''motorstop'', [Str ''true'', Str ''true''])")
        apply simp
       apply simp
       apply (rule disjI2)
       apply (case_tac "(shd t) = (STR ''startsearch'', [Str ''true'', Str ''false''])")
       apply simp
        apply (simp add: ltl_step_startsearch)
        apply standard
       apply (metis (no_types, hide_lams) fst_conv list.simps(3) opendoor_9 prod.collapse snd_conv)
        apply (rule disjI1)
        apply standard
         apply (simp add: ltl_step_startsearch ev_Stream make_full_observation.ctr[of lift "Some s" r p t])
         apply (metis (no_types, lifting) Pair_inject list.simps(3) opendoor_9 prod.collapse)
        apply fastforce
       apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some s" r p t] ltl_step_ocd_invalid)
       apply (erule disjE)
        apply (simp add: ltl_step.simps)
       by (simp add: prem_stop_at_none)

     apply (case_tac "s \<in> {1, 2, 3, 4}")
     subgoal for x s r p t
       apply (case_tac "(shd t) = (STR ''motorstop'', [Str ''true'', Str ''true''])")
        apply simp
       apply (rule disjI2)+
       apply standard
        apply simp
        apply (rule impI)
        apply (case_tac "ltl_step lift (Some s) r (shd t)", case_tac a)
         apply (simp add: ltl_step.simps)
        apply simp
        apply (case_tac "aa \<in> {1, 2, 3, 4}")
       prefer 2
       using not_motorstop_step_state apply blast
       apply (simp add: ltl_step_floor_output)
       apply standard
       apply standard
       apply simp
        apply (case_tac "ltl_step lift (Some s) r (shd t)", case_tac a)
         apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some s" r p t] ltl_step.simps)
         apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some s" r p t])
       using ltl_step_floor_output not_motorstop_step_state apply auto[1]
       apply simp
       apply (case_tac "ltl_step lift (Some s) r (shd t)", case_tac a)
        apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some s" r p t] ltl_step.simps)
       using prem_stop_at_none ltl_step_state_none apply blast
       by fastforce

     apply (case_tac "s=9")
      apply simp
      apply (rule disjI2)+
      apply standard
       apply (rule impI)
       apply (case_tac "\<exists>n. r $ 4 = Some (value.Int n) \<and> n \<in> {1, 2, 3, 4}")
        apply (case_tac "shd t = (STR ''return'', [])")
         apply (erule exE)
         apply simp
         apply (simp add: return ltl_step.simps apply_updates_def)
         apply (case_tac "nat na \<in> {1, 2, 3, 4}")
          apply (simp add: ltl_step_floor_output)
         apply auto[1]
        apply (case_tac "shd t", simp add: possible_steps_9_invalid ltl_step.simps)
       apply (simp add: ltl_step_9_invalid ltl_step.simps)
      apply standard
      apply standard

       apply (case_tac "\<exists>n. r $ 4 = Some (value.Int n) \<and> n \<in> {1, 2, 3, 4}")
        apply (case_tac "shd t = (STR ''return'', [])")
         apply (erule exE)
         apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some 9"] return ltl_step.simps apply_updates_def)
         apply (metis (no_types, lifting) insertCI ltl_step_floor_output nat_numeral numeral_Bit0 numeral_eq_one_iff)

         apply (case_tac "shd t")
         apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some 9"] possible_steps_9_invalid ltl_step.simps)

       apply (case_tac "shd t", simp add: ev_Stream make_full_observation.ctr[of lift "Some 9"] ltl_step_9_invalid)
       apply (simp add: ltl_step.simps(1))

      apply (case_tac "ltl_step lift (Some s) r (shd t)", case_tac a)
       apply (simp add: ev_Stream make_full_observation.ctr[of lift "Some 9"] ltl_step.simps)
     using prem_stop_at_none ltl_step_state_none apply blast
      apply fastforce

     apply (rule disjI2)+
     apply simp
     apply standard
     apply (simp add: invalid_state ltl_step.simps)
     apply (rule disjI2)
     apply (simp add: invalid_state ltl_step.simps)
     apply (rule alw_implies_until)
     apply (rule alw_mono[of "alw (output_eq [])"])
      apply (simp add: no_output_none_if_empty)
     by fastforce
  }
  thus ?thesis using assms by auto
qed

text_raw\<open>\snip{alwMustStopToOpenGen}{1}{2}{%\<close>
lemma alw_must_stop_to_open_gen:
  assumes "\<exists>s r p t. j= make_full_observation lift (Some s) r p t"
  shows "alw ((ev (nxt ((label_eq ''opendoor'') aand
              (nxt (output_eq [Some (Str ''true''), Some  n]))))) impl
             ((not (nxt ((label_eq ''opendoor'') aand
              (nxt (output_eq [Some (Str ''true''), Some  n]))))) until
             (((label_eq ''motorstop'') or (nxt (output_eq [Some (Str ''true''), Some  n])))))) j"
text_raw\<open>}%endsnip\<close>
  using assms apply coinduct
  apply simp
  apply standard
  using alw_must_stop_to_open_aux apply simp
  apply (erule exE)+
  apply simp
  apply (case_tac "ltl_step lift (Some s) r (shd t)", case_tac a)
   apply simp
   apply (rule disjI2)
   apply (rule alw_mono[of "alw (output_eq [])"])
    apply (metis alw_alw ltl_step_state_none no_output_none_if_empty)
   apply clarify
   apply (rule alw_implies_until)
   apply (rule alw_mono[of "alw (output_eq [])"])
    apply simp
   apply fastforce
  by fastforce

text_raw\<open>\snip{alwMustStopToOpen}{1}{2}{%\<close>
lemma alw_must_stop_to_open:
  "alw ((ev (nxt ((label_eq ''opendoor'') aand
        (nxt (output_eq [Some (Str ''true''), Some  n]))))) impl
       ((not (nxt ((label_eq ''opendoor'') aand
        (nxt (output_eq [Some (Str ''true''), Some  n]))))) until
       (((label_eq ''motorstop'') or (nxt (output_eq [Some (Str ''true''), Some  n])))))) (watch lift i)"
text_raw\<open>}%endsnip\<close>
  using alw_must_stop_to_open_gen by blast

lemma alw_must_stop_to_open_aux_suntil:
  assumes "\<exists>s r p t. j= make_full_observation lift (Some s) r p t"
  shows "((ev (nxt ((label_eq ''opendoor'') aand (nxt (output_eq [Some(Str ''true''), Some n]))))) impl
         ((not (nxt (label_eq ''opendoor'' aand (nxt (output_eq [Some(Str ''true''), Some n]))))) suntil(((label_eq ''motorstop'') or (nxt (output_eq [Some(Str ''true''), Some n])))))) j"
  apply (simp add: suntil_as_until)
  apply standard
  apply standard
  using assms alw_must_stop_to_open_aux apply simp
  using assms apply clarify
  by (rule ev.induct, simp, auto)

lemma abstract_watch:
  assumes "\<And>j. \<exists>s r p t. j= make_full_observation e (Some s) r p t \<Longrightarrow> P j"
  shows "P (watch e i)"
  using assms by blast

declare nxt.simps [simp del]

lemma aux:
"alw (output_eq []) xs \<Longrightarrow>
 \<not>ev (nxt (\<lambda>xs. label (shd xs) = STR ''opendoor'' \<and> nxt (output_eq [Some (EFSM.Str ''true''), Some n]) xs)) xs"
  apply (simp add: not_ev_iff)
  apply (rule alw_mono[of "alw (output_eq [])"])
   apply simp
  apply (simp add: nxt.simps)
  apply (rule impI)
  apply (case_tac "xsa", case_tac x2)
  apply simp
  by fastforce

theorem must_stop_lift_to_open_door_aux :
  assumes "\<exists>s r p t. j= make_full_observation lift (Some s) r p t"
  shows "alw ((ev (nxt ((label_eq ''opendoor'') aand (nxt (output_eq [Some(Str ''true''), Some n]))))) impl
      ((not (nxt (label_eq ''opendoor'' aand (nxt (output_eq [Some(Str ''true''), Some n]))))) suntil
      (((label_eq ''motorstop'') or (nxt (output_eq [Some(Str ''true''), Some n])))))) j"
  using assms apply coinduct
  apply simp
  apply standard
   apply (simp add: suntil_as_until)
   apply standard
   apply standard
  using alw_must_stop_to_open_aux apply auto[1]
  apply (rule ev.induct)
     apply simp
    apply (simp add: nxt.simps)
    apply auto[1]
   apply auto[1]

  apply (erule exE)+
  apply simp
  apply (case_tac "ltl_step lift (Some s) r (shd t)", case_tac a)
   apply simp
   apply (rule disjI2)
   apply (rule alw_mono[of "alw (output_eq [])"])
    apply (metis alw_alw ltl_step_state_none no_output_none_if_empty)
   apply clarify
   apply (simp add: suntil_as_until aux)
  by auto

lemma LTL_must_stop_lift_to_open_door: "alw ((ev (nxt ((label_eq ''opendoor'') aand (nxt (output_eq [Some(Str ''true''), Some n]))))) impl
      ((not (nxt ((label_eq ''opendoor'') aand (nxt (output_eq [Some(Str ''true''), Some n]))))) suntil
      (((label_eq ''motorstop'') or (nxt (output_eq [Some(Str ''true''), Some n])))))) (watch lift t)"
  using must_stop_lift_to_open_door_aux by blast

lemma LTL_must_stop_lift_to_open_door_ev: "(ev (state_eq (Some 5)) impl (ev (output_eq [Some (value.Int 0), Some (value.Int 1), Some (Str ''true'')]))) (watch lift t)"
  oops

end
