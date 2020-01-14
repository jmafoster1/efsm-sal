theory EFSM_LTL
imports "../efsm-isabelle/EFSM" "HOL-Library.Linear_Temporal_Logic_on_Streams" "LTL_Exp"
begin

record state =
  statename :: "nat option"
  datastate :: registers
  event :: event
  "output" :: outputs

type_synonym property = "state stream \<Rightarrow> bool"

abbreviation label :: "state \<Rightarrow> String.literal" where
  "label s \<equiv> fst (event s)"

abbreviation inputs :: "state \<Rightarrow> value list" where
  "inputs s \<equiv> snd (event s)"

fun ltl_step :: "transition_matrix \<Rightarrow> nat option \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> (nat option \<times> outputs \<times> registers)" where
  "ltl_step _ None r _ = (None, [], r)" |
  "ltl_step e (Some s) r (l, i) = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))
                  )"

lemma ltl_step_alt:  "ltl_step e (Some s) r t = (let possibilities = possible_steps e s r (fst t) (snd t) in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t') = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (apply_outputs (Outputs t') (join_ir (snd t) r)), (apply_updates (Updates t') (join_ir (snd t) r) r))
                  )"
  apply (case_tac t)
  by (simp add: Let_def)

lemma ltl_step_none: "possible_steps e s r (fst ie) (snd ie) = {||} \<Longrightarrow> ltl_step e (Some s) r ie = (None, [], r)"
  by (simp add: ltl_step_alt)

primcorec make_full_observation :: "transition_matrix \<Rightarrow> nat option \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> event stream \<Rightarrow> state stream" where
  "make_full_observation e s d p i = (
    let (s', o', d') = ltl_step e s d (shd i) in
    \<lparr>statename = s, datastate = d, event=(shd i), output = p\<rparr>##(make_full_observation e s' d' o' (stl i))
  )"

definition watch :: "transition_matrix \<Rightarrow> event stream \<Rightarrow> state stream" where
  "watch e i \<equiv> (make_full_observation e (Some 0) <> [] i)"

definition state_eq :: "nat option \<Rightarrow> state stream \<Rightarrow> bool" where
  "state_eq v s \<equiv> statename (shd s) = v"

lemma state_eq_holds: "state_eq s = holds (\<lambda>x. statename x = s)"
  apply (rule ext)
  by (simp add: state_eq_def holds_def)

lemma state_eq_None_not_Some: "state_eq None s \<Longrightarrow> \<not> state_eq (Some n) s"
  by (simp add: state_eq_def)

definition label_eq :: "string \<Rightarrow> state stream \<Rightarrow> bool" where
  "label_eq v s \<equiv> fst (event (shd s)) = (String.implode v)"

lemma watch_label: "label_eq l (watch e t) = (fst (shd t) = String.implode l)"
  by (simp add: label_eq_def watch_def)

definition input_eq :: "value list \<Rightarrow> state stream \<Rightarrow> bool" where
  "input_eq v s \<equiv> inputs (shd s) = v"

definition event_eq :: "(string \<times> inputs) \<Rightarrow> state stream \<Rightarrow> bool" where
  "event_eq e = label_eq (fst e) aand input_eq (snd e)"

definition output_eq :: "value option list \<Rightarrow> state stream \<Rightarrow> bool" where
  "output_eq v s \<equiv> output (shd s) = v"

lemma shd_state_is_none: "(state_eq None) (make_full_observation e None r p t)"
  by (simp add: state_eq_def)

lemma unfold_observe_none: "make_full_observation e None d p t = (\<lparr>statename = None, datastate = d, event=(shd t), output = p\<rparr>##(make_full_observation e None d [] (stl t)))"
  by (simp add: stream.expand)

lemma once_none_always_none: "alw (state_eq None) (make_full_observation e None r p t)"
proof -
  obtain ssa :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
      "\<forall>f p s. f (stl (ssa f)) \<noteq> stl (f (ssa f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then have "alw (state_eq None) (make_full_observation e None r [] (stl t))"
    by (metis (no_types) all_imp_alw shd_state_is_none stream.sel(2) unfold_observe_none)
  then show ?thesis
    by (metis (no_types) alw.simps shd_state_is_none stream.sel(2) unfold_observe_none)
qed

lemma no_output_none: "nxt (alw (output_eq [])) (make_full_observation e None r p t)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: output_eq_def all_imp_alw)
qed

lemma no_output_none_nxt: "alw (nxt (output_eq [])) (make_full_observation e None r p t)"
  by (metis alw_inv alw_mono no_output_none nxt.simps)

lemma no_updates_none: "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r p t)"
proof -
  have "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r [] (stl t))"
    proof -
      obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
        "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
        by (metis (no_types) alw_inv)
      then show ?thesis
        by (simp add: output_eq_def all_imp_alw)
    qed
    then show ?thesis
    proof(coinduction)
      case alw
      then show ?case
        by simp
    qed
qed

lemma event_components: "(label_eq l aand input_eq i) s = (event (shd s) = (String.implode l, i))"
  apply (simp add: label_eq_def input_eq_def)
  by (metis fst_conv prod.collapse snd_conv)

lemma alw_not_some: "alw (\<lambda>xs. statename (shd xs) \<noteq> Some s) (make_full_observation e None r p t)"
  by (metis (mono_tags, lifting) alw_mono once_none_always_none option.distinct(1) state_eq_def)

lemma state_none: "((state_eq None) impl nxt (state_eq None)) (make_full_observation e s r p t)"
  by (simp add: state_eq_def)

lemma state_none_2: "(state_eq None) (make_full_observation e s r p t) \<Longrightarrow> (state_eq None) (make_full_observation e s r p (stl t))"
  by (simp add: state_eq_def)

lemma decompose_pair: "e \<noteq> (l, i) = (\<not> (fst e =l \<and> snd e = i))"
  by (metis fst_conv prod.collapse sndI)

definition check_exp :: "ltl_gexp \<Rightarrow> state stream \<Rightarrow> bool" where
  "check_exp g s = (gval g (snd (event (shd s))) (datastate (shd s)) (output (shd s)) = trilean.true)"

lemma alw_ev: "alw f = not (ev (\<lambda>s. \<not>f s))"
  by simp

end
