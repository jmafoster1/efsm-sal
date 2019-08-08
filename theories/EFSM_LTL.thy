theory EFSM_LTL
imports "EFSM" "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
begin

datatype ior = ip | op | rg

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
                     (Some s', (apply_outputs (Transition.Outputs t') (join_ir (snd t) r)), (apply_updates (Updates t') (join_ir (snd t) r) r))
                  )"
  apply (case_tac t)
  by (simp add: Let_def)

primcorec make_full_observation :: "transition_matrix \<Rightarrow> nat option \<Rightarrow> registers \<Rightarrow> event stream \<Rightarrow> state stream" where
  "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in \<lparr>statename = s, datastate = d, event=(shd i), output = o'\<rparr>##(make_full_observation e s' d' (stl i)))"

lemma make_full_observation_unfold: "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in \<lparr>statename = s, datastate = d, event=(shd i), output = o'\<rparr>##(make_full_observation e s' d' (stl i)))"
  using make_full_observation.code by blast

definition watch :: "transition_matrix \<Rightarrow> event stream \<Rightarrow> state stream" where
  "watch e i \<equiv> (make_full_observation e (Some 0) <> i)"

definition Outputs :: "nat \<Rightarrow> state stream \<Rightarrow> value option" where
  "Outputs n s \<equiv> nth (output (shd s)) n"

definition Inputs :: "nat \<Rightarrow> state stream \<Rightarrow> value" where
  "Inputs n s \<equiv> nth (inputs (shd s)) (n-1)"

definition Registers :: "nat \<Rightarrow> state stream \<Rightarrow> value option" where
  "Registers n s \<equiv> datastate (shd s) $ n"

definition StateEq :: "nat option \<Rightarrow> state stream \<Rightarrow> bool" where
  "StateEq v s \<equiv> statename (shd s) = v"

lemma StateEq_None_not_Some: "StateEq None s \<Longrightarrow> \<not> StateEq (Some n) s"
  by (simp add: StateEq_def)

definition LabelEq :: "string \<Rightarrow> state stream \<Rightarrow> bool" where
  "LabelEq v s \<equiv> fst (event (shd s)) = (String.implode v)"

lemma watch_label: "LabelEq l (watch e t) = (fst (shd t) = String.implode l)"
  by (simp add: LabelEq_def watch_def)

definition InputEq :: "value list \<Rightarrow> state stream \<Rightarrow> bool" where
  "InputEq v s \<equiv> inputs (shd s) = v"

definition EventEq :: "(string \<times> inputs) \<Rightarrow> state stream \<Rightarrow> bool" where
  "EventEq e = LabelEq (fst e) aand InputEq (snd e)"

definition OutputEq :: "value option list \<Rightarrow> state stream \<Rightarrow> bool" where
  "OutputEq v s \<equiv> output (shd s) = v"

definition InputLength :: "nat \<Rightarrow> state stream \<Rightarrow> bool" where
  "InputLength v s \<equiv> length (inputs (shd s)) = v"

definition OutputLength :: "nat \<Rightarrow> state stream \<Rightarrow> bool" where
  "OutputLength v s \<equiv> length (output (shd s)) = v"

fun "checkInx" :: "ior \<Rightarrow> nat \<Rightarrow> (value option \<Rightarrow> value option \<Rightarrow> trilean) \<Rightarrow> value option \<Rightarrow> state stream \<Rightarrow> bool" where
  "checkInx ior.ip n f v s = (f (Some (Inputs (n-1) s)) v = trilean.true)" |
  "checkInx ior.op n f v s = (f (Outputs n s) v = trilean.true)" |
  "checkInx ior.rg n f v s = (f (datastate (shd s) $ n) v = trilean.true)"

lemma shd_state_is_none: "(StateEq None) (make_full_observation e None r t)"
  by (simp add: StateEq_def)

lemma unfold_observe_none: "make_full_observation e None d t = (\<lparr>statename = None, datastate = d, event=(shd t), output = []\<rparr>##(make_full_observation e None d (stl t)))"
  by (simp add: stream.expand)

lemma once_none_always_none: "alw (StateEq None) (make_full_observation e None r t)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: StateEq_def all_imp_alw)
qed

lemma no_output_none: "alw (OutputEq []) (make_full_observation e None r t)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: OutputEq_def all_imp_alw)
qed

lemma no_updates_none: "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r t)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: all_imp_alw)
qed

lemma no_updates_none_individual: "alw (checkInx rg n ValueEq (r $ n)) (make_full_observation e None r t)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: ValueEq_def all_imp_alw)
qed

lemma event_components: "(LabelEq l aand InputEq i) s = (event (shd s) = (String.implode l, i))"
  apply (simp add: LabelEq_def InputEq_def)
  by (metis fst_conv prod.collapse snd_conv)

lemma alw_not_some: "alw (\<lambda>xs. statename (shd xs) \<noteq> Some s) (make_full_observation e None r t)"
  using once_none_always_none[of e r t]
  unfolding StateEq_def
  by (simp add: alw_mono)

lemma decompose_pair: "e \<noteq> (l, i) = (\<not> (fst e =l \<and> snd e = i))"
  by (metis fst_conv prod.collapse sndI)

lemma suntil_implies_until: "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  by (simp add: UNTIL.base UNTIL.step suntil_induct_strong)

(* This takes about 25 seconds to go through *)
lemma alw_implies_until: "alw \<phi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  using UNTIL.coinduct alw.cases
  by blast

lemma suntil_same: "(\<phi> suntil \<phi>) \<omega> = \<phi> \<omega>"
  using suntil.base suntil.cases by blast

lemma not_ev_not_suntil: "\<not> ev \<psi> \<omega> \<Longrightarrow> \<not> ((\<phi> suntil \<psi>) \<omega>)"
  using ev_suntil by blast

lemma alw_as_suntil: "alw \<phi> \<omega> = not ((\<lambda>x. True) suntil (not \<phi>)) \<omega>"
  apply standard
   apply (metis ev_suntil not_alw_iff)
  by (simp add: not_ev_iff true_suntil)

lemma alw_conj_pred: "alw \<chi> \<omega> \<Longrightarrow> \<psi> \<omega> = (\<psi> aand \<chi>) \<omega>"
  by auto

lemma not_until_implies_not_suntil: "\<not>(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not>(\<phi> suntil \<psi>) \<omega>"
  using suntil_implies_until by auto

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"


lemma "\<not>alw \<phi> \<omega> \<Longrightarrow> \<not>ev \<psi> \<omega> \<Longrightarrow> \<not>(\<phi> until \<psi>) \<omega>"
  apply (simp add: not_ev_iff)
  apply (simp add: alw_as_suntil)
  

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not> alw \<phi> \<omega> \<Longrightarrow> ev \<psi> \<omega>"
  apply (simp add: not_alw_iff)
  apply (simp add: ev_iff_sdrop)
  apply clarify

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> alw \<phi> \<omega> \<or> ev \<psi> \<omega>"
  apply (case_tac "alw \<phi> \<omega>")
   apply simp
  apply simp

lemma " \<not> ev \<psi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega> \<Longrightarrow> (\<phi> until (\<lambda>x. False)) \<omega>"
proof(coinduction)
  case UNTIL
  then show ?case
    apply simp
    apply standard
    using UNTIL.cases apply blast
    apply (rule disjI2)
qed

lemma "\<not> ev \<psi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega> = (\<phi> until (\<lambda>x. False)) \<omega>"
  apply standard

lemma "\<not> ev \<psi> \<omega> \<Longrightarrow> \<not>alw \<phi> \<omega> \<Longrightarrow> \<not>(\<phi> until \<psi>) \<omega>"
  apply clarify
  apply (rule UNTIL.cases)
    apply simp
   apply auto[1]
  apply clarify


lemma "\<not> ev \<psi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega> \<Longrightarrow> alw \<phi> \<omega>"


lemma "(\<phi> until \<psi>) \<omega>  \<Longrightarrow> \<not> ((\<phi> suntil \<psi>) \<omega>) \<Longrightarrow> alw \<phi> \<omega>"


lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not> alw \<phi> \<omega> \<Longrightarrow> ev \<psi> \<omega>"
  apply (simp only: not_alw_iff ev_eq_suntil)
  apply simp
  apply (case_tac "(\<phi> suntil \<psi>) \<omega>")
   apply (metis (full_types) ev_eq_suntil ev_suntil)
  using suntil.base suntil.step suntil_induct_strong

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> alw \<phi> \<omega> \<or> ev \<psi> \<omega>"
  apply (case_tac "alw \<phi> \<omega>")
   apply simp
  apply (case_tac "ev \<psi> \<omega>")
   apply simp
  apply simp

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not> ev \<psi> \<omega> \<Longrightarrow> (\<phi> until (\<lambda>xs. False)) \<omega>"
  apply (simp add: not_ev_iff)

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not> ev \<psi> \<omega> \<Longrightarrow> alw \<phi> \<omega>"

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not>(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> alw \<phi> \<omega>"
  apply (case_tac "ev \<psi> \<omega>")
   prefer 2
   apply (simp add: not_ev_iff)

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"
  

lemma "(\<phi> until \<psi>) \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega> \<or> alw \<phi> \<omega>"
  apply (rule suntil.cases)
  using suntil.base apply blast
   prefer 2
   apply simp
  apply clarify
  apply (simp add: not_alw_iff)
  

lemma "(\<phi> until \<psi>) \<omega> = ((\<phi> suntil \<psi>) or (alw \<phi>)) \<omega>"
  apply standard

end
