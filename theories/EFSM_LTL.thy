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
  "Registers n s \<equiv> datastate (shd s) n"

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
  "checkInx ior.rg n f v s = (f (datastate (shd s) n) v = trilean.true)"

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

lemma no_updates_none_individual: "alw (checkInx rg n ValueEq (r n)) (make_full_observation e None r t)"
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

end
