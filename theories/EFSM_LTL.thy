theory EFSM_LTL
imports "EFSM" "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
begin

datatype ior = ip | op | rg

record state =
  statename :: "nat option"
  datastate :: datastate
  event :: event
  "output" :: outputs

type_synonym full_observation = "state stream"
type_synonym property = "full_observation \<Rightarrow> bool"

abbreviation label :: "state \<Rightarrow> String.literal" where
  "label s \<equiv> fst (event s)"

abbreviation inputs :: "state \<Rightarrow> value list" where
  "inputs s \<equiv> snd (event s)"

fun ltl_step :: "transition_matrix \<Rightarrow> nat option \<Rightarrow> datastate \<Rightarrow> event \<Rightarrow> (nat option \<times> outputs \<times> datastate)" where
  "ltl_step _ None r _ = (None, [], r)" |
  "ltl_step e (Some s) r (l, i) = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))
                  )"

primcorec make_full_observation :: "transition_matrix \<Rightarrow> nat option \<Rightarrow> datastate \<Rightarrow> event stream \<Rightarrow> full_observation" where
  "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in \<lparr>statename = s, datastate = d, event=(shd i), output = o'\<rparr>##(make_full_observation e s' d' (stl i)))"

lemma make_full_observation_unfold: "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in \<lparr>statename = s, datastate = d, event=(shd i), output = o'\<rparr>##(make_full_observation e s' d' (stl i)))"
  using make_full_observation.code by blast

definition watch :: "transition_matrix \<Rightarrow> event stream \<Rightarrow> full_observation" where
  "watch e i \<equiv> (make_full_observation e (Some 0) <> i)"

abbreviation non_null :: "property" where
  "non_null s \<equiv> (statename (shd s) \<noteq> None)"

abbreviation null :: "property" where
  "null s \<equiv> (statename (shd s) = None)"

definition Outputs :: "nat \<Rightarrow> state stream \<Rightarrow> value option" where
  "Outputs n s \<equiv> nth (output (shd s)) n"

definition Inputs :: "nat \<Rightarrow> state stream \<Rightarrow> value" where
  "Inputs n s \<equiv> nth (inputs (shd s)) (n-1)"

definition Registers :: "nat \<Rightarrow> state stream \<Rightarrow> value option" where
  "Registers n s \<equiv> datastate (shd s) (R n)"

definition StateEq :: "nat option \<Rightarrow> state stream \<Rightarrow> bool" where
  "StateEq v s \<equiv> statename (shd s) = v"

definition LabelEq :: "string \<Rightarrow> state stream \<Rightarrow> bool" where
  "LabelEq v s \<equiv> fst (event (shd s)) = (String.implode v)"

lemma watch_label: "LabelEq l (watch e t) = (fst (shd t) = String.implode l)"
  by (simp add: LabelEq_def watch_def)

fun "checkInx" :: "ior \<Rightarrow> nat \<Rightarrow> (value option \<Rightarrow> value option \<Rightarrow> trilean) \<Rightarrow> value option \<Rightarrow> state stream \<Rightarrow> bool" where
  "checkInx ior.ip n f v s = (f (Some (Inputs (n-1) s)) v = trilean.true)" |
  "checkInx ior.op n f v s = (f (Outputs n s) v = trilean.true)" |
  "checkInx ior.rg n f v s = (f (datastate (shd s) (vname.R n)) v = trilean.true)"

definition InputEq :: "value list \<Rightarrow> state stream \<Rightarrow> bool" where
  "InputEq v s \<equiv> inputs (shd s) = v"

definition OutputEq :: "value option list \<Rightarrow> state stream \<Rightarrow> bool" where
  "OutputEq v s \<equiv> output (shd s) = v"

definition InputLength :: "nat \<Rightarrow> state stream \<Rightarrow> bool" where
  "InputLength v s \<equiv> length (inputs (shd s)) = v"

definition OutputLength :: "nat \<Rightarrow> state stream \<Rightarrow> bool" where
  "OutputLength v s \<equiv> length (output (shd s)) = v"

abbreviation some_state :: "full_observation \<Rightarrow> bool" where
  "some_state s \<equiv> (\<exists>state. statename (shd s) = Some state)"

lemma non_null_equiv: "non_null = some_state"
  by simp

lemma start_some_state:  "s = make_full_observation e (Some 0) <> t \<Longrightarrow> some_state s"
  by simp

lemma some_until_none: "s = make_full_observation e (Some 0) <> t \<Longrightarrow> (some_state until null) s "
proof (coinduction)
  case UNTIL
  then show ?case
    by (smt UNTIL.coinduct non_null_equiv)
qed

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

lemma event_components: "(LabelEq l aand InputEq i) s = (event (shd s) = (String.implode l, i))"
  apply (simp add: LabelEq_def InputEq_def)
  by (metis fst_conv prod.collapse snd_conv)

lemma alw_not_some: "alw (\<lambda>xs. statename (shd xs) \<noteq> Some s) (make_full_observation e None r t)"
  using once_none_always_none[of e r t]
  unfolding StateEq_def
  by (simp add: alw_mono)

lemma decompose_pair: "e \<noteq> (l, i) = (\<not> (fst e =l \<and> snd e = i))"
  by (metis fst_conv prod.collapse sndI)

lemma check_binding_aand: "(alw x aand y) = (alw x) aand y"
  by simp

lemma check_binding_or: "(alw x or y) = (alw x) or y"
  by simp

lemma check_binding_impl: "(alw x impl y) = (alw x) impl y"
  by simp

end
