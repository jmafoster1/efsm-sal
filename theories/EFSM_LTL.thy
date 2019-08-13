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

lemma not_suntil_iff: "\<not>(\<phi> until \<psi>) \<omega> \<or> \<not>ev \<psi> \<omega> \<Longrightarrow> \<not>(\<phi> suntil \<psi>) \<omega>"
  using ev_suntil suntil_implies_until by blast

lemma not_suntil_nxt: " \<not>(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> \<phi> \<omega> \<Longrightarrow> \<not>(\<phi> suntil \<psi>) (stl \<omega>)"
  using suntil.step by blast

lemma de_morgans: "(\<not> x \<or> \<not> y) = (\<not>(x \<and> y))"
  by simp

lemma suntil_true: "ev P \<omega> = ((\<lambda>x. True) suntil P) \<omega>"
  by (simp add: true_suntil)

lemma ev_stl: "\<not> \<psi> \<omega> \<Longrightarrow> ev \<psi> \<omega> = ev \<psi> (stl \<omega>)"
  using ev.cases by auto

lemma suntil_stl: "\<not> \<psi> \<omega> \<Longrightarrow> \<phi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega> = (\<phi> suntil \<psi>) (stl \<omega>)"
  by (meson suntil.simps)

lemma until_stl: "\<not> \<psi> \<omega> \<Longrightarrow> \<phi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega> = (\<phi> until \<psi>) (stl \<omega>)"
  by (meson UNTIL.cases UNTIL.step)

lemma suntil_iff: "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega> \<and> (\<phi> suntil \<psi>) \<omega>"
  using not_ev_not_suntil by blast

lemma de_morgans_fun: "(\<lambda>xs. \<not> \<phi> xs \<and> \<not> \<psi> xs) = (\<lambda>xs. \<not> (\<phi> xs \<or> \<psi> xs))"
  by simp

lemma ev_not_iff: "ev (\<lambda>xs. \<not> P xs) \<omega> = (\<not> alw P \<omega>)"
  by (simp add: alw_iff_sdrop ev_iff_sdrop)

lemma not_alw_not_iff: "(\<not> alw (\<lambda>xs. \<not> \<psi> xs) \<omega>) = ev \<psi> \<omega>"
  by (simp add: alw_iff_sdrop ev_iff_sdrop)

lemma eq_shift: "\<exists>l \<omega>'. \<omega> = l @- \<omega>'"
  by (metis shift.simps(1))

lemma ev_shift: "\<exists>l \<omega>'. ev \<psi> \<omega> = ev \<psi> (l @- \<omega>')"
  by (metis eq_shift)

lemma suntil_shift: "\<psi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) (l @- \<omega>) \<Longrightarrow> (\<phi> suntil \<psi>) (l @- \<omega>)"
proof(induct l)
  case Nil
  then show ?case
    by (simp add: suntil.base)
next
  case (Cons a l)
  then show ?case
    by (metis UNTIL.cases list.sel(3) list.simps(3) shift_simps(2) suntil.base suntil.step)
qed

lemma suntil_if_shift: "\<exists>l \<omega>. \<omega>' = (l @- \<omega>) \<and> \<psi> \<omega> \<and> (\<phi> until \<psi>) (l @- \<omega>) \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>'"
  using suntil_shift by blast

lemma until_ev_suntil: "(\<phi> until \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"
  apply (rule suntil_if_shift)
  apply (simp add: ev_iff_sdrop)
  apply (erule exE)
  apply (rule_tac x="stake m \<omega>" in exI)
  apply (rule_tac x="sdrop m \<omega>" in exI)
  by (simp add: stake_sdrop)

lemma alw_ev_conj: "alw \<psi> \<omega> \<Longrightarrow> ev \<phi> \<omega> \<Longrightarrow> ev (\<lambda>xs. \<phi> xs \<and> \<psi> xs) \<omega>"
  by (simp add: ev_iff_sdrop alw_iff_sdrop)

lemma not_suntil_iff_2: "\<not>(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> \<not>(\<phi> until \<psi>) \<omega> \<or> \<not>ev \<psi> \<omega>"
  using until_ev_suntil by blast

lemma suntil_eq: "(\<phi> suntil \<psi>) \<omega> = ((\<phi> until \<psi>) \<omega> \<and> ev \<psi> \<omega>)"
  using not_suntil_iff not_suntil_iff_2 by blast

(* This takes about 25 seconds to go through on my office machine *)
lemma until_iff_alw: "alw (\<phi> or \<psi>) \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  using UNTIL.coinduct alw.cases UNTIL.cases
  by blast

lemma not_until_not_alw: "\<not>(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not>alw (\<phi> or \<psi>) \<omega>"
  using until_iff_alw
  by auto

lemma not_until_not_ev_not_alw: "\<not>(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not>ev \<psi> \<omega> \<Longrightarrow> \<not>alw \<phi> \<omega>"
  using not_until_not_alw[of \<phi> \<psi> \<omega>]
  apply simp
  using alw_implies_until by auto

lemma alw_stl: "\<phi> xs \<Longrightarrow> alw \<phi> xs = alw \<phi> (stl xs)"
  using alw.simps by auto

lemma ev_cases: "ev \<phi> \<omega> = \<phi> \<omega> \<or> ev \<phi> (stl \<omega>)"
  using ev_stl by blast

lemma "\<forall>m. \<phi> (sdrop m \<omega>) \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  by (simp add: alw_iff_sdrop alw_implies_until)

lemma "(\<phi> until \<psi>) \<omega> = ((\<phi> suntil \<psi>) or (alw \<phi>)) \<omega>"
  apply standard
   defer
  using alw_implies_until not_suntil_iff apply blast
  apply (case_tac "alw \<phi> \<omega>")
   apply (simp add: suntil_eq)
  apply simp
  oops
end
