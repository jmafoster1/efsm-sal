theory LTL_Stream_Additions
imports "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
begin

lemma suntil_implies_until: "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  by (simp add: UNTIL.base UNTIL.step suntil_induct_strong)

lemma alw_implies_until: "alw \<phi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  by (metis until_false until_mono)

lemma until_ev_suntil: "ev \<psi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"
proof(induction rule: ev.induct)
  case (base xs)
  then show ?case
    by (simp add: suntil.base)
next
  case (step xs)
  then show ?case
    by (metis UNTIL.cases suntil.base suntil.step)
qed

lemma suntil_as_until: "(\<phi> suntil \<psi>) \<omega> = ((\<phi> until \<psi>) \<omega> \<and> ev \<psi> \<omega>)"
  using ev_suntil suntil_implies_until until_ev_suntil by blast

lemma not_relesased_yet: "(\<phi> until \<psi>) \<omega> \<Longrightarrow> \<not> \<psi> \<omega> \<Longrightarrow> \<phi> \<omega>"
  using UNTIL.cases by auto

lemma until_must_release: "ev (not \<phi>) \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega>"
proof(induction rule: ev.induct)
  case (base xs)
  then show ?case
    using not_relesased_yet by blast
next
  case (step xs)
  then show ?case
    using UNTIL.cases by blast
qed

lemma until_as_suntil: "(\<phi> until \<psi>) \<omega> = ((\<phi> suntil \<psi>) or (alw \<phi>)) \<omega>"
  using alw_implies_until not_alw_iff suntil_implies_until until_ev_suntil until_must_release by blast

end
