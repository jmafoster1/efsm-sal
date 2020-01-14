theory XXXlinkedin_ext_fixed
imports "../../efsm-ltl/EFSM_LTL"
begin

declare One_nat_def [simp del]

definition "login" :: "transition" where
"login \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (aexp.V (vname.I 0)))
      ]
\<rparr>"

definition "view" :: "transition" where
"view \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''friendID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''HM8p''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view1" :: "transition" where
"view1 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.R 1)) (aexp.L (Str ''free'')),
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view2" :: "transition" where
"view2 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.R 1)) (aexp.L (Str ''free'')),
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''4zoF''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view3" :: "transition" where
"view3 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.R 1)) (aexp.L (Str ''paid'')),
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf" :: "transition" where
"pdf \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''friendID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''HM8p''))
      ],
      Outputs = [
            (aexp.L (Str ''detailed_pdf_of_friendID''))
      ],
      Updates = []
\<rparr>"

definition "pdf1" :: "transition" where
"pdf1 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''MNn5''))
      ],
      Outputs = [
            (aexp.L (Str ''summary_pdf_of_otherID''))
      ],
      Updates = []
\<rparr>"

definition "pdf2" :: "transition" where
"pdf2 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''4zoF''))
      ],
      Outputs = [
            (aexp.L (Str ''detailed_pdf_of_otherID''))
      ],
      Updates = []
\<rparr>"

definition "linkedIn" :: "transition_matrix" where
"linkedIn \<equiv> {|
      ((0, 1), login),
      ((1, 2), view),
      ((1, 4), view1),
      ((1, 4), view2),
      ((1, 6), view3),
      ((2, 3), pdf),
      ((4, 5), pdf1),
      ((6, 7), pdf2)
|}"

lemmas transitions = login_def view_def view1_def view2_def view3_def pdf_def pdf1_def pdf2_def

lemma implode_login: "String.implode ''login'' = STR ''login''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_pdf: "String.implode ''pdf'' = STR ''pdf''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_friendID: "String.implode ''friendID'' = STR ''friendID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_otherID: "String.implode ''otherID'' = STR ''otherID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_HM8p: "String.implode ''HM8p'' = STR ''HM8p''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_MNn5: "String.implode ''MNn5'' = STR ''MNn5''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_4zoF: "String.implode ''4zoF'' = STR ''4zoF''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_name: "String.implode ''name'' = STR ''name''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_OON: "String.implode ''OUT_OF_NETWORK'' = STR ''OUT_OF_NETWORK''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_detailedPDF: "String.implode ''detailed_pdf_of_otherID'' = STR ''detailed_pdf_of_otherID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_summaryPDF: "String.implode ''summary_pdf_of_otherID'' = STR ''summary_pdf_of_otherID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_detailedPDF_friend: "String.implode ''detailed_pdf_of_friendID'' = STR ''detailed_pdf_of_friendID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_paid: "String.implode ''paid'' = STR ''paid''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_free: "String.implode ''free'' = STR ''free''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemmas implode = implode_summaryPDF implode_detailedPDF_friend implode_detailedPDF
                 implode_OON implode_name implode_4zoF implode_MNn5 implode_HM8p
                 implode_friendID implode_otherID implode_pdf implode_login implode_paid implode_free

lemma login_user: "possible_steps linkedIn 0 <> STR ''login'' [u] = {|(1, login)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: login_def)

lemma apply_updates_login: "apply_updates (Updates XXXlinkedin_ext_fixed.login) (join_ir [EFSM.Str ''free''] <>) <> = (<>(1 := Str ''free''))"
  by (simp add: login_def datastate)

lemma not_view_1: "l \<noteq> STR ''view'' \<Longrightarrow> possible_steps linkedIn 1 r l i = {||}"
  apply (simp add: possible_steps_empty linkedIn_def transitions)
  by auto

lemma view_friend: "possible_steps linkedIn 1 (<>(1 := EFSM.Str ''free'')) STR ''view''
                  [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] = {|(2, view)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: transitions apply_guards implode Str_def numeral_2_eq_2 One_nat_def)

lemma not_pdf_2: "l \<noteq> STR ''pdf'' \<Longrightarrow> possible_steps linkedIn 2 r l i = {||}"
  by (simp add: possible_steps_empty linkedIn_def transitions)

lemma pdf_friend: "possible_steps linkedIn 2 (<>(1 := EFSM.Str ''free'')) STR ''pdf''
                      [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] = {|(3, pdf)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def input2state_def implode Str_def numeral_2_eq_2 One_nat_def)

lemma pdf_2_invalid: "i \<noteq> [Str ''friendID'', Str ''name'', Str ''HM8p''] \<Longrightarrow>
possible_steps linkedIn 2 (<>(1 := EFSM.Str ''free'')) STR ''pdf'' i = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def linkedIn_def)
  apply (simp add: pdf_def apply_guards_def join_ir_nth Str_def implode)
  using nth_equalityI[of "[value.Str STR ''friendID'', value.Str STR ''name'', value.Str STR ''HM8p'']" i]
  apply simp
  by (metis (no_types, lifting) One_nat_def Suc_1 add_diff_cancel_left' less_2_cases less_Suc_eq nth_Cons' numeral_3_eq_3 plus_1_eq_Suc)

lemma stop_at_3: "possible_steps linkedIn 3 r l i = {||}"
  by (simp add: possible_steps_empty linkedIn_def)

lemma stop_at_5: "possible_steps linkedIn 5 r l i = {||}"
  by (simp add: possible_steps_empty linkedIn_def)

lemma stop_at_7: "possible_steps linkedIn 7 r l i = {||}"
  by (simp add: possible_steps_empty linkedIn_def)

lemma wrong_head: "i ! 0 = EFSM.Str ''otherID'' \<Longrightarrow>
      i \<noteq> [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p'']"
  using Str_def implode_friendID implode_otherID by auto

lemma "length i = length i' \<Longrightarrow> \<forall>j<length i. i ! j = i' ! j \<Longrightarrow> i = i'"
  using nth_equalityI by blast

lemma possible_ltl_steps_from_2:
  "ltl_step linkedIn (Some 2) (<>(1 := EFSM.Str ''free'')) e = (Some 3, [Some (Str ''detailed_pdf_of_friendID'')], (<>(1 := EFSM.Str ''free''))) \<or>
   ltl_step linkedIn (Some 2) (<>(1 := EFSM.Str ''free'')) e = (None, [],(<>(1 := EFSM.Str ''free'')))"
  apply (case_tac "e = (STR ''pdf'', [Str ''friendID'', Str ''name'', Str ''HM8p''])")
   apply (simp add: pdf_friend pdf_def join_ir_def input2state_def apply_outputs_def)
  apply (case_tac "fst e = STR ''pdf''")
   defer
   apply (simp add: ltl_step_alt not_pdf_2)
  apply (rule disjI2)
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def linkedIn_def pdf_def apply_guards_def join_ir_nth Str_def implode)
  using nth_equalityI[of "snd e" "[value.Str STR ''friendID'', value.Str STR ''name'', value.Str STR ''HM8p'']"]
  apply simp
  by (metis (no_types, lifting) One_nat_def Suc_1 add_diff_cancel_left' decompose_pair less_2_cases less_Suc_eq nth_Cons' numeral_3_eq_3 plus_1_eq_Suc)

lemma s2_ok: "alw (\<lambda>xs. label (shd xs) = STR ''pdf'' \<and> value_eq (Some (nth (inputs (shd xs)) 0)) (Some (EFSM.Str ''otherID'')) = trilean.true \<longrightarrow>
              output (shd (stl xs)) \<noteq> [Some (EFSM.Str ''detailed_pdf_of_otherID'')])
     (make_full_observation linkedIn (Some 2) (<>(1 := EFSM.Str ''free'')) p i)"
  apply (rule alw)
   apply (simp add: ltl_step_alt pdf_2_invalid wrong_head)
  apply simp
  apply (case_tac "ltl_step linkedIn (Some 2) (<>(1 := EFSM.Str ''free'')) (shd i) = (None, [],(<>(1 := EFSM.Str ''free'')))")
  apply simp
   apply (rule alw_mono[of "nxt (output_eq [])"])
    apply (simp add: no_output_none_nxt)
   apply (simp add: output_eq_def)
  apply (case_tac "ltl_step linkedIn (Some 2) (<>(1 := EFSM.Str ''free'')) (shd i) = 
                    (Some 3, [Some (Str ''detailed_pdf_of_friendID'')], (<>(1 := EFSM.Str ''free'')))")
   apply simp
   apply (rule alw_mono[of "nxt (output_eq [])"])
    apply (rule alw)
     apply (simp add: ltl_step_alt output_eq_def stop_at_3)
    apply (simp add: ltl_step_alt no_output_none_nxt stop_at_3)
   apply (simp add: output_eq_def)
  using possible_ltl_steps_from_2 by blast

lemma view_other: "possible_steps linkedIn 1 (<>(1 := EFSM.Str ''free'')) STR ''view''
                  [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] = {|(4, view1)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def input2state_def implode Str_def numeral_2_eq_2 One_nat_def)

lemma view_other_fuzz_foiled: " possible_steps linkedIn 1 (<>(1 := EFSM.Str ''free'')) STR ''view''
                  [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] = {|(4, view2)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def input2state_def implode Str_def numeral_2_eq_2 One_nat_def)

lemma pdf_summary: "possible_steps linkedIn 4 (<>(1 := EFSM.Str ''free'')) STR ''pdf''
                      [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] = {|(5, pdf1)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def input2state_def implode Str_def numeral_2_eq_2 One_nat_def)

lemma not_pdf_4: "l \<noteq> STR ''pdf'' \<Longrightarrow> possible_steps linkedIn 4 r l i = {||}"
  by (simp add: possible_steps_empty linkedIn_def transitions numeral_2_eq_2)

lemma pdf_4_invalid_inputs: "i \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] \<Longrightarrow>
possible_steps linkedIn 4 r l i = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def linkedIn_def)
  apply (simp add: pdf1_def apply_guards_def join_ir_nth Str_def implode)
  using nth_equalityI[of "[value.Str STR ''otherID'', value.Str STR ''OUT_OF_NETWORK'', value.Str STR ''MNn5'']" i]
  apply simp
  by (metis One_nat_def Suc_1 add_diff_cancel_left' less_2_cases less_Suc_eq nth_Cons' numeral_3_eq_3 plus_1_eq_Suc)

lemma possible_ltl_steps_from_4:
  "ltl_step linkedIn (Some 4) (<>(1 := EFSM.Str ''free'')) e = (Some 5, [Some (Str ''summary_pdf_of_otherID'')], (<>(1 := EFSM.Str ''free''))) \<or>
   ltl_step linkedIn (Some 4) (<>(1 := EFSM.Str ''free'')) e = (None, [],(<>(1 := EFSM.Str ''free'')))"
  apply (simp add: ltl_step_alt)
  apply (case_tac "e = (STR ''pdf'', [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''])")
   apply (simp add: pdf_summary apply_outputs_def join_ir_def pdf1_def)
  apply (case_tac "fst e = STR ''pdf''")
   apply (rule disjI2)
  using pdf_4_invalid_inputs[of "snd e" "(<>(1 := EFSM.Str ''free''))" "STR ''pdf''"]
   apply (simp add: Let_def)
   apply (metis (no_types, lifting) prod.collapse)
  by (simp add: not_pdf_4)

lemma s4_ok: "alw (\<lambda>xs. label (shd xs) = STR ''pdf'' \<and> value_eq (Some (nth (inputs (shd xs)) 0)) (Some (EFSM.Str ''otherID'')) = trilean.true \<longrightarrow>
              output (shd (stl xs)) \<noteq> [Some (EFSM.Str ''detailed_pdf_of_otherID'')])
     (make_full_observation linkedIn (Some 4) (<>(1 := EFSM.Str ''free'')) p i)"
  apply (rule alw)
   apply simp
  using possible_ltl_steps_from_4[of "shd i"]
  Str_def implode_detailedPDF implode_summaryPDF apply auto[1]
  using possible_ltl_steps_from_4[of "shd i"]
  apply simp
  apply (case_tac "ltl_step linkedIn (Some 4) (<>(1 := EFSM.Str ''free'')) (shd i) =
    (Some 5, [Some (EFSM.Str ''summary_pdf_of_otherID'')], <>(1 := EFSM.Str ''free''))")
   apply simp
   apply (rule alw)
    apply (simp add: ltl_step_alt stop_at_5)
   apply (rule alw_mono[of "nxt (output_eq [])"])
    apply (simp add: ltl_step_alt no_output_none_nxt stop_at_5)
   apply (simp add: output_eq_def)
   apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: no_output_none_nxt)
  by (simp add: output_eq_def)

lemma invalid_input_1:
      "i \<noteq> [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] \<Longrightarrow>
       i \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] \<Longrightarrow>
       i \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] \<Longrightarrow>
       possible_steps linkedIn 1 (<>(1 := EFSM.Str ''free'')) l i = {||}"
  apply (case_tac i)
   apply (simp add: possible_steps_empty linkedIn_def)
   apply safe[1]
      apply (simp add: transitions)+
  apply (case_tac list)
   apply (simp add: possible_steps_empty linkedIn_def)
   apply safe[1]
      apply (simp add: transitions)+
  apply (case_tac lista)
   apply (simp add: possible_steps_empty linkedIn_def)
   apply safe[1]
      apply (simp add: transitions)+
  apply (case_tac listb)
   apply (simp add: possible_steps_empty linkedIn_def)
  defer
   apply (simp add: possible_steps_empty apply_guards_def linkedIn_def join_ir_def transitions)
  apply auto[1]
   apply safe
  by (simp_all add: apply_guards_def transitions join_ir_def input2state_def Str_def implode numeral_2_eq_2 One_nat_def)

lemma after_login: "alw (\<lambda>xs. label (shd xs) = STR ''pdf'' \<and> value_eq (Some (nth (inputs (shd xs)) 0)) (Some (EFSM.Str ''otherID'')) = trilean.true \<longrightarrow>
              \<not> output_eq [Some (EFSM.Str ''detailed_pdf_of_otherID'')] (stl xs))
     (make_full_observation XXXlinkedin_ext_fixed.linkedIn (Some 1) (<>(1 := EFSM.Str ''free'')) p i)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: ltl_step_alt)
    apply (case_tac "(fst (shd i)) = STR ''view''")
     defer
     apply (simp add: not_view_1)
     apply standard
      apply clarify
      apply (simp add: output_eq_def)
      apply (rule disjI2)
      apply (rule alw_mono[of "nxt (output_eq [])"])
       apply (simp add: no_output_none_nxt)
      apply (simp add: output_eq_def)
     apply standard
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply (simp add: output_eq_def)

    apply simp
    apply (case_tac "(snd (shd i)) = [Str ''friendID'', Str ''name'', Str ''HM8p'']")
     apply (simp add: view_friend view_def)
    apply (rule disjI2)
    using s2_ok[of "[]" "stl i"]
    apply (simp add: alw_mono output_eq_def)
    apply (case_tac "(snd (shd i)) = [Str ''otherID'', Str ''OUT_OF_NETWORK'', Str ''MNn5'']")
     apply (simp add: view_other view1_def)
    using s4_ok[of "[]" "stl i"]
    apply (simp add: alw_mono output_eq_def)
    apply (case_tac "(snd (shd i)) = [Str ''otherID'', Str ''name'', Str ''4zoF'']")
     apply (simp add: view_other_fuzz_foiled view2_def)
    using s4_ok[of "[]" "stl i"]
    apply (simp add: alw_mono output_eq_def)
    apply (simp add: invalid_input_1)
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (output_eq [])"])
    using no_output_none_nxt apply blast
    by (simp add: output_eq_def)
qed

(* SAL thinks this is true so we should be able to prove it *)
text_raw\<open>\snip{neverDetailedProof}{1}{2}{%\<close>
lemma LTL_neverDetailed:
    "(((label_eq  ''login'' aand input_eq [Str ''free'']) impl
     (nxt (alw ((label_eq ''pdf'' aand
     check_exp (Eq (V (I 0)) (L (Str ''otherID'')))) impl
     (not (nxt (output_eq [Some (Str ''detailed_pdf_of_otherID'')]))))))))
     (watch linkedIn i)"
  apply (simp add: watch_def ltl_step_alt)
  apply (simp add: input_eq_def label_eq_def)
  apply (simp add: implode login_user apply_updates_login check_exp_def login_def)
  using after_login[of "[]" "stl i"]
  by (simp add: alw_mono join_ir_nth)

text_raw\<open>}%endsnip\<close>
end
