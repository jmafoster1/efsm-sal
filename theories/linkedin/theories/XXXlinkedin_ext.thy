theory XXXlinkedin_ext
imports "../../efsm-ltl/EFSM_LTL"
begin

declare One_nat_def [simp del]

definition "login" :: "transition" where
"login \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''free''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "login1" :: "transition" where
"login1 \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (aexp.V (vname.I 0)) (aexp.L (Str ''paid''))
      ],
      Outputs = [],
      Updates = []
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
      ((0, 1), login1),
      ((1, 2), view),
      ((1, 4), view1),
      ((1, 6), view2),
      ((1, 6), view3),
      ((2, 3), pdf),
      ((4, 5), pdf1),
      ((6, 7), pdf2)
|}"

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

lemmas implode = implode_detailedPDF implode_OON implode_name implode_4zoF implode_MNn5
                 implode_HM8p implode_friendID implode_otherID implode_pdf implode_login

lemma login_free: "possible_steps linkedIn 0 <> STR ''login'' [EFSM.Str ''free''] = {|(1, login)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
                   apply (simp_all add: apply_guards login_def login1_def Str_def)
  using trilean.distinct(1) by presburger

lemma not_view: "l \<noteq> STR ''view'' \<Longrightarrow>
       possible_steps linkedIn 1 r l i = {||}"
  apply (simp add: possible_steps_empty linkedIn_def)
  apply safe
  by (simp_all add: view_def view1_def view2_def view3_def)

lemma view_fuzz: "possible_steps linkedIn 1 <> STR ''view'' [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''MNn5''] = {|(6, view3)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: view_def view1_def view2_def  view3_def apply_guards_def join_ir_nth Str_def implode)

lemma not_pdf_6: "l \<noteq> STR ''pdf'' \<Longrightarrow> possible_steps linkedIn 6 <> l i = {||}"
  apply (simp add: possible_steps_empty linkedIn_def)
  apply safe
  by (simp_all add: pdf2_def)

lemma pdf_6_invalid_inputs: "i \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] \<Longrightarrow>
 possible_steps linkedIn 6 <> STR ''pdf'' i = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def linkedIn_def)
  apply (simp add: pdf2_def apply_guards_def join_ir_nth Str_def implode)
  using nth_equalityI[of "[value.Str STR ''otherID'', value.Str STR ''name'', value.Str STR ''4zoF'']" i]
  apply simp
  by (metis One_nat_def add_diff_cancel_left' less_2_cases less_Suc_eq nth_Cons' numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc)

lemma pdf_fuzz: "possible_steps linkedIn 6 <> STR ''pdf'' [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] = {|(7, pdf2)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: pdf2_def apply_guards numeral_2_eq_2 Str_def implode One_nat_def)

text_raw\<open>\snip{contradiction}{1}{2}{%\<close>
lemma contradiction: "apply_outputs (Outputs pdf2) (join_ir (snd (shd i)) <>) \<noteq> [Some (value.Str STR ''detailed_pdf_of_otherID'')]"
  apply (simp add: apply_outputs_def pdf2_def Str_def implode)
  oops
  text_raw\<open>}%endsnip\<close>

lemma possible_steps_linkedIn_6:
  "possible_steps linkedIn 6 <> STR ''pdf'' i = {|(7, pdf2)|} \<or>
   possible_steps linkedIn 6 <> STR ''pdf'' i = {||}"
  apply (case_tac "[EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF'']")
   apply simp
  by (metis pdf_6_invalid_inputs pdf_fuzz)

(* This should be where the wheels fall off *)
lemma flaw: "alw (\<lambda>xs. label (shd xs) = STR ''pdf'' \<and> value_eq (Some (nth (inputs (shd xs)) 0)) (Some (value.Str STR ''otherID'')) = trilean.true \<longrightarrow>
              output (shd xs) \<noteq> [Some (value.Str STR ''detailed_pdf_of_otherID'')])
     (make_full_observation linkedIn (Some 6) <> i)"
  apply (rule alw)
   apply (simp add: ltl_step_alt)
   apply (case_tac "possible_steps linkedIn 6 <> STR ''pdf'' (snd (shd i)) = {||}")
    apply simp
   apply (case_tac "possible_steps linkedIn 6 <> STR ''pdf'' (snd (shd i)) = {|(7, pdf2)|}")
    apply simp
    apply standard
    apply standard
  sorry

lemma after_login: "alw (\<lambda>xs. label (shd xs) = String.implode ''pdf'' \<and> value_eq (Some (inputs (shd xs) ! 0)) (Some (EFSM.Str ''otherID'')) = trilean.true \<longrightarrow>
              \<not> output_eq [Some (EFSM.Str ''detailed_pdf_of_otherID'')] xs)
     (make_full_observation linkedIn (Some 1) <> (stl i))"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: ltl_step_alt Str_def implode)
    apply (case_tac "(fst (shd (stl i))) = STR ''view''")
     defer
     apply (simp add: not_view)
     apply standard
      apply (simp add: output_eq_def ltl_step_alt not_view)
      apply standard
      apply (rule disjI2)
    using no_output_none[of linkedIn "<>" "stl (stl i)"]
    unfolding output_eq_def
      apply (simp add: alw_mono)
     apply standard
      apply (rule disjI2)
    using no_output_none[of linkedIn "<>" "stl (stl i)"]
    unfolding output_eq_def
     apply (simp add: alw_mono)

     apply (simp add: output_eq_def)
    apply (case_tac "(snd (shd (stl i))) = [Str ''otherID'', Str ''name'', Str ''MNn5'']")
     apply (simp add: ltl_step_alt view_fuzz view3_def)
     apply (rule disjI2)
    using flaw[of "stl (stl i)"]
     apply (simp add: alw_mono) (* Using a broken proof *)
    oops

text_raw\<open>\snip{neverDetailed}{1}{2}{%\<close>
lemma LTL_neverDetailed:
    "(((label_eq  ''login'' aand input_eq [Str ''free'']) impl
     (nxt (alw ((label_eq ''pdf'' aand
     check_exp (Eq (V (ltl_vname.I 0)) (L (Str ''otherID'')))) impl 
     (not (output_eq [Some (Str ''detailed_pdf_of_otherID'')])))))))
     (watch linkedIn i)"
text_raw\<open>}%endsnip\<close>
  apply (simp add: watch_def ltl_step_alt)
  apply (simp add: input_eq_def label_eq_def implode_login)
  apply (simp add: login_free login_def)
  apply standard
  oops

end
