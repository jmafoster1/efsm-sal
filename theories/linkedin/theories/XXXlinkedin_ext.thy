theory XXXlinkedin_ext
imports "../../EFSM_LTL"
begin

declare One_nat_def [simp del]

definition "login" :: "transition" where
"login \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''free''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "login1" :: "transition" where
"login1 \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''paid''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view" :: "transition" where
"view \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''friendID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''HM8p''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view1" :: "transition" where
"view1 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (V (I 3)) (L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view2" :: "transition" where
"view2 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''4zoF''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view3" :: "transition" where
"view3 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf" :: "transition" where
"pdf \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''friendID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''HM8p''))
      ],
      Outputs = [
            (L (Str ''detailed_pdf_of_friendID''))
      ],
      Updates = []
\<rparr>"

definition "pdf1" :: "transition" where
"pdf1 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (V (I 3)) (L (Str ''MNn5''))
      ],
      Outputs = [
            (L (Str ''summary_pdf_of_otherID''))
      ],
      Updates = []
\<rparr>"

definition "pdf2" :: "transition" where
"pdf2 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''4zoF''))
      ],
      Outputs = [
            (L (Str ''detailed_pdf_of_otherID''))
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
  by (simp_all add: view_def view1_def view2_def view3_def apply_guards Str_def implode_otherID implode_friendID implode_name implode_OON implode_MNn5 implode_4zoF)

lemma not_pdf_6: "l \<noteq> STR ''pdf'' \<Longrightarrow> possible_steps linkedIn 6 <> l i = {||}"
  apply (simp add: possible_steps_empty linkedIn_def)
  apply safe
  by (simp_all add: pdf2_def)

lemma pdf_6_invalid_inputs: "i \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] \<Longrightarrow>
 possible_steps linkedIn 6 <> STR ''pdf'' i = {||}"
  apply (case_tac i)
   apply (simp add: possible_steps_empty pdf2_def linkedIn_def)
  apply (case_tac list)
   apply (simp add: possible_steps_empty pdf2_def linkedIn_def)
  apply (case_tac lista)
   apply (simp add: possible_steps_empty pdf2_def linkedIn_def)
  apply (case_tac listb)
   apply (simp add: possible_steps_empty pdf2_def linkedIn_def apply_guards)
  by (simp add: possible_steps_empty pdf2_def linkedIn_def)

lemma pdf_fuzz: "possible_steps linkedIn 6 <> STR ''pdf'' [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] = {|(7, pdf2)|}"
  apply (simp add: possible_steps_singleton linkedIn_def)
  apply safe
  by (simp_all add: pdf2_def apply_guards)

(* This should be where the wheels fall off *)
lemma "alw (\<lambda>xs. label (shd xs) = STR ''pdf'' \<and> ValueEq (Some (Inputs 0 xs)) (Some (value.Str STR ''otherID'')) = trilean.true \<longrightarrow>
              output (shd xs) \<noteq> [Some (value.Str STR ''detailed_pdf_of_otherID'')])
     (make_full_observation linkedIn (Some 6) <> (stl (stl i)))"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: ltl_step_alt)
    apply (case_tac "(fst (shd (stl (stl i)))) = STR ''pdf''")
     defer
     apply (simp add: not_pdf_6)
    using no_output_none[of linkedIn "<>" "stl (stl (stl i))"]
    unfolding OutputEq_def
     apply (simp add: alw_mono)
    apply simp
    apply (case_tac "(snd (shd (stl (stl i)))) = [Str ''otherID'', Str ''name'', Str ''4zoF'']")
     defer
     apply (simp add: pdf_6_invalid_inputs)
    using no_output_none[of linkedIn "<>" "stl (stl (stl i))"]
    unfolding OutputEq_def
     apply (simp add: alw_mono)
    apply (simp add: pdf_fuzz pdf2_def)
    apply standard
     apply standard
     apply (simp add: apply_outputs Str_def implode)
     apply (simp add: ValueEq_def Inputs_def)
    oops

lemma after_login: "alw (\<lambda>xs. label (shd xs) = String.implode ''pdf'' \<and> ValueEq (Some (Inputs 0 xs)) (Some (EFSM.Str ''otherID'')) = trilean.true \<longrightarrow>
              \<not> OutputEq [Some (EFSM.Str ''detailed_pdf_of_otherID'')] xs)
     (make_full_observation linkedIn (Some 1) <> (stl i))"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: ltl_step_alt Str_def implode)
    apply (case_tac "(fst (shd (stl i))) = STR ''view''")
     defer
     apply (simp add: not_view)
     apply standard
      apply (simp add: OutputEq_def ltl_step_alt not_view)
     apply (simp add: OutputEq_def ValueEq_def)
    using no_output_none[of linkedIn "<>" "stl (stl i)"]
    unfolding OutputEq_def
     apply (simp add: alw_mono)
    apply (case_tac "(snd (shd (stl i))) = [Str ''otherID'', Str ''name'', Str ''MNn5'']")
     apply (simp add: ltl_step_alt view_fuzz view3_def)
    apply (rule disjI2)
    oops


text_raw{*\snip{neverDetailed}{1}{2}{%*}
lemma LTL_neverDetailed:
    "(((LabelEq  ''login'' aand InputEq [Str ''free'']) impl
     (nxt (alw ((LabelEq ''pdf'' aand
     checkInx ip 1 ValueEq (Some (Str ''otherID''))) impl 
     (not (OutputEq [Some (Str ''detailed_pdf_of_otherID'')])))))))
     (watch linkedIn i)"
text_raw{*}%endsnip*}
  apply (simp add: watch_def ltl_step_alt)
  apply (simp add: InputEq_def LabelEq_def implode_login)
  apply (simp add: login_free login_def)
  apply standard
  oops

end