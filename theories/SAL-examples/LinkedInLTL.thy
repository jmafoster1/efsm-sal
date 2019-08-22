theory LinkedInLTL
imports "../EFSM_LTL"

begin

declare One_nat_def [simp del]

definition login :: transition where
"login \<equiv> \<lparr>
        Label = (STR ''login''),
        Arity = 1,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''free''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition viewFriend :: "transition" where
"viewFriend \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''friendID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [L (Str ''friendID''), L (Str ''name''), L (Str ''HM8p'')],
        Updates = []
      \<rparr>"

definition viewOther :: "transition" where
"viewOther \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''4Zof'')],
        Updates = []
      \<rparr>"

definition viewOtherOON :: "transition" where
"viewOtherOON \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), gexp.Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''OUT_OF_NETWORK''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition viewOtherFuzz :: "transition" where
"viewOtherFuzz \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition pdfFriend :: "transition" where
"pdfFriend \<equiv> \<lparr>
        Label = (STR ''pdf''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''friendID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [L (Str ''detailedPDF'')],
        Updates = []
      \<rparr>"

definition pdfOther :: "transition" where
"pdfOther \<equiv> \<lparr>
        Label = (STR ''pdf''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''detailedPDF'')],
        Updates = []
      \<rparr>"

definition pdfOtherOON :: "transition" where
"pdfOtherOON \<equiv> \<lparr>
        Label = (STR ''pdf''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')),
                 gexp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')),
                 gexp.Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''summaryPDF'')],
        Updates = []
      \<rparr>"

definition linkedIn :: transition_matrix where
"linkedIn \<equiv> {|
              ((0,1), login),
              ((1,2), viewFriend),
              ((1,2), viewOther),
              ((1,3), viewOtherOON),
              ((1,3), viewOtherFuzz),
              ((3, 5), pdfOtherOON),
              ((3, 4), pdfOther),
              ((2, 4), pdfFriend),
              ((2, 4), pdfOther)
         |}"

lemma implode_login: "String.implode ''login'' = STR ''login''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_pdf: "String.implode ''pdf'' = STR ''pdf''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma possible_steps_login: "possible_steps linkedIn 0 Map.empty STR ''login'' [EFSM.Str ''free''] = {|(1, login)|}"
  by eval

lemma possible_steps_1_pdf: "possible_steps linkedIn 1 Map.empty STR ''pdf'' [EFSM.Str ''otherID'', type, token] = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: viewFriend_def viewOther_def viewOtherOON_def viewOtherFuzz_def)

lemma "alw (\<lambda>xs. event (shd xs) = (String.implode ''pdf'', [EFSM.Str ''otherID'', type, token]) \<longrightarrow>
              value_eq (EFSM_LTL.Outputs 1 (stl xs)) (Some (EFSM.Str ''detailedPDF'')) \<noteq> trilean.true)
     (make_full_observation linkedIn (Some 1) Map.empty (stl i))"
  oops

(*neverDetailed: THEOREM linkedIn |- G(
(label=login AND ip_1_login_1=String_free) => X(G(
(label=pdf AND ip_1_view_3=String_otherID) => X(op_1_pdf_1 /= String_detailedPDF)
)
);*)

lemma LTL_neverDetailed:
    "(alw ((label_eq ''login'' aand input_eq [Str ''free'']) impl
          (nxt (alw ((label_eq ''pdf'' aand input_eq [(Str ''otherID''), type, token]) impl
          (nxt (not (check_inx op 1 value_eq (Some (Str ''detailedPDF''))))))))))
     (watch linkedIn i)"
  oops

lemma LTL_teststate_eqNone: "(ev (state_eq None)) (watch linkedIn i)"
  oops

lemma LTL_testinput_eq: "((((state_eq (Some 0)) aand (label_eq ''login'')) aand (input_eq [Str ''free''])) impl (nxt (state_eq (Some 1)))) (watch linkedIn i)"
  oops

lemma LTL_testoutput_eq: "(alw (state_eq (Some 3) aand input_eq [Str ''otherID'', Str ''OUT_OF_NETWORK'', Str ''MNn5'']) impl output_eq [Some (Str ''summaryPDF'')]) (watch linkedIn i)"
  oops

end
