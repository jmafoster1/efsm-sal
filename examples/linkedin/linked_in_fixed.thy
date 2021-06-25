(* Generated by the SAL to Isabelle Translator *)
(* Version 1.5 released 25 June 2021 *)

theory linked_in_fixed
imports "EFSM.EFSM_LTL"
begin

declare One_nat_def [simp del]
declare ltl_step_alt [simp]

definition login :: "transition" where
"login \<equiv> \<lparr>
    Label = (STR ''login''),
    Arity = 1,
    Guards = [],
    Outputs = [],
    Updates = [
      (1, (V (I 0)))
    ]
\<rparr>"

definition view :: "transition" where
"view \<equiv> \<lparr>
    Label = (STR ''view''),
    Arity = 3,
    Guards = [
      (Eq (V (I 0)) (L (Str ''friendID''))),
      (Eq (V (I 1)) (L (Str ''name''))),
      (Eq (V (I 2)) (L (Str ''HM8p'')))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition view1 :: "transition" where
"view1 \<equiv> \<lparr>
    Label = (STR ''view''),
    Arity = 3,
    Guards = [
      (Eq (V (R 1)) (L (Str ''free''))),
      (Eq (V (I 0)) (L (Str ''otherID''))),
      (Eq (V (I 1)) (L (Str ''OUT_OF_NETWORK''))),
      (Eq (V (I 2)) (L (Str ''MNn5'')))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition view2 :: "transition" where
"view2 \<equiv> \<lparr>
    Label = (STR ''view''),
    Arity = 3,
    Guards = [
      (Eq (V (R 1)) (L (Str ''free''))),
      (Eq (V (I 0)) (L (Str ''otherID''))),
      (Eq (V (I 1)) (L (Str ''name''))),
      (Eq (V (I 2)) (L (Str ''4zoF'')))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition view3 :: "transition" where
"view3 \<equiv> \<lparr>
    Label = (STR ''view''),
    Arity = 3,
    Guards = [
      (Eq (V (R 1)) (L (Str ''paid''))),
      (Eq (V (I 0)) (L (Str ''otherID''))),
      (Eq (V (I 1)) (L (Str ''name''))),
      (Eq (V (I 2)) (L (Str ''MNn5'')))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition pdf :: "transition" where
"pdf \<equiv> \<lparr>
    Label = (STR ''pdf''),
    Arity = 3,
    Guards = [
      (Eq (V (I 0)) (L (Str ''friendID''))),
      (Eq (V (I 1)) (L (Str ''name''))),
      (Eq (V (I 2)) (L (Str ''HM8p'')))
    ],
    Outputs = [
      (L (Str ''detailed_pdf_of_friendID''))
    ],
    Updates = []
\<rparr>"

definition pdf1 :: "transition" where
"pdf1 \<equiv> \<lparr>
    Label = (STR ''pdf''),
    Arity = 3,
    Guards = [
      (Eq (V (I 0)) (L (Str ''otherID''))),
      (Eq (V (I 1)) (L (Str ''OUT_OF_NETWORK''))),
      (Eq (V (I 2)) (L (Str ''MNn5'')))
    ],
    Outputs = [
      (L (Str ''summary_pdf_of_otherID''))
    ],
    Updates = []
\<rparr>"

definition pdf2 :: "transition" where
"pdf2 \<equiv> \<lparr>
    Label = (STR ''pdf''),
    Arity = 3,
    Guards = [
      (Eq (V (I 0)) (L (Str ''otherID''))),
      (Eq (V (I 1)) (L (Str ''name''))),
      (Eq (V (I 2)) (L (Str ''4zoF'')))
    ],
    Outputs = [
      (L (Str ''detailed_pdf_of_otherID''))
    ],
    Updates = []
\<rparr>"


definition linkedIn :: "transition_matrix" where
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
  
  
lemmas transitions =
  login_def
  view_def
  view1_def
  view2_def
  view3_def
  pdf_def
  pdf1_def
  pdf2_def
  
  
lemma LTL_neverDetailed :
  "((label_eq ''login'' aand
      input_eq [Str ''free'']) impl
      nxt (alw ((label_eq ''pdf'' aand
      check_exp ((Eq (V (Ip 0)) (L (Str ''otherID''))))) impl
      not (nxt (output_eq [Some (Str
      ''detailed_pdf_of_otherID'')])))))
(watch linkedIn trace)"
oops

end
