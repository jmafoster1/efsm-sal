theory XXXlinkedin_ext
imports "../../EFSM_LTL"
begin

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

end
