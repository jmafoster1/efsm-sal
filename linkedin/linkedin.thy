theory linkedin
imports "EFSM.EFSM_LTL"
begin

definition "login" :: "transition" where
"login \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guards = [
            gexp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''free''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view" :: "transition" where
"view \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guards = [
            gexp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''friendID'')),
            gexp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''name'')),
            gexp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''HM8p''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view1" :: "transition" where
"view1 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guards = [
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view2" :: "transition" where
"view2 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guards = [
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''4zoF''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view3" :: "transition" where
"view3 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guards = [
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf" :: "transition" where
"pdf \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guards = [
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''friendID'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''HM8p''))
      ],
      Outputs = [
            (aexp.L (Str ''detailed_pdf_of(friendID)''))
      ],
      Updates = []
\<rparr>"

definition "pdf1" :: "transition" where
"pdf1 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guards = [
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''MNn5''))
      ],
      Outputs = [
            (aexp.L (Str ''summary_pdf_of(otherID)''))
      ],
      Updates = []
\<rparr>"

definition "pdf2" :: "transition" where
"pdf2 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guards = [
            GExp.Eq (aexp.V (vname.I 1)) (aexp.L (Str ''otherID'')),
            GExp.Eq (aexp.V (vname.I 2)) (aexp.L (Str ''name'')),
            GExp.Eq (aexp.V (vname.I 3)) (aexp.L (Str ''4zoF''))
      ],
      Outputs = [
            (aexp.L (Str ''detailed_pdf_of(otherID)''))
      ],
      Updates = []
\<rparr>"

definition "linkedIn" :: "transition_matrix" where
"linkedIn \<equiv> {|
      ((0, 1), login),
      ((1, 2), view),
      ((1, 4), view1),
      ((1, 6), view2),
      ((1, 6), view3),
      ((2, 3), pdf),
      ((4, 5), pdf1),
      ((6, 7), pdf2)
|}"

end
