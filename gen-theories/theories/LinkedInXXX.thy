theory LinkedInXXX
imports "../Contexts"
begin

definition "login" :: "transition" where
"login \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''ree''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view" :: "transition" where
"view \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''riendID'')),
            GExp.Eq (V (I 2)) (L (Str ''ame'')),
            GExp.Eq (V (I 3)) (L (Str ''M8p''))
      ],
      Outputs = [
            (L (Str ''riendID'')),
            (L (Str ''ame'')),
            (L (Str ''M8p''))
      ],
      Updates = []
\<rparr>"

definition "view1" :: "transition" where
"view1 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''therID'')),
            GExp.Eq (V (I 2)) (L (Str ''ame'')),
            GExp.Eq (V (I 3)) (L (Str ''Zof''))
      ],
      Outputs = [
            (L (Str ''therID'')),
            (L (Str ''ame'')),
            (L (Str ''Zof''))
      ],
      Updates = []
\<rparr>"

definition "view2" :: "transition" where
"view2 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''therID'')),
            GExp.Eq (V (I 2)) (L (Str ''UT_OF_NETWORK'')),
            GExp.Eq (V (I 3)) (L (Str ''Nn5''))
      ],
      Outputs = [
            (L (Str ''therID'')),
            (L (Str ''UT_OF_NETWORK'')),
            (L (Str ''Nn5''))
      ],
      Updates = []
\<rparr>"

definition "view3" :: "transition" where
"view3 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''therID'')),
            GExp.Eq (V (I 2)) (L (Str ''ame'')),
            GExp.Eq (V (I 3)) (L (Str ''Nn5''))
      ],
      Outputs = [
            (L (Str ''therID'')),
            (L (Str ''ame'')),
            (L (Str ''Nn5''))
      ],
      Updates = []
\<rparr>"

definition "pdf" :: "transition" where
"pdf \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''riendID'')),
            GExp.Eq (V (I 2)) (L (Str ''ame'')),
            GExp.Eq (V (I 3)) (L (Str ''M8p''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf1" :: "transition" where
"pdf1 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''therID'')),
            GExp.Eq (V (I 2)) (L (Str ''ame'')),
            GExp.Eq (V (I 3)) (L (Str ''Zof''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf2" :: "transition" where
"pdf2 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''therID'')),
            GExp.Eq (V (I 2)) (L (Str ''ame'')),
            GExp.Eq (V (I 3)) (L (Str ''Zof''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf3" :: "transition" where
"pdf3 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''therID'')),
            GExp.Eq (V (I 2)) (L (Str ''UT_OF_NETWORK'')),
            GExp.Eq (V (I 3)) (L (Str ''Nn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "efsm" :: "transition_matrix" where
"efsm \<equiv> {|
      ((0, 1), login),
      ((1, 2), view),
      ((1, 2), view1),
      ((1, 3), view2),
      ((1, 3), view3),
      ((2, 4), pdf),
      ((3, 4), pdf1),
      ((2, 4), pdf2),
      ((3, 5), pdf3)
|}"

end
