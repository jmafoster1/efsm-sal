theory XXXGeneralisation
imports "../Contexts"
begin

definition "select" :: "transition" where
"select \<equiv> \<lparr>
      Label = STR ''select'',
      Arity = 1,
      Guard = [
            gexp.Eq (V (I 1)) (L (Str ''coke''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "coin" :: "transition" where
"coin \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [
            gexp.Eq (V (I 1)) (L (Num 50))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "coin1" :: "transition" where
"coin1 \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [
            gexp.Eq (V (I 1)) (L (Num 50))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "vend" :: "transition" where
"vend \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [],
      Outputs = [
            (L (Num 1))
      ],
      Updates = []
\<rparr>"

definition "vend1" :: "transition" where
"vend1 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = []
\<rparr>"

definition "vend_f" :: "transition_matrix" where
"vend_f \<equiv> {|
      ((0, 1), select),
      ((1, 2), coin),
      ((2, 3), coin1),
      ((3, 4), vend),
      ((2, 2), vend1)
|}"

definition "select1" :: "transition" where
"select1 \<equiv> \<lparr>
      Label = STR ''select'',
      Arity = 1,
      Guard = [
            gexp.Eq (V (I 1)) (L (Str ''coke''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "coin2" :: "transition" where
"coin2 \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (V (I 1)))
      ]
\<rparr>"

definition "coin3" :: "transition" where
"coin3 \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, Plus (V (R 1)) (V (I 1)))
      ]
\<rparr>"

definition "vend2" :: "transition" where
"vend2 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            Ge (V (R 1)) (L (Num 100))
      ],
      Outputs = [
            (L (Num 1))
      ],
      Updates = []
\<rparr>"

definition "vend3" :: "transition" where
"vend3 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            Lt (V (R 1)) (L (Num 100))
      ],
      Outputs = [
            (L (Num 1))
      ],
      Updates = []
\<rparr>"

definition "vend_g" :: "transition_matrix" where
"vend_g \<equiv> {|
      ((0, 1), select1),
      ((1, 2), coin2),
      ((2, 2), coin3),
      ((2, 3), vend2),
      ((2, 2), vend3)
|}"

end
