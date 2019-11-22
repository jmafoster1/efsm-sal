theory XXXvend1a
imports "../Contexts"
begin

definition "select" :: "transition" where
"select \<equiv> \<lparr>
      Label = STR ''select'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (V (I 1))),
            (2, (L (Num 100)))
      ]
\<rparr>"

definition "coin" :: "transition" where
"coin \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [],
      Outputs = [
            Plus (L (Num 100)) (Plus (V (I 1)) (Minus (L (Num 0)) (V (R 2))))
      ],
      Updates = [
            (2, Plus (L (Num 50)) (Minus (L (Num 0)) (Plus (V (R 2)) (Times (L (Num 2)) (V (I 1))))))
      ]
\<rparr>"

definition "vend" :: "transition" where
"vend \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            Gt (L (Num 100)) (V (R 2))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "vend1" :: "transition" where
"vend1 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            gNot (Gt (L (Num 100)) (gOr (V (R 2)) (Gt (L (Num 100)) (V (R 2)))))
      ],
      Outputs = [
            (V (R 1))
      ],
      Updates = []
\<rparr>"

definition "thegraph" :: "transition_matrix" where
"thegraph \<equiv> {|
      ((0, 1), select),
      ((1, 1), coin),
      ((1, 1), vend),
      ((1, 4), vend1)
|}"

end
