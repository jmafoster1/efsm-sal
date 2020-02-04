theory XXXMotorControlImproved
imports "../theories/efsm-isabelle/EFSM"
begin

definition "init" :: "transition" where
"init \<equiv> \<lparr>
      Label = STR ''init'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (L (Num 0))),
            (2, (L (Num 0))),
            (3, (L (Num 999)))
      ]
\<rparr>"

definition "feed" :: "transition" where
"feed \<equiv> \<lparr>
      Label = STR ''feed'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (4, (V (I 1)))
      ]
\<rparr>"

definition "m3r" :: "transition" where
"m3r \<equiv> \<lparr>
      Label = STR ''m3r'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (3, Minus (V (R 3)) (L (Num 1)))
      ]
\<rparr>"

definition "m2" :: "transition" where
"m2 \<equiv> \<lparr>
      Label = STR ''m2'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (2, Plus (V (R 2)) (L (Num 1))),
            (4, Minus (V (R 4)) (L (Num 1)))
      ]
\<rparr>"

definition "check" :: "transition" where
"check \<equiv> \<lparr>
      Label = STR ''check'',
      Arity = 0,
      Guard = [
            Gt (V (R 4)) (L (Num 0))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "check1" :: "transition" where
"check1 \<equiv> \<lparr>
      Label = STR ''check'',
      Arity = 0,
      Guard = [
            Eq (V (R 4)) (L (Num 0))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "release" :: "transition" where
"release \<equiv> \<lparr>
      Label = STR ''release'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pass" :: "transition" where
"pass \<equiv> \<lparr>
      Label = STR ''pass'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = []
\<rparr>"

definition "m1" :: "transition" where
"m1 \<equiv> \<lparr>
      Label = STR ''m1'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, Plus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "check2" :: "transition" where
"check2 \<equiv> \<lparr>
      Label = STR ''check'',
      Arity = 0,
      Guard = [
            Le (V (R 1)) (L (Num 500))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "check3" :: "transition" where
"check3 \<equiv> \<lparr>
      Label = STR ''check'',
      Arity = 0,
      Guard = [
            Gt (V (R 1)) (L (Num 500))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "m1r" :: "transition" where
"m1r \<equiv> \<lparr>
      Label = STR ''m1r'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, Minus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition "check4" :: "transition" where
"check4 \<equiv> \<lparr>
      Label = STR ''check'',
      Arity = 0,
      Guard = [
            Gt (V (R 1)) (L (Num 0))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "check5" :: "transition" where
"check5 \<equiv> \<lparr>
      Label = STR ''check'',
      Arity = 0,
      Guard = [
            Eq (V (R 1)) (L (Num 0))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "thegraph" :: "transition_matrix" where
"thegraph \<equiv> {|
      ((0, 1), init),
      ((1, 2), feed),
      ((2, 3), m3r),
      ((3, 4), m2),
      ((4, 2), check),
      ((4, 10), check1),
      ((10, 5), release),
      ((5, 6), pass),
      ((6, 7), m1),
      ((7, 6), check2),
      ((7, 8), check3),
      ((8, 9), m1r),
      ((9, 8), check4),
      ((9, 1), check5)
|}"

end
