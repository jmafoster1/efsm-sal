theory XXXliftController3
imports "EFSM.EFSM"
begin

definition "continit" :: "transition" where
"continit \<equiv> \<lparr>
      Label = STR ''continit'',
      Arity = 0,
      Guards = [],
      Outputs = [],
      Updates = [
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "motorstop" :: "transition" where
"motorstop \<equiv> \<lparr>
      Label = STR ''motorstop'',
      Arity = 2,
      Guards = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 4)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "motorstop1" :: "transition" where
"motorstop1 \<equiv> \<lparr>
      Label = STR ''motorstop'',
      Arity = 2,
      Guards = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 3)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "motorstop2" :: "transition" where
"motorstop2 \<equiv> \<lparr>
      Label = STR ''motorstop'',
      Arity = 2,
      Guards = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 2)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "motorstop3" :: "transition" where
"motorstop3 \<equiv> \<lparr>
      Label = STR ''motorstop'',
      Arity = 2,
      Guards = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 1)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "startsearch" :: "transition" where
"startsearch \<equiv> \<lparr>
      Label = STR ''startsearch'',
      Arity = 2,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "startsearch1" :: "transition" where
"startsearch1 \<equiv> \<lparr>
      Label = STR ''startsearch'',
      Arity = 2,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "startsearch2" :: "transition" where
"startsearch2 \<equiv> \<lparr>
      Label = STR ''startsearch'',
      Arity = 2,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "startsearch3" :: "transition" where
"startsearch3 \<equiv> \<lparr>
      Label = STR ''startsearch'',
      Arity = 2,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "opendoor" :: "transition" where
"opendoor \<equiv> \<lparr>
      Label = STR ''opendoor'',
      Arity = 1,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 4))
      ],
      Updates = []
\<rparr>"

definition "opendoor1" :: "transition" where
"opendoor1 \<equiv> \<lparr>
      Label = STR ''opendoor'',
      Arity = 1,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 3))
      ],
      Updates = []
\<rparr>"

definition "opendoor2" :: "transition" where
"opendoor2 \<equiv> \<lparr>
      Label = STR ''opendoor'',
      Arity = 1,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 2))
      ],
      Updates = []
\<rparr>"

definition "opendoor3" :: "transition" where
"opendoor3 \<equiv> \<lparr>
      Label = STR ''opendoor'',
      Arity = 1,
      Guards = [
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 1))
      ],
      Updates = []
\<rparr>"

definition "return" :: "transition" where
"return \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 4)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return1" :: "transition" where
"return1 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 3)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return2" :: "transition" where
"return2 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 2)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return3" :: "transition" where
"return3 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 1)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "down" :: "transition" where
"down \<equiv> \<lparr>
      Label = STR ''down'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 2)),
            (L (Str ''true''))
      ],
      Updates = [
            (4, (L (Num 3))),
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "down1" :: "transition" where
"down1 \<equiv> \<lparr>
      Label = STR ''down'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''false'')))
      ],
      Outputs = [
            (L (Num 2)),
            (L (Str ''false''))
      ],
      Updates = [
            (4, (L (Num 3))),
            (1, (L (Str ''false'')))
      ]
\<rparr>"

definition "up" :: "transition" where
"up \<equiv> \<lparr>
      Label = STR ''up'',
      Arity = 2,
      Guards = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 1)),
            (L (Str ''true''))
      ],
      Updates = [
            (4, (L (Num 4))),
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "down2" :: "transition" where
"down2 \<equiv> \<lparr>
      Label = STR ''down'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 2)),
            (L (Str ''true''))
      ],
      Updates = [
            (4, (L (Num 2))),
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "down3" :: "transition" where
"down3 \<equiv> \<lparr>
      Label = STR ''down'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''false'')))
      ],
      Outputs = [
            (L (Num 2)),
            (L (Str ''false''))
      ],
      Updates = [
            (4, (L (Num 2))),
            (1, (L (Str ''false'')))
      ]
\<rparr>"

definition "up1" :: "transition" where
"up1 \<equiv> \<lparr>
      Label = STR ''up'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 1)),
            (L (Str ''true''))
      ],
      Updates = [
            (4, (L (Num 3))),
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "up2" :: "transition" where
"up2 \<equiv> \<lparr>
      Label = STR ''up'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''false'')))
      ],
      Outputs = [
            (L (Num 1)),
            (L (Str ''false''))
      ],
      Updates = [
            (4, (L (Num 3))),
            (1, (L (Str ''false'')))
      ]
\<rparr>"

definition "down4" :: "transition" where
"down4 \<equiv> \<lparr>
      Label = STR ''down'',
      Arity = 2,
      Guards = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 2)),
            (L (Str ''true''))
      ],
      Updates = [
            (3, (L (Num 1))),
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "up3" :: "transition" where
"up3 \<equiv> \<lparr>
      Label = STR ''up'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 1)),
            (L (Str ''true''))
      ],
      Updates = [
            (1, (L (Str ''true''))),
            (4, (L (Num 2)))
      ]
\<rparr>"

definition "up4" :: "transition" where
"up4 \<equiv> \<lparr>
      Label = STR ''up'',
      Arity = 3,
      Guards = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true''))),
            (Eq (V (I 3)) (L (Str ''false'')))
      ],
      Outputs = [
            (L (Num 1)),
            (L (Str ''false''))
      ],
      Updates = [
            (4, (L (Num 2))),
            (1, (L (Str ''false'')))
      ]
\<rparr>"

definition "thegraph" :: "transition_matrix" where
"thegraph \<equiv> {|
      ((0, 1), continit),
      ((2, 6), motorstop),
      ((3, 7), motorstop1),
      ((4, 8), motorstop2),
      ((5, 9), motorstop3),
      ((6, 1), startsearch),
      ((7, 1), startsearch1),
      ((8, 1), startsearch2),
      ((9, 1), startsearch3),
      ((6, 6), opendoor),
      ((7, 7), opendoor1),
      ((8, 8), opendoor2),
      ((9, 9), opendoor3),
      ((1, 2), return),
      ((1, 3), return1),
      ((1, 4), return2),
      ((1, 5), return3),
      ((2, 3), down),
      ((2, 3), down1),
      ((3, 2), up),
      ((3, 4), down2),
      ((3, 4), down3),
      ((4, 3), up1),
      ((4, 3), up2),
      ((4, 5), down4),
      ((5, 4), up3),
      ((5, 4), up4)
|}"

end
