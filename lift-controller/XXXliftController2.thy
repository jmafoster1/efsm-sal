theory XXXliftController2
imports "../EFSM"
begin

definition "continit" :: "transition" where
"continit \<equiv> \<lparr>
      Label = STR ''continit'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "motorstop4" :: "transition" where
"motorstop4 \<equiv> \<lparr>
      Label = STR ''motorstop4'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 4)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "motorstop3" :: "transition" where
"motorstop3 \<equiv> \<lparr>
      Label = STR ''motorstop3'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
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
      Label = STR ''motorstop2'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 2)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "motorstop1" :: "transition" where
"motorstop1 \<equiv> \<lparr>
      Label = STR ''motorstop1'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num 1)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

definition "startsearch4" :: "transition" where
"startsearch4 \<equiv> \<lparr>
      Label = STR ''startsearch4'',
      Arity = 2,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "startsearch3" :: "transition" where
"startsearch3 \<equiv> \<lparr>
      Label = STR ''startsearch3'',
      Arity = 2,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "startsearch2" :: "transition" where
"startsearch2 \<equiv> \<lparr>
      Label = STR ''startsearch2'',
      Arity = 2,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "startsearch1" :: "transition" where
"startsearch1 \<equiv> \<lparr>
      Label = STR ''startsearch1'',
      Arity = 2,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "opendoor4" :: "transition" where
"opendoor4 \<equiv> \<lparr>
      Label = STR ''opendoor4'',
      Arity = 1,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 4))
      ],
      Updates = []
\<rparr>"

definition "opendoor3" :: "transition" where
"opendoor3 \<equiv> \<lparr>
      Label = STR ''opendoor3'',
      Arity = 1,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 3))
      ],
      Updates = []
\<rparr>"

definition "opendoor2" :: "transition" where
"opendoor2 \<equiv> \<lparr>
      Label = STR ''opendoor2'',
      Arity = 1,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 2))
      ],
      Updates = []
\<rparr>"

definition "opendoor1" :: "transition" where
"opendoor1 \<equiv> \<lparr>
      Label = STR ''opendoor1'',
      Arity = 1,
      Guard = [
            (Eq (V (I 0)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num 1))
      ],
      Updates = []
\<rparr>"

definition "return4" :: "transition" where
"return4 \<equiv> \<lparr>
      Label = STR ''return4'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 4)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return3" :: "transition" where
"return3 \<equiv> \<lparr>
      Label = STR ''return3'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 3)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return2" :: "transition" where
"return2 \<equiv> \<lparr>
      Label = STR ''return2'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 2)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return1" :: "transition" where
"return1 \<equiv> \<lparr>
      Label = STR ''return1'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 1)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "down43stop" :: "transition" where
"down43stop \<equiv> \<lparr>
      Label = STR ''down43stop'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
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

definition "down43" :: "transition" where
"down43 \<equiv> \<lparr>
      Label = STR ''down43'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
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

definition "up34stop" :: "transition" where
"up34stop \<equiv> \<lparr>
      Label = STR ''up34stop'',
      Arity = 2,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
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

definition "down32stop" :: "transition" where
"down32stop \<equiv> \<lparr>
      Label = STR ''down32stop'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
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

definition "down32" :: "transition" where
"down32 \<equiv> \<lparr>
      Label = STR ''down32'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
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

definition "up23stop" :: "transition" where
"up23stop \<equiv> \<lparr>
      Label = STR ''up23stop'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
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

definition "up23" :: "transition" where
"up23 \<equiv> \<lparr>
      Label = STR ''up23'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
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

definition "down21stop" :: "transition" where
"down21stop \<equiv> \<lparr>
      Label = STR ''down21stop'',
      Arity = 2,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
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

definition "up12stop" :: "transition" where
"up12stop \<equiv> \<lparr>
      Label = STR ''up12stop'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''true'')))
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

definition "up12" :: "transition" where
"up12 \<equiv> \<lparr>
      Label = STR ''up12'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true''))),
            (Eq (V (I 2)) (L (Str ''false'')))
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
      ((2, 6), motorstop4),
      ((3, 7), motorstop3),
      ((4, 8), motorstop2),
      ((5, 9), motorstop1),
      ((6, 1), startsearch4),
      ((7, 1), startsearch3),
      ((8, 1), startsearch2),
      ((9, 1), startsearch1),
      ((6, 6), opendoor4),
      ((7, 7), opendoor3),
      ((8, 8), opendoor2),
      ((9, 9), opendoor1),
      ((1, 2), return4),
      ((1, 3), return3),
      ((1, 4), return2),
      ((1, 5), return1),
      ((2, 3), down43stop),
      ((2, 3), down43),
      ((3, 2), up34stop),
      ((3, 4), down32stop),
      ((3, 4), down32),
      ((4, 3), up23stop),
      ((4, 3), up23),
      ((4, 5), down21stop),
      ((5, 4), up12stop),
      ((5, 4), up12)
|}"

end
