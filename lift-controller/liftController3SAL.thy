theory liftController3SAL
imports "EFSM.EFSM"
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
      Label = STR ''motorstop'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''motorstop'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''motorstop'',
      Arity = 2,
      Guard = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Guard = [
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "opendoor4" :: "transition" where
"opendoor4 \<equiv> \<lparr>
      Label = STR ''opendoor'',
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
      Label = STR ''opendoor'',
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
      Label = STR ''opendoor'',
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
      Label = STR ''opendoor'',
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
      Label = STR ''return'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 4)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return3" :: "transition" where
"return3 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 3)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return2" :: "transition" where
"return2 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 2)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return1" :: "transition" where
"return1 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guard = [
            (Eq (V (R 4)) (L (Num 1)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "down43stop" :: "transition" where
"down43stop \<equiv> \<lparr>
      Label = STR ''down'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''down'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''false'')))
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
      Label = STR ''up'',
      Arity = 2,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''down'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''down'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''false'')))
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
      Label = STR ''up'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''up'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''false'')))
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
      Label = STR ''down'',
      Arity = 2,
      Guard = [
            (Eq (V (R 2)) (L (Num 2))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''up'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true'')))
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
      Label = STR ''up'',
      Arity = 3,
      Guard = [
            (Eq (V (R 2)) (L (Num 1))),
            (Eq (V (R 1)) (L (Str ''false''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''false'')))
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

definition "lift" :: "transition_matrix" where
"lift \<equiv> {|
    ((0, 9), continit), ((9, 4), return4), ((9, 3), return3), ((9, 2), return2), ((9, 1), return1), ((8, 9), startsearch),
       ((8, 8), opendoor4), ((7, 9), startsearch), ((7, 7), opendoor3), ((6, 9), startsearch), ((6, 6), opendoor2),
       ((5, 9), startsearch), ((5, 5), opendoor1), ((4, 8), motorstop4), ((4, 3), down43stop), ((4, 3), down43),
       ((3, 7), motorstop3), ((3, 4), up34stop), ((3, 2), down32stop), ((3, 2), down32), ((2, 6), motorstop2),
       ((2, 3), up23stop), ((2, 3), up23), ((2, 1), down21stop), ((1, 5), motorstop1), ((1, 2), up12stop), ((1, 2), up12)
  |}"


  lemma alw_must_stop_to_open: "alw ((not (label_eq ''opendoor'' aand nxt (output_eq [Some (Num 1)]))) until (label_eq ''motorstop'')) (watch lift i)"
  oops

end
