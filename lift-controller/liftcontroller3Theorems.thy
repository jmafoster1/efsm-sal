theorem test :
"alw ((ev (nxt ((label_eq ''opendoor '') aand (nxt (output_eq
    [Some(''true''),
    Some(10)]))))) impl ((not (nxt ((label_eq ''opendoor '') aand
    (nxt (output_eq [Some(''true''),
    Some(10)]))))) until(((label_eq ''motorstop'') or (nxt
    (output_eq [Some(''true''), Some(10)]))))))
(watch lift i)"
oops

