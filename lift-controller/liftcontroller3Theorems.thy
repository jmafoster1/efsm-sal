theorem test2 :
"(alw ((not ((label_eq ''opendoor '') aand (nxt (output_eq
    [Some(''true''),
    Some(10)])))) until((label_eq ''motorstop'') or (output_eq
    [Some(''true''),
    Some(10)])))) or (alw (not ((label_eq ''opendoor '') aand (nxt
    (output_eq [Some(''true''), Some(10)])))))
(watch lift i)"
oops

