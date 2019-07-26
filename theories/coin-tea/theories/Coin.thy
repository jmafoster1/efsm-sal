theory Coin
imports "../../EFSM"
begin

text_raw{*\snip{coin}{1}{2}{%*}
definition coin :: transition where
"coin \<equiv> \<lparr>
          Label = (STR ''coin''),
          Arity = 0,
          Guard = [],
          Outputs = [],
          Updates = [(1, (Plus (V (R 1)) (L (Num 1))))]
        \<rparr>"
text_raw{*}%endsnip*}

end