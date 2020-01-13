theory LTL_Exp
imports Main "../efsm-isabelle/Value" FinFun.FinFun
begin

unbundle finfun_syntax

datatype ltl_vname = I nat | O nat | R nat

datatype ltl_aexp = L "value" | V ltl_vname | Plus ltl_aexp ltl_aexp | Minus ltl_aexp ltl_aexp | Times ltl_aexp ltl_aexp

type_synonym registers = "nat \<Rightarrow>f value option"
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

fun aval :: "ltl_aexp \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> value option" where
  "aval (L x) _ _ _ = Some x" |
  "aval (V (I x)) i _ _ = Some (i ! x)" |
  "aval (V (ltl_vname.O x)) _ _ p = p ! x" |
  "aval (V (R x)) _ r _ = r $ x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) i r p = value_plus (aval a\<^sub>1 i r p)(aval a\<^sub>2 i r p)" |
  "aval (Minus a\<^sub>1 a\<^sub>2) i r p = value_minus (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)" |
  "aval (Times a\<^sub>1 a\<^sub>2) i r p = value_times (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)"

datatype ltl_gexp = Bc bool | Eq ltl_aexp ltl_aexp | Gt ltl_aexp ltl_aexp | In ltl_vname "value list" | Null ltl_aexp | Nor ltl_gexp ltl_gexp

fun gval :: "ltl_gexp \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> trilean" where
  "gval (Bc True) _ _ _ = true" |
  "gval (Bc False) _ _ _ = false" |
  "gval (Gt a\<^sub>1 a\<^sub>2) i r p = value_gt (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) i r p = value_eq (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)" |
  "gval (In (I n) l) i r p = (if (i ! n) \<in> set l then true else false)" |
  "gval (In (R n) l) i r p = (if (r $ n) \<in> set (map Some l) then true else false)" |
  "gval (In (ltl_vname.O n) l) i r p = (if (p ! n) \<in> set (map Some l) then true else false)" |
  "gval (Null a) i r p = value_eq (aval a i r p) None" |
  "gval (Nor a\<^sub>1 a\<^sub>2) i r p = \<not>\<^sub>? ((gval a\<^sub>1 i r p) \<or>\<^sub>? (gval a\<^sub>2 i r p))"

definition "Lt a b = Gt b a"

end