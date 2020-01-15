theory LTL_Exp
imports Main "../efsm-isabelle/EFSM" "../efsm-isabelle/VName" FinFun.FinFun
begin

no_notation relcomp (infixr "O" 75) and comp (infixl "o" 55)

datatype ltl_vname = Ip nat | Op nat | Rg nat

type_synonym ltl_gexp = "ltl_vname gexp"

definition join_iro :: "value list \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> ltl_vname datastate" where
  "join_iro i r o = (\<lambda>x. case x of
    Rg n \<Rightarrow> r $ n |
    Ip n \<Rightarrow> Some (i ! n) |
    Op n \<Rightarrow> o ! n
  )"

(*

datatype ltl_aexp = L "value" | V ltl_vname | Plus ltl_aexp ltl_aexp | Minus ltl_aexp ltl_aexp | Times ltl_aexp ltl_aexp

type_synonym registers = "nat \<Rightarrow>f value option"
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

fun aval :: "ltl_aexp \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> value option" where
  "aval (L x) _ _ _ = Some x" |
  "aval (V v) i r p = (case v of
    Inl (I n) \<Rightarrow> Some (i ! n) |
    Inl (R n) \<Rightarrow> r $ n |
    Inr (op.O n) \<Rightarrow> p ! n
  )" |
  "aval (Plus a\<^sub>1 a\<^sub>2) i r p = value_plus (aval a\<^sub>1 i r p)(aval a\<^sub>2 i r p)" |
  "aval (Minus a\<^sub>1 a\<^sub>2) i r p = value_minus (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)" |
  "aval (Times a\<^sub>1 a\<^sub>2) i r p = value_times (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)"

datatype ltl_gexp = Bc bool | Eq ltl_aexp ltl_aexp | Gt ltl_aexp ltl_aexp | In ltl_vname "value list" | Null ltl_aexp | Nor ltl_gexp ltl_gexp

fun gval :: "ltl_gexp \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> trilean" where
  "gval (Bc True) _ _ _ = true" |
  "gval (Bc False) _ _ _ = false" |
  "gval (Gt a\<^sub>1 a\<^sub>2) i r p = value_gt (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) i r p = value_eq (aval a\<^sub>1 i r p) (aval a\<^sub>2 i r p)" |
  "gval (In v l) i r p = (case v of
    Inl (I n) \<Rightarrow> (if (i ! n) \<in> set l then true else false) |
    Inl (R n) \<Rightarrow> (if (r $ n) \<in> set (map Some l) then true else false) |
    Inr (op.O n) \<Rightarrow>(if (p ! n) \<in> set (map Some l) then true else false)
  )" |
  "gval (Null a) i r p = value_eq (aval a i r p) None" |
  "gval (Nor a\<^sub>1 a\<^sub>2) i r p = \<not>\<^sub>? ((gval a\<^sub>1 i r p) \<or>\<^sub>? (gval a\<^sub>2 i r p))"

definition "Lt a b = Gt b a"
*)

end