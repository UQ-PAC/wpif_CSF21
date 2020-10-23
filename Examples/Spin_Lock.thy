theory Spin_Lock
  imports Nat_Language
begin

section \<open>Define the variables\<close>
datatype addr = r\<^sub>1 | r\<^sub>2 | x | z | secret | public 
definition all_vars
  where "all_vars = [r\<^sub>1, r\<^sub>2, x, z, secret, public]"
definition locals
  where "locals = [r\<^sub>1, r\<^sub>2]"

section \<open>Establish the language & logic\<close>
global_interpretation natlang: nat_language all_vars locals
  defines \<Gamma>\<^sub>a = natlang.\<Gamma>\<^sub>a
      and \<Gamma>\<^sub>b = natlang.\<Gamma>\<^sub>b
      and wp = natlang.wp
      and stabilize = natlang.stabilize
      and wp\<^sub>Q = natlang.wp\<^sub>Q
      and guar = natlang.guar
      and PO = natlang.PO
      and secureUpd = natlang.secureUpd
      and ctrled = natlang.ctrled
      and if_secure = natlang.if_secure
      and wellformed = natlang.wellformed
      and negate = natlang.negate
      and var_policy = natlang.var_policy
      and \<Gamma>\<^sub>e = natlang.\<Gamma>\<^sub>e
      and invar = natlang.invar
      and low\<^sub>v = natlang.low\<^sub>v
      and wf\<^sub>\<L> = natlang.wf\<^sub>\<L>
      and step = natlang.step
      and str_env = natlang.str_env
      and onlyGlobals = natlang.onlyGlobals
  apply unfold_locales unfolding all_vars_def by allvars_tac

syntax
  "_Assign" :: "'addr \<Rightarrow> ('addr) aexp \<Rightarrow> ('addr, nat, 'addr aexp, 'addr bexp) WPLang"
    ("(_ :=/ _)" [70, 65] 61)
  "_Store" :: "'addr \<Rightarrow> ('addr) aexp \<Rightarrow> ('addr) aexp \<Rightarrow> ('addr, nat, 'addr aexp, 'addr bexp) WPLang"
    ("(_ IN _ :=/ _)" [70, 70, 65] 61)
  "_Load" :: "'addr \<Rightarrow> ('addr) list \<Rightarrow> ('addr) aexp \<Rightarrow> ('addr, nat, 'addr aexp, 'addr bexp) WPLang"
    ("(_ :=/ _ IN/ _)" [70, 70, 70] 61)
  "_Secure" :: "('addr,nat) rpred \<Rightarrow> ('addr,nat) rpred \<Rightarrow> ('addr \<Rightarrow> 'addr bexp) \<Rightarrow> ('addr,nat) pred \<Rightarrow> ('addr, nat, 'addr aexp, 'addr bexp) WPLang \<Rightarrow> bool"
    ("(0_,_ \<turnstile> R: _ /G: _ /{_})" [0, 0, 0, 0, 0] 61)

translations
  "x := a" \<rightharpoonup> "CONST Act (CONST Assign x a)"
  "x IN i := a" \<rightharpoonup> "CONST Act (CONST Store x i a)"
  "r := a IN i" \<rightharpoonup> "CONST Act (CONST Action.Load r a i)"
  "L,P \<turnstile> R: RP G: GP {c}" \<rightharpoonup> "CONST if_secure RP GP L P c"

section \<open>Example\<close>

subsection \<open>Specification\<close>

fun \<L> :: "addr \<Rightarrow> addr bexp" where
  "\<L> z = true" |
  "\<L> public = true" |
  "\<L> x = UCmp (\<lambda>x. x \<noteq> 1) (Load z)" |
  "\<L> _ = false"

definition P\<^sub>0 :: "(addr,nat) pred"
  where "P\<^sub>0 \<equiv> Pb True"

subsection \<open>Functions\<close>

lemma secret_write:
  "\<L>,P\<^sub>0 \<turnstile>
   R: invar (Low x) \<and>\<^sub>p (PCmp (=) (Var z\<^sup>o) (Const 1) \<longrightarrow>\<^sub>p (const z))
   G: PCmp (=) (Var z\<^sup>o) (Const 2) \<longrightarrow>\<^sub>p (const z \<and>\<^sub>p const x)
   {
    WHILE NCAS z (Nat 0) (Nat 1)
    INV {Pb True}
    DO
      WHILE \<lbrace>BCmp (Load z) (\<noteq>) (Nat 0)\<rbrace>
      INV {Pb True} DO Skip OD
    OD;
    x := Load secret;
    x := Nat 0;
    z := Nat 0}"
  by natlang.vcgsolve

lemma public_read:
  "\<L>,P\<^sub>0 \<turnstile>
   R: PCmp (=) (Var z\<^sup>o) (Const 2) \<longrightarrow>\<^sub>p (const z \<and>\<^sub>p invar (Low x))
   G: const x \<and>\<^sub>p (PCmp (=) (Var z\<^sup>o) (Const 1) \<longrightarrow>\<^sub>p (const z))
   {IF CAS z (Nat 0) (Nat 2)
    THEN public := Load x; z := Nat 0
    ELSE Skip
    FI}"
  by natlang.vcgsolve

lemma public_write:
  "\<L>,P\<^sub>0 \<turnstile>
   R: Pb True
   G: const z \<and>\<^sub>p invar (Low x)
   { x := Load public }"
  by natlang.vcgsolve

lemma secret_read:
  "\<L>,P\<^sub>0 \<turnstile>
   R: Pb True
   G: const x \<and>\<^sub>p const z
   { secret := Load x }"
  by natlang.vcgsolve

end