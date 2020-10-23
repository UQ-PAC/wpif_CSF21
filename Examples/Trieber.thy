theory Trieber
  imports Nat_Language
begin

section \<open>Define the variables\<close>
datatype addr = i | j | r | val | level | head | l\<^sub>0 | l\<^sub>1 | l\<^sub>2 | t\<^sub>0 | t\<^sub>1 | t\<^sub>2 | n\<^sub>0 | n\<^sub>1 | n\<^sub>2 | public | x | exit
definition all_vars
  where "all_vars = [i, j, r, val, level, exit, head, l\<^sub>0, l\<^sub>1, l\<^sub>2, t\<^sub>0, t\<^sub>1, t\<^sub>2, n\<^sub>0, n\<^sub>1, n\<^sub>2, public, x]"
definition locals
  where "locals = [j, r, val, level, x, exit]"

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
  "\<L> head = true" |
  "\<L> l\<^sub>0 = true" |
  "\<L> l\<^sub>1 = true" |
  "\<L> l\<^sub>2 = true" |
  "\<L> n\<^sub>0 = true" |
  "\<L> n\<^sub>1 = true" |
  "\<L> n\<^sub>2 = true" |
  "\<L> t\<^sub>0 = UCmp (\<lambda>x. x = 0) (Load l\<^sub>0)" |
  "\<L> t\<^sub>1 = UCmp (\<lambda>x. x = 0) (Load l\<^sub>1)" |
  "\<L> t\<^sub>2 = UCmp (\<lambda>x. x = 0) (Load l\<^sub>2)" |
  "\<L> public = true" |
  "\<L> _ = false"

definition "P\<^sub>0 \<equiv> (PCmp (=) (Var i) (Const 0) \<longrightarrow>\<^sub>p PCmp (=) (Var l\<^sub>0) (Const 1)) \<and>\<^sub>p
                 (PCmp (=) (Var i) (Const 1) \<longrightarrow>\<^sub>p PCmp (=) (Var l\<^sub>1) (Const 1)) \<and>\<^sub>p
                 (PCmp (=) (Var i) (Const 2) \<longrightarrow>\<^sub>p PCmp (=) (Var l\<^sub>2) (Const 1)) "

definition "R \<equiv> (PCmp (=) (Var i\<^sup>o) (Const 0) \<longrightarrow>\<^sub>p (const l\<^sub>0 \<and>\<^sub>p const t\<^sub>0)) \<and>\<^sub>p
                 (PCmp (=) (Var i\<^sup>o) (Const 1) \<longrightarrow>\<^sub>p (const l\<^sub>1 \<and>\<^sub>p const t\<^sub>1)) \<and>\<^sub>p
                 (PCmp (=) (Var i\<^sup>o) (Const 2) \<longrightarrow>\<^sub>p (const l\<^sub>2 \<and>\<^sub>p const t\<^sub>2)) \<and>\<^sub>p
                 const i"

definition "G \<equiv> (PCmp (=) (Var l\<^sub>0\<^sup>o) (Const (0 :: nat)) \<longrightarrow>\<^sub>p PCmp (=) (Var l\<^sub>0`) (Const 0)) \<and>\<^sub>p
                 (PCmp (=) (Var l\<^sub>1\<^sup>o) (Const 0) \<longrightarrow>\<^sub>p PCmp (=) (Var l\<^sub>1`) (Const 0)) \<and>\<^sub>p
                 (PCmp (=) (Var l\<^sub>2\<^sup>o) (Const 0) \<longrightarrow>\<^sub>p PCmp (=) (Var l\<^sub>2`) (Const 0))"

declare G_def [natlang.RGSimp]
declare R_def [natlang.RGSimp]

subsection \<open>Constants\<close>

definition "levels = [l\<^sub>0, l\<^sub>1, l\<^sub>2]"
definition "vals = [t\<^sub>0, t\<^sub>1, t\<^sub>2]"
definition "nexts = [n\<^sub>0, n\<^sub>1, n\<^sub>2]"
definition "L = Nat 3"

subsection \<open>Functions\<close>

lemma put:
  "\<L>,P\<^sub>0 \<and>\<^sub>p Low i \<and>\<^sub>p Low level \<and>\<^sub>p (PCmp (=) (Var level) (Const 0) \<longrightarrow>\<^sub>p (Low val)) \<turnstile>
   R: R
   G: G
   {
    vals IN Load i := Nat 0;
    levels IN Load i := Load level;
    vals IN Load i := Load val;
    DO
      j := Load head;
      nexts IN Load i := Load j
    INV {Low j \<and>\<^sub>p Low i}
    WHILE NCAS head (Load j) (Load i)
   }"
  by natlang.vcgsolve
  
lemma pop:
  "\<L>,Low r \<and>\<^sub>p Low x \<and>\<^sub>p Low j \<turnstile>
   R: G
   G: R
   {
    exit := Nat 0;
    DO
      x := Load head;
      IF \<lbrace>BCmp (Load x) (<) L\<rbrace>
      THEN
        j := levels IN Load x;
        IF \<lbrace>BCmp (Load j) (=) (Nat 0)\<rbrace>
        THEN
          j := nexts IN Load x;
          r := vals IN Load x;
          IF CAS head (Load x) (Load j)
          THEN exit := Nat 1
          ELSE Skip
          FI
        ELSE Skip
        FI
      ELSE Skip
      FI
    INV {Low r \<and>\<^sub>p Low exit}
    WHILE \<lbrace>BCmp (Load exit) (=) (Nat 0)\<rbrace>;
    public := Load r
   }"
  by natlang.vcgsolve

end