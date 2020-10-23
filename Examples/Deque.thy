theory Deque
  imports Nat_Language
begin

section \<open>Define the variables\<close>
datatype addr = h | t | task | level | head | tail | r | l\<^sub>0 | l\<^sub>1 | l\<^sub>2 | t\<^sub>0 | t\<^sub>1 | t\<^sub>2 | public | z | x
definition all_vars
  where "all_vars = [h, t, task, level, head, tail, r, l\<^sub>0, l\<^sub>1, l\<^sub>2, t\<^sub>0, t\<^sub>1, t\<^sub>2, public, z, x]"
definition locals
  where "locals = [h, t, task, level, r]"

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
  "\<L> tail = true" |
  "\<L> head = true" |
  "\<L> l\<^sub>0 = true" |
  "\<L> l\<^sub>1 = true" |
  "\<L> l\<^sub>2 = true" |
  "\<L> t\<^sub>0 = UCmp (\<lambda>x. x = 0) (Load l\<^sub>0)" |
  "\<L> t\<^sub>1 = UCmp (\<lambda>x. x = 0) (Load l\<^sub>1)" |
  "\<L> t\<^sub>2 = UCmp (\<lambda>x. x = 0) (Load l\<^sub>2)" |
  "\<L> public = true" |
  "\<L> z = true" |
  "\<L> _ = false"

definition P\<^sub>0 :: "(addr,nat) pred"
  where "P\<^sub>0 \<equiv> PCmp (\<lambda>x y. even x) (Var z) (Const 0)"

definition "R \<equiv>  (const z) \<and>\<^sub>p (const t\<^sub>0) \<and>\<^sub>p (const l\<^sub>0) \<and>\<^sub>p (const t\<^sub>1) \<and>\<^sub>p (const l\<^sub>1) \<and>\<^sub>p (const t\<^sub>2) \<and>\<^sub>p (const l\<^sub>2)"

definition "G \<equiv> inc z 
            \<and>\<^sub>p ((PCmp (\<lambda>x y. even x) (Var z\<^sup>o) (Const 0) \<and>\<^sub>p PCmp (=) (Var (Orig z)) (Var (Prime z))) \<longrightarrow>\<^sub>p (PCmp (=) (Var (Orig l\<^sub>0)) (Var (Prime l\<^sub>0)))) 
            \<and>\<^sub>p ((PCmp (\<lambda>x y. even x) (Var z\<^sup>o) (Const 0) \<and>\<^sub>p PCmp (=) (Var (Orig z)) (Var (Prime z))) \<longrightarrow>\<^sub>p (PCmp (=) (Var (Orig l\<^sub>1)) (Var (Prime l\<^sub>1)))) 
            \<and>\<^sub>p ((PCmp (\<lambda>x y. even x) (Var z\<^sup>o) (Const 0) \<and>\<^sub>p PCmp (=) (Var (Orig z)) (Var (Prime z))) \<longrightarrow>\<^sub>p (PCmp (=) (Var (Orig l\<^sub>2)) (Var (Prime l\<^sub>2))))"

lemma [natlang.RGSpec]:
  "transitive G"
  by natlang.wf_spec (intro conjI impI; auto)

lemma [natlang.RGSpec]:
  "str_env (step G)"
  by natlang.wf_spec (auto simp: G_def)

declare G_def [natlang.RGSimp]
declare R_def [natlang.RGSimp]

subsection \<open>Constants\<close>

definition "levels = [l\<^sub>0, l\<^sub>1, l\<^sub>2]"
definition "tasks = [t\<^sub>0, t\<^sub>1, t\<^sub>2]"
definition "L = Nat 3"
definition "fail = Nat 0"
definition "none = Nat 0"

subsection \<open>Functions\<close>

lemma put:
  "\<L>,P\<^sub>0 \<and>\<^sub>p Low level \<and>\<^sub>p (PCmp (=) (Var level) (Const 0) \<longrightarrow>\<^sub>p (Low task)) \<turnstile>
   R: R
   G: G
   {
    t := Load tail;
    z := BExp (Load z) (+) (Nat 1);
    tasks IN (BExp (Load t) (mod) L) := Nat 0;
    levels IN (BExp (Load t) (mod) L) := Load level;
    tasks IN (BExp (Load t) (mod) L) := Load task;
    z := BExp (Load z) (+) (Nat 1);
    tail := BExp (Load t) (+) (Nat 1)}"
  by natlang.vcgsolve (metis mod_Suc n_not_Suc_n numeral_2_eq_2)+

lemma take:
  "\<L>,P\<^sub>0 \<turnstile>
   R: Pb True
   G: G
   {
    t := BExp (Load tail) (-) (Nat 1);
    tail := Load t;
    h := Load head;
    IF \<lbrace>BCmp (Load h) (\<le>) (Load t)\<rbrace>
    THEN
      task := tasks IN BExp (Load t) (mod) L;
      IF \<lbrace>BCmp (Load h) (=) (Load t)\<rbrace>
      THEN
        IF NCAS head (Load h) (BExp (Load h) (+) (Nat 1))
        THEN task := Nat 0
        ELSE Skip
        FI ;
        tail := BExp (Load h) (+) (Nat 1)
      ELSE Skip
      FI 
    ELSE
      task := Nat 0;
      tail := Load h
    FI
   }"
  by natlang.vcgsolve 

lemma steal:
  "\<L>,P\<^sub>0 \<turnstile>
   R: G
   G: R
   {
    h := Load head;
    t := Load tail;
    IF \<lbrace>BCmp (Load h) (<) (Load t)\<rbrace>
    THEN
      DO
        DO
          r := Load z
        INV {Low r \<and>\<^sub>p Low h \<and>\<^sub>p PCmp (\<le>) (Var r) (Var z)} 
        WHILE \<lbrace>Not (UCmp even (Load r))\<rbrace>;
        level := levels IN BExp (Load h) (mod) L;
        IF \<lbrace>BCmp (Load level) (=) (Nat 0)\<rbrace>
        THEN task := tasks IN BExp (Load h) (mod) L
        ELSE task := fail
        FI 
      INV {Low r \<and>\<^sub>p Low h \<and>\<^sub>p (PCmp (=) (Var r) (Var z) \<longrightarrow>\<^sub>p Low task)}     
      WHILE \<lbrace>BCmp (Load z) (\<noteq>) (Load r)\<rbrace>;
      IF NCAS head (Load h) (BExp (Load h) (+) (Nat 1))
      THEN task := fail
      ELSE Skip
      FI
    ELSE
      task := none
    FI ;
    public := Load task 
   }"
  by natlang.vcgsolve (metis (no_types, lifting) le_antisym le_trans)+

end