theory Nat_Language
  imports "../WP_Typed_Rely_Guarantee"
begin

datatype ('Addr) aexp = 
  Load "'Addr" 
  | Nat "nat" 
  | UExp "nat \<Rightarrow> nat" "'Addr aexp"
  | BExp "'Addr aexp" "nat \<Rightarrow> nat \<Rightarrow> nat" "'Addr aexp" 

datatype 'Addr bexp =
  true
  | false
  | Conj "'Addr bexp" "'Addr bexp"
  | Disj "'Addr bexp" "'Addr bexp"
  | Not  "'Addr bexp"
  | UCmp "nat \<Rightarrow> bool" "'Addr aexp"
  | BCmp "'Addr aexp" "nat \<Rightarrow> nat \<Rightarrow> bool" "'Addr aexp"

fun
  eval\<^sub>A :: "('Addr,nat) Mem \<Rightarrow> 'Addr aexp \<Rightarrow> nat"
where
  "eval\<^sub>A mem (Load v) = mem v" |
  "eval\<^sub>A mem (Nat c) = c" |
  "eval\<^sub>A mem (UExp f a) = f (eval\<^sub>A mem a)" |
  "eval\<^sub>A mem (BExp a f b) = f (eval\<^sub>A mem a) (eval\<^sub>A mem b)"

fun
  eval\<^sub>B :: "('Addr,nat) Mem \<Rightarrow> 'Addr bexp \<Rightarrow> bool"
where
  "eval\<^sub>B mem (Conj P Q) = (eval\<^sub>B mem P \<and> eval\<^sub>B mem Q)" |
  "eval\<^sub>B mem (Disj P Q) = (eval\<^sub>B mem P \<or> eval\<^sub>B mem Q)" |
  "eval\<^sub>B mem (Not P) = (\<not> eval\<^sub>B mem P)" |
  "eval\<^sub>B mem (UCmp f a) = f (eval\<^sub>A mem a)" |
  "eval\<^sub>B mem (BCmp a f b) = f (eval\<^sub>A mem a) (eval\<^sub>A mem b)" |
  "eval\<^sub>B mem (true) = True" |
  "eval\<^sub>B mem (false) = False"

fun
  lift\<^sub>A :: "'Addr aexp \<Rightarrow> ('Addr,nat) exp"
where
  "lift\<^sub>A (Load v) = Var v" |
  "lift\<^sub>A (Nat n) = Const n" |
  "lift\<^sub>A (UExp f a) = Op (\<lambda>x y. f x) (lift\<^sub>A a) (Const 0)" |
  "lift\<^sub>A (BExp e\<^sub>1 f e\<^sub>2) = Op (f) (lift\<^sub>A e\<^sub>1) (lift\<^sub>A e\<^sub>2)" 

fun
  lift\<^sub>B :: "'Addr bexp \<Rightarrow> ('Addr,nat) pred"
where
  "lift\<^sub>B (Conj P Q) = (lift\<^sub>B P \<and>\<^sub>p lift\<^sub>B Q)" |
  "lift\<^sub>B (Disj P Q) = (lift\<^sub>B P \<or>\<^sub>p lift\<^sub>B Q)" |
  "lift\<^sub>B (Not P) = (PNeg (lift\<^sub>B P))" |
  "lift\<^sub>B (UCmp f a) = (PCmp (\<lambda>x y. f x) (lift\<^sub>A a) (Const 0))" |
  "lift\<^sub>B (BCmp a f b) = (PCmp f (lift\<^sub>A a) (lift\<^sub>A b))" |
  "lift\<^sub>B (true) = (Pb True)" |
  "lift\<^sub>B (false) = (Pb False)"

fun 
  vars\<^sub>A :: "'Addr aexp \<Rightarrow> 'Addr list"
where
  "vars\<^sub>A (Load v) = [v]" |
  "vars\<^sub>A (Nat n) = []" |
  "vars\<^sub>A (UExp f a) = (vars\<^sub>A a)" |
  "vars\<^sub>A (BExp a f b) = (vars\<^sub>A a @ vars\<^sub>A b)"

fun 
  vars\<^sub>B :: "'Addr bexp \<Rightarrow> 'Addr list"
where
  "vars\<^sub>B (Conj P Q) = (vars\<^sub>B P @ vars\<^sub>B Q)" |
  "vars\<^sub>B (Disj P Q) = (vars\<^sub>B P @ vars\<^sub>B Q)" |
  "vars\<^sub>B (Not P) = (vars\<^sub>B P)" |
  "vars\<^sub>B (UCmp f a) = (vars\<^sub>A a)" |
  "vars\<^sub>B (BCmp a f b) = (vars\<^sub>A a @ vars\<^sub>A b)" |
  "vars\<^sub>B _ = []"

(* Common operations *)
abbreviation inc :: "'Addr \<Rightarrow> ('Addr, nat) rpred" where
  "inc y \<equiv> (PCmp (\<le>) (Var y\<^sup>o) (Var y`))"

definition const :: "'Addr \<Rightarrow> ('Addr, nat) rpred" where
  "const y \<equiv> (PCmp (=) (Var (Orig y)) (Var (Prime y))) \<and>\<^sub>p (Low (Orig y) \<longrightarrow>\<^sub>p Low (Prime y))"

definition invar :: "('Addr, nat) pred \<Rightarrow> ('Addr, nat) rpred" where
  "invar P \<equiv> orig P \<longrightarrow>\<^sub>p Primed_Typed_Predicate_Language.prime P"

locale nat_language = 
  fixes all_vars :: "'Addr list"
  and locals :: "'Addr list"
  assumes all: "UNIV = set all_vars"

context nat_language
begin

named_theorems nat_language_simp

lemma nl_eval\<^sub>A [nat_language_simp]:
  "eval mem (lift\<^sub>A e) = eval\<^sub>A mem e"
  by (induct e, auto)

lemma nl_eval\<^sub>B [nat_language_simp]:
  "test mem \<Gamma> (lift\<^sub>B e) = eval\<^sub>B mem e"
  by (induct e, auto simp: nl_eval\<^sub>A)

lemma nl_vars\<^sub>A [nat_language_simp]:
  "set (vars\<^sub>A e) = vars\<^sub>e (lift\<^sub>A e)"
  by (induct e, auto)

lemma nl_vars\<^sub>B [nat_language_simp]:
  "set (vars\<^sub>B e) = vars\<^sub>p (lift\<^sub>B e)"
  by (induct e, auto simp: nl_vars\<^sub>A)

end

sublocale nat_language \<subseteq> type_rg_if_impl all_vars eval\<^sub>A eval\<^sub>B lift\<^sub>A lift\<^sub>B vars\<^sub>A vars\<^sub>B Not locals
  by unfold_locales (auto simp: all nat_language_simp)

method allvars_tac = (intro UNIV_eq_I; case_tac xa; simp)

context nat_language
begin

method try_refl = (insert context_order_refl; assumption)?

lemma prepare[intro]: 
  assumes "\<forall>m \<Gamma>. test m \<Gamma> (P \<longrightarrow>\<^sub>p Q)"
  shows "P \<turnstile>\<^sub>p Q"
  using assms unfolding entail_def by auto

named_theorems RGSpec

named_theorems RGSimp
declare step_def [RGSimp]
declare str_env_def [RGSimp]
declare invar_def [RGSimp]
declare const_def [RGSimp]
declare Primed_Typed_Predicate_Language.prime_def [RGSimp]
declare type_ord_def [RGSimp]

method wf_solve = 
  (match conclusion in "transitive R" for R \<Rightarrow> \<open>simp add: transitive_def; intro impI allI; normalization; clarsimp\<close>) |
  (match conclusion in "reflexive G" for G \<Rightarrow> \<open>simp add: reflexive_def; intro impI allI; normalization; clarsimp\<close>) |
  (match conclusion in "wf\<^sub>\<L> L" for L \<Rightarrow> \<open>simp add: wf\<^sub>\<L>_def, intro allI, case_tac x, simp_all\<close>) |
  (match conclusion in "str_env (step G)" for G \<Rightarrow> \<open>simp add: RGSimp\<close>) |
  (match conclusion in "onlyGlobals R" for R \<Rightarrow> \<open>normalization; simp add: RGSimp\<close>)

method wf_spec = (solves \<open>insert RGSpec, simp\<close> | wf_solve)

method stable = ((unfold asn_def)?, intro allI impI, normalization, clarsimp, argo?)

method solve = 
  (match conclusion in "P \<turnstile>\<^sub>p Q" for P Q \<Rightarrow> \<open>intro prepare allI\<close>; normalization; clarsimp?) |
  (match conclusion in "\<forall>m \<Gamma> m' \<Gamma>' mh \<Gamma>h. test (m \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>h) P \<and> test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R \<longrightarrow> test (m' \<Oplus> mh) (\<Gamma>' \<Oplus> \<Gamma>h) P" for P R \<Rightarrow> \<open>stable\<close>)

method act_intro = (rule actWP_rewrite)

method step =
  (match conclusion in "valid R G \<L> P (c\<^sub>2 ; c\<^sub>1) Q" for R G P c\<^sub>1 c\<^sub>2 \<L> Q \<Rightarrow> \<open>rule seqWP\<close>) |
  (match conclusion in "valid R G \<L> P (Act \<alpha>) Q" for R G P \<alpha> \<L> Q \<Rightarrow> \<open>act_intro\<close>, try_refl) |
  (match conclusion in "valid R G \<L> P (Skip) Q" for R G P \<L> Q  \<Rightarrow> \<open>rule skipWP_rewrite\<close>, try_refl) |
  (match conclusion in "valid R G \<L> P (DoWhile c I g) Q" for R G P \<L> c I g Q  \<Rightarrow> \<open>rule doWhileWP\<close>, try_refl) |
  (match conclusion in "valid R G \<L> P (While c I g) Q" for R G P \<L> c I g Q  \<Rightarrow> \<open>rule whileWP_rewrite\<close>, try_refl) |
  (match conclusion in "valid R G \<L> P (If c I g) Q" for R G P \<L> c I g Q  \<Rightarrow> \<open>rule ifWP_rewrite\<close>, try_refl) 

method pre = (rule if_secureI, wf_spec, wf_spec, wf_spec, wf_spec, wf_spec, wf_spec, wf_spec)
method stepall = (find_goal \<open>step\<close>)+
method vcg = (pre, stepall)
method solveall = (solve+)
method vcgsolve = (vcg, solveall, (intro conjI impI)?)

end

end