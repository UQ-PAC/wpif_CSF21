theory WP_Typed_Rely_Guarantee
  imports Typed_Rely_Guarantee Language_Lift Indexed_Typed_Predicate_Language "HOL-Eisbach.Eisbach"
begin

text \<open>
Combine the deeply embedded predicate language with the abstract typed rely guarantee information
flow logic to generate an 'executable' version, based on the weakest-pre rules found in the paper.

TODO:
  - Is it nicer to enforce restrictions on the types of R and G in the type system? 
\<close>

section \<open>Language Definition\<close>

type_synonym ('Var,'Bexp) policy = "'Var \<Rightarrow> 'Bexp"

datatype ('Var, 'Val, 'Aexp, 'Bexp) WPLang =
  Skip
| Act "('Var, 'Aexp, 'Bexp) Action"
| Seq "('Var, 'Val, 'Aexp, 'Bexp) WPLang" "('Var, 'Val, 'Aexp, 'Bexp) WPLang" ("(_;/ _)"      [60,61] 60)
| If "('Var, 'Aexp, 'Bexp) Action" "('Var, 'Val, 'Aexp, 'Bexp) WPLang" "('Var, 'Val, 'Aexp, 'Bexp) WPLang" ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
| While "('Var, 'Aexp, 'Bexp) Action" "('Var,'Val) pred"  "('Var, 'Val, 'Aexp, 'Bexp) WPLang" ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)
| DoWhile "('Var, 'Val, 'Aexp, 'Bexp) WPLang" "('Var,'Val) pred" "('Var, 'Aexp, 'Bexp) Action" ("(1DO _/ INV {_} //WHILE _ )"  [0,0,100] 61)

section \<open>Initial Implementation Definitions\<close>
text \<open>
  Introduce sufficient definitions and lemmas to establish the sublocale 
  with the abstract type system.
  Currently this is only requires the concept of a information flow update,
  which describes how the logic updates \<Gamma> entries due to an action.
\<close>
locale type_rg_if_impl = 
  language_lift all_vars eval\<^sub>A eval\<^sub>B lift\<^sub>A lift\<^sub>B vars\<^sub>A vars\<^sub>B not
  for all_vars :: "'Var list"
  and eval\<^sub>A :: "('Var, nat) Mem \<Rightarrow> 'Aexp \<Rightarrow> nat"
  and eval\<^sub>B :: "('Var, nat) Mem \<Rightarrow> 'Bexp \<Rightarrow> bool"
  and lift\<^sub>A :: "'Aexp \<Rightarrow> ('Var,nat) exp"
  and lift\<^sub>B :: "'Bexp \<Rightarrow> ('Var,nat) pred"
  and vars\<^sub>A :: "'Aexp \<Rightarrow> 'Var list"
  and vars\<^sub>B :: "'Bexp \<Rightarrow> 'Var list"
  and not :: "'Bexp \<Rightarrow> 'Bexp"
  and locals :: "'Var list"

context type_rg_if_impl
begin

text \<open>Define how the type context is updated for each action\<close>
fun flow
  where
    "flow (x \<leftarrow> e) m \<Gamma> = \<Gamma>(x := \<forall>v \<in> vars\<^sub>e (lift\<^sub>A e). \<Gamma> v)" |
    "flow (CAS x e\<^sub>1 e\<^sub>2) m \<Gamma> = \<Gamma>(x := \<forall>v \<in> vars\<^sub>e (lift\<^sub>A e\<^sub>2). \<Gamma> v)" |
    "flow (Store x i e) m \<Gamma> = 
      (if \<forall>v \<in> vars\<^sub>e (lift\<^sub>A i). \<Gamma> v then \<Gamma>((x ! eval\<^sub>A m i) := \<forall>v \<in> vars\<^sub>e (lift\<^sub>A e). \<Gamma> v) else 
      (\<lambda>y. if y \<in> set x then False else \<Gamma> y))" |
    "flow (Load r x i) m \<Gamma> = 
      (if \<forall>v \<in> vars\<^sub>e (lift\<^sub>A i). \<Gamma> v then \<Gamma>(r := \<Gamma> (x ! eval\<^sub>A m i)) else \<Gamma>(r := False))" |
    "flow _ _ \<Gamma> = \<Gamma>"

text \<open>Show that the type context update is sound\<close>
lemma flow_sound_impl:
  "(m\<^sub>1,m\<^sub>1') \<in> update \<alpha> \<longrightarrow> (m\<^sub>2,m\<^sub>2') \<in> update \<alpha> \<longrightarrow> type_ord  (flow \<alpha> m\<^sub>1 (m\<^sub>1 \<triangle> m\<^sub>2)) (m\<^sub>1' \<triangle> m\<^sub>2') "
proof (cases \<alpha>)
  case (Store x i e)
  have "\<forall>v\<in>vars\<^sub>e (lift\<^sub>A i). m\<^sub>1 v = m\<^sub>2 v \<Longrightarrow> eval\<^sub>A m\<^sub>1 i = eval\<^sub>A m\<^sub>2 i" using eval\<^sub>A_det by blast
  then show ?thesis using Store by (auto simp: type_ord_def mem_delta_def intro!: eval\<^sub>A_det)
next
  case (Load r x i)
  have "\<forall>v\<in>vars\<^sub>e (lift\<^sub>A i). m\<^sub>1 v = m\<^sub>2 v \<Longrightarrow> eval\<^sub>A m\<^sub>1 i = eval\<^sub>A m\<^sub>2 i" using eval\<^sub>A_det by blast
  then show ?thesis using Load by (auto simp: type_ord_def mem_delta_def)
qed  (auto simp: type_ord_def mem_delta_def intro!: eval\<^sub>A_det)

end

sublocale type_rg_if_impl \<subseteq> typed_rely_guarantee update flow
  using flow_sound_impl by unfold_locales auto

section \<open>Locale\<close>

context type_rg_if_impl
begin

abbreviation T
  where "T b \<equiv> pred\<^sub>0 (lift\<^sub>B b)"

abbreviation F
  where "F b \<equiv> pred\<^sub>0 (lift\<^sub>B (not b))"

abbreviation var_policy ("_:::_" [1000,100] 100)
  where "var_policy \<L> x \<equiv> lift\<^sub>B (\<L> x)"

abbreviation pol
  where "pol \<L> \<equiv> forVars all_vars (\<lambda>y. (\<L> ::: y) \<longrightarrow>\<^sub>p Low y)"

subsection \<open>Executable Implementation\<close>

text \<open>
Generate a predicate to demonstrate a low expression.
Considers the global security policy as an initial optimisation,
as some variables may be trivially low.
\<close>
definition low\<^sub>v
  where "low\<^sub>v \<L> y \<equiv> case \<L> ::: y of Pb True \<Rightarrow> Pb True | _ \<Rightarrow> Low y \<or>\<^sub>p \<L> ::: y"

lemma low\<^sub>v [simp]:
  "test m \<Gamma> (low\<^sub>v \<L> y) = test m \<Gamma> (Low y \<or>\<^sub>p \<L> ::: y)"
  unfolding low\<^sub>v_def
  apply (cases "\<L> ::: y")
          apply (auto)
  apply (case_tac x1)
  by auto

definition \<Gamma>\<^sub>e
  where "\<Gamma>\<^sub>e vs \<L> = forVars vs (low\<^sub>v \<L>)"

abbreviation \<Gamma>\<^sub>a where "\<Gamma>\<^sub>a e \<equiv> \<Gamma>\<^sub>e (vars\<^sub>A e)"
abbreviation \<Gamma>\<^sub>b where "\<Gamma>\<^sub>b e \<equiv> \<Gamma>\<^sub>e (vars\<^sub>B e)"

text \<open>
The secureUpd proof obligation ensures that the assignment of e to x does not lower the 
classification of any variables whilst they still hold classified information.
\<close>
definition ctrled
  where "ctrled x \<L> = filter (\<lambda>v. x \<in> set (vars\<^sub>B (\<L> v))) all_vars"

definition secureUpd
  where "secureUpd x e \<L> \<equiv> forVars (ctrled x \<L>) (\<lambda>y. subst\<^sub>p (\<L> ::: y) x e \<longrightarrow>\<^sub>p low\<^sub>v \<L> y)"

text \<open>
Shorthand for the security proof obligation for an assignment x := e.
v should be the variables of e. These are provided separately to facilitate optimisation.
\<close>
abbreviation PO\<^sub>a
  where "PO\<^sub>a x e v \<L> \<equiv> (\<L> ::: x \<longrightarrow>\<^sub>p \<Gamma>\<^sub>e v \<L>) \<and>\<^sub>p secureUpd x e \<L>"

text \<open>
The PO proof obligation ensures that the assignment does not directly leak information and
includes the secureUpd case.
\<close>
fun PO
  where
    "PO (x \<leftarrow> e) \<L> = PO\<^sub>a x (lift\<^sub>A e) (vars\<^sub>A e) \<L>" | 
    "PO (Guard b) \<L> = \<Gamma>\<^sub>b b \<L>" |
    "PO (NCAS x e\<^sub>1 e\<^sub>2) \<L> = (low\<^sub>v \<L> x \<and>\<^sub>p \<Gamma>\<^sub>a e\<^sub>1 \<L> \<and>\<^sub>p (PCmp (=) (Var x) (lift\<^sub>A e\<^sub>1) \<longrightarrow>\<^sub>p  PO\<^sub>a x (lift\<^sub>A e\<^sub>2) (vars\<^sub>A e\<^sub>2) \<L>))" |
    "PO (CAS x e\<^sub>1 e\<^sub>2) \<L> = (low\<^sub>v \<L> x \<and>\<^sub>p \<Gamma>\<^sub>a e\<^sub>1 \<L> \<and>\<^sub>p (PCmp (=) (Var x) (lift\<^sub>A e\<^sub>1) \<longrightarrow>\<^sub>p PO\<^sub>a x (lift\<^sub>A e\<^sub>2) (vars\<^sub>A e\<^sub>2) \<L>))" |
    "PO (Store x i e) \<L> = (\<Gamma>\<^sub>a i \<L> \<and>\<^sub>p index_assert x (lift\<^sub>A i) (\<lambda>v. PO\<^sub>a v (lift\<^sub>A e) (vars\<^sub>A e) \<L>))" |
    "PO (Load r x i) \<L> = (\<Gamma>\<^sub>a i \<L> \<and>\<^sub>p index_assert x (lift\<^sub>A i) (\<lambda>v. PO\<^sub>a r (Var v) [v] \<L>))" |
    "PO _ _ = Pb True"

text \<open>
Shorthand for the guarantee proof obligation for an assignment x := e.
v should be the variables of e. These are provided separately to facilitate optimisation.
\<close>
abbreviation guar\<^sub>a
  where "guar\<^sub>a x e v G \<L> \<equiv> unprime\<^sub>r (subst\<^sub>\<Gamma> (subst\<^sub>p G (Prime x) (orig\<^sub>e e)) (Prime x) (orig (\<Gamma>\<^sub>e v \<L>)))"

text \<open>
The guar proof obligation ensures that the operation conforms to some general guarantee condition G.
\<close>
fun guar :: "('Var,'Aexp,'Bexp) Action \<Rightarrow> ('Var,nat) rpred \<Rightarrow> ('Var,'Bexp) policy \<Rightarrow> ('Var,nat) pred" 
  where 
    "guar (x \<leftarrow> e) G \<L> = guar\<^sub>a x (lift\<^sub>A e) (vars\<^sub>A e) G \<L>" |
    "guar (CAS x e\<^sub>1 e\<^sub>2) G \<L> = (PCmp (=) (Var x) (lift\<^sub>A e\<^sub>1) \<longrightarrow>\<^sub>p guar\<^sub>a x (lift\<^sub>A e\<^sub>2) (vars\<^sub>A e\<^sub>2) G \<L>)" |
    "guar (NCAS x e\<^sub>1 e\<^sub>2) G \<L> = (PCmp (=) (Var x) (lift\<^sub>A e\<^sub>1) \<longrightarrow>\<^sub>p guar\<^sub>a x (lift\<^sub>A e\<^sub>2) (vars\<^sub>A e\<^sub>2) G \<L>)" |
    "guar (Store x i e) G \<L> = index_assert x (lift\<^sub>A i) (\<lambda>v. guar\<^sub>a v (lift\<^sub>A e) (vars\<^sub>A e) G \<L>)" |
    "guar (Load r x i) G \<L> = index_assert x (lift\<^sub>A i) (\<lambda>v. guar\<^sub>a r (Var v) ([v]) G \<L>)" |
    "guar _ G \<L> = Pb True"

text \<open>
Transform a context based on an action.
\<close>
fun wp\<^sub>Q :: "('Var,'Aexp,'Bexp) Action \<Rightarrow> ('Var,nat) ipred \<Rightarrow> ('Var,'Bexp) policy \<Rightarrow> ('Var,nat) ipred" 
  where 
    "wp\<^sub>Q (x \<leftarrow> e) Q \<L> = wp\<^sub>a x (lift\<^sub>A e) (\<Gamma>\<^sub>a e \<L>) Q" | 
    "wp\<^sub>Q (Guard b) Q \<L> = wp\<^sub>b (lift\<^sub>B b) Q" |
    "wp\<^sub>Q (CAS x e\<^sub>1 e\<^sub>2) Q \<L> = wp\<^sub>b (PCmp (=) (Var x) (lift\<^sub>A e\<^sub>1)) (wp\<^sub>a x (lift\<^sub>A e\<^sub>2) (\<Gamma>\<^sub>a e\<^sub>2 \<L>) Q)" |
    "wp\<^sub>Q (NCAS x e _) Q \<L> = wp\<^sub>b (PCmp (\<noteq>) (Var x) (lift\<^sub>A e)) Q" |
    "wp\<^sub>Q (Store x i e) Q \<L> = wp\<^sub>l x (lift\<^sub>A i) (lift\<^sub>A e) (\<Gamma>\<^sub>a e \<L>) Q" |
    "wp\<^sub>Q (Load r x i) Q \<L> = wp\<^sub>a r (list\<^sub>e x (lift\<^sub>A i)) (list\<^sub>t x (lift\<^sub>A i) (low\<^sub>v \<L>)) Q" |
    "wp\<^sub>Q _ Q \<L> = Q"

text \<open>
Generate a stable predicate by priming the state and introducing a reflexive and transitive R
to link the new current state with the original.

TODO:
  - Can we instead model the environment step as a series of assignments?
    This was its just substitutions, rather than requiring the constant introduction of R.
  - Shortcut the operation if we know P is already stable
  - Fragment the state into stable and unstable components & 
    only introduce the aspects of R that are necessary
\<close>
definition stabilize :: "('Var, nat) rpred \<Rightarrow> ('Var, nat) ipred \<Rightarrow> ('Var, nat) ipred"
  where "stabilize R P \<equiv> pred\<^sub>r (R \<and>\<^sub>p forVars locals (\<lambda>v. PImp (Low (Orig v)) (Low (Prime v)))) \<longrightarrow>\<^sub>p prime P (set locals)"

text \<open>
Define the predicate transformer for the language given a wellformed Q, R, G and \<L>.

Additional proof obligations for the loop invariant are not included as they
should be emitted as side conditions in the appropriate rules.

TODO:
  - This form does not assume a stable loop invariant and instead makes it stable.
    Is this best? Or do we place that burden on the user?
    This form allows for the user to specify any invariant and a shortcut can be applied
    in the case it happens to already be stable.
\<close>
fun wp
  where
    "wp R G \<L> Skip Q = Q" |
    "wp R G \<L> (Act \<alpha>) Q = stabilize R (pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>) \<and>\<^sub>p wp\<^sub>Q \<alpha> Q \<L>)" |
    "wp R G \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wp R G \<L> c\<^sub>1 (wp R G \<L> c\<^sub>2 Q)" |
    "wp R G \<L> (If \<alpha> c\<^sub>1 c\<^sub>2) Q = stabilize R (pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>) \<and>\<^sub>p (wp\<^sub>Q \<alpha> (wp R G \<L> c\<^sub>1 Q) \<L>) \<and>\<^sub>p (wp\<^sub>Q (negate \<alpha>) (wp R G \<L> c\<^sub>2 Q) \<L>))" |
    "wp R G \<L> (While \<alpha> I c) Q = stabilize R (pred\<^sub>0 I)" |
    "wp R G \<L> (DoWhile c I \<alpha>) Q = wp R G \<L> c (stabilize R (pred\<^sub>0 I))"

subsubsection \<open>State & Wellformedness Properties\<close>

definition state
  where "state P \<equiv> {(m,\<Gamma>). asn m \<Gamma> P}"

definition step
  where "step P \<equiv> {((m,\<Gamma>),(m',\<Gamma>')). test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') P}"

definition policy
  where "policy \<L> \<equiv> \<lambda>x. {m. eval\<^sub>B m (\<L> x)}"

lemma str_state [simp]:
  "str (state Q) \<equiv> \<forall>m \<Gamma> \<Gamma>'. asn m \<Gamma> Q \<and> \<Gamma> \<ge>\<^sub>\<Gamma> \<Gamma>' \<longrightarrow> asn m \<Gamma>' Q"
  unfolding str_def state_def by simp 

lemma str_step [simp]:
  "str_env (step Q) \<equiv> \<forall>m m' \<Gamma> \<Gamma>' \<Gamma>n \<Gamma>n'. test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') Q \<and> \<Gamma>n \<ge>\<^sub>\<Gamma> \<Gamma> \<and> \<Gamma>' \<ge>\<^sub>\<Gamma> \<Gamma>n' \<longrightarrow> test (m \<mapsto> m') (\<Gamma>n \<mapsto> \<Gamma>n') Q"
  unfolding str_env_def step_def by simp

lemma str_stable [simp]:
  "stable (state Q) (step R) = (\<forall>m m' \<Gamma> \<Gamma>'. asn m \<Gamma> Q \<and> test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R \<longrightarrow> asn m' \<Gamma>' Q)"
  unfolding stable_def state_def step_def preserve_def by auto

lemma secure_policy [simp]:
  "(m,\<Gamma>) \<in> (secure (policy \<L>)) = (\<forall>x. eval\<^sub>B m (\<L> x) \<longrightarrow> \<Gamma> x)"
  unfolding secure_def policy_def by simp

definition wf\<^sub>\<L>
  where "wf\<^sub>\<L> \<L> \<equiv> \<forall>x. x \<notin> set (vars\<^sub>B (\<L> x))"

definition localR
  where "localR \<equiv> forVars locals (\<lambda>v. PCmp (=) (Var (Orig v)) (Var (Prime v)) \<and>\<^sub>p PImp (Low (Orig v)) (Low (Prime v)))"

definition onlyGlobals
  where "onlyGlobals R \<equiv> \<forall>x \<in> vars\<^sub>p R \<union> vars\<^sub>\<Gamma> R. case x of Orig y \<Rightarrow> y \<notin> set locals | Prime y \<Rightarrow> y \<notin> set locals"

definition wellformed :: "('Var,nat) rpred \<Rightarrow> ('Var,nat) rpred \<Rightarrow> ('Var,'Bexp) policy \<Rightarrow> ('Var,nat) ipred \<Rightarrow> bool"
  where "wellformed R G \<L> Q \<equiv> 
    stable (state Q) (invSec (policy \<L>) \<inter> step (R \<and>\<^sub>p localR)) \<and> 
    str (state Q) \<and> str_env (step G) \<and> str_env (step R) \<and>
    reflexive R \<and> transitive R \<and> reflexive G \<and> wf\<^sub>\<L> \<L>
    \<and> onlyGlobals R "

lemma G_refl [intro]:
  assumes wf: "wellformed R G \<L> Q"
  shows "test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) G" 
  using wf by (auto simp: wellformed_def reflexive_def)

lemma wf\<^sub>\<L>_self [simp]:
  assumes "wellformed R G \<L> Q"
  shows "eval\<^sub>B (m(x:= e)) (\<L> x) = eval\<^sub>B m (\<L> x)"  
  using assms by (intro eval\<^sub>B_det) (auto simp: wf\<^sub>\<L>_def wellformed_def)

subsection \<open>Correctness of Implementation\<close>

lemma low_exp:
  assumes "test m (m \<triangle> m') (\<Gamma>\<^sub>a b \<L>)"
  assumes "(m,m \<triangle> m') \<in> (secure (policy \<L>))"
  shows "eval\<^sub>A m b = eval\<^sub>A m' b"
  using assms by (auto intro!: eval\<^sub>A_det simp: \<Gamma>\<^sub>e_def mem_delta_def split: pred.splits)

lemma low_guard:
  assumes "test m (m \<triangle> m') (\<Gamma>\<^sub>b b \<L>)"
  assumes "(m,m \<triangle> m') \<in> (secure (policy \<L>))"
  shows "eval\<^sub>B m b = eval\<^sub>B m' b"
  using assms by (auto intro!: eval\<^sub>B_det simp: \<Gamma>\<^sub>e_def mem_delta_def)

lemma low_guardE:
  assumes "test m (m \<triangle> m') (\<Gamma>\<^sub>b b \<L>)"
  assumes "(m,m \<triangle> m') \<in> (secure (policy \<L>))"
  obtains "eval\<^sub>B m b = eval\<^sub>B m' b"
  using assms by (auto intro!: eval\<^sub>B_det simp: \<Gamma>\<^sub>e_def mem_delta_def)

lemma low_expE:
  assumes "test m (m \<triangle> m') (\<Gamma>\<^sub>a b \<L>)"
  assumes "(m,m \<triangle> m') \<in> (secure (policy \<L>))"
  obtains "eval\<^sub>A m b = eval\<^sub>A m' b"
  using assms by (auto intro!: eval\<^sub>A_det simp: \<Gamma>\<^sub>e_def mem_delta_def)

lemma \<Gamma>_not [simp]:
  "\<Gamma>\<^sub>b (not b) = \<Gamma>\<^sub>b (b)"
  unfolding \<Gamma>\<^sub>e_def by auto

lemma secure_upd_nop:
  "v \<notin> set (ctrled x \<L>) \<Longrightarrow> eval\<^sub>B (m(x := eval m e)) (\<L> v) = eval\<^sub>B m (\<L> v)"
  by (intro eval\<^sub>B_det) (simp add: ctrled_def)

lemma secure_upd [simp]:
  "test m \<Gamma> (secureUpd x e \<L>) = (\<forall>y. test m \<Gamma> (subst\<^sub>p (\<L> ::: y) x e \<longrightarrow>\<^sub>p (Low y \<or>\<^sub>p \<L> ::: y)))"
  using secure_upd_nop unfolding secureUpd_def by fastforce

lemma \<Gamma>\<^sub>e_flow:
  assumes "(m, \<Gamma>) \<in> secure (policy \<L>)"
  assumes "test m \<Gamma> (\<Gamma>\<^sub>e e \<L>)"
  shows "\<forall>x\<in>set e. \<Gamma> x"
  using assms unfolding \<Gamma>\<^sub>e_def  by simp blast

lemma stabilize:
  "wellformed R G \<L> P \<Longrightarrow> asn m \<Gamma> (stabilize R Q) = (\<forall>m' \<Gamma>'. test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') (R \<and>\<^sub>p localR) \<longrightarrow> asn m' \<Gamma>' Q)" 
  apply (rule; clarsimp simp add: stabilize_def asn_def localR_def simp flip: test_pred\<^sub>r_alt simp del: test_pred\<^sub>r)
proof (simp add: mergei_def)
  fix m' \<Gamma>' m'' \<Gamma>''
  assume a: "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R" "\<forall>v\<in>set locals. m v = m' v \<and> (\<Gamma> v \<longrightarrow> \<Gamma>' v)"
  assume b: "\<forall>m' \<Gamma>'.
          test (m \<Oplus> m') (\<Gamma> \<Oplus> \<Gamma>') (pred\<^sub>r (R \<and>\<^sub>p forVars locals (\<lambda>v. Low v\<^sup>o \<longrightarrow>\<^sub>p Low v`))) \<longrightarrow>
          test (\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else m' (n, x)) (\<Gamma>') Q"
  hence b: "\<And>m' \<Gamma>'. test (m \<Oplus> m') (\<Gamma> \<Oplus> \<Gamma>') (pred\<^sub>r (R \<and>\<^sub>p forVars locals (\<lambda>v. Low v\<^sup>o \<longrightarrow>\<^sub>p Low v`))) \<Longrightarrow>
          test (\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else m' (n, x)) (\<Gamma>') Q"
    by auto

  have "\<forall>x. (\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else (m' \<Oplus> m'') (n, x)) x = (m' \<Oplus> m'') x"
    apply (intro allI)
    using a
    apply (case_tac x)
    by (auto simp: merge_def)
  hence m: "(\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else (m' \<Oplus> m'') (n, x)) = (m' \<Oplus> m'')"
    by blast

  have t: "test (\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else (m' \<Oplus> m'') (n, x)) ( (\<Gamma>' \<Oplus> \<Gamma>'')) Q"
  proof (intro b)
    show "test (m \<Oplus> m' \<Oplus> m'') (\<Gamma> \<Oplus> (\<Gamma>' \<Oplus> \<Gamma>'')) (pred\<^sub>r (R \<and>\<^sub>p forVars locals (\<lambda>v. Low v\<^sup>o \<longrightarrow>\<^sub>p Low v`)))" using a by simp
  qed

  thus "test (m' \<Oplus> m'') (\<Gamma>' \<Oplus> \<Gamma>'') Q" unfolding m .
next
  fix m' \<Gamma>' m'' \<Gamma>''
  let ?m = "(\<lambda>x. if x \<in> set locals then m x else m' x)"
  let ?\<Gamma> = "(\<lambda>x. if x \<in> set locals then \<Gamma> x else \<Gamma>' x)"
  assume a: "\<forall>mh \<Gamma>h. test (m \<Oplus> m' \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h) (pred\<^sub>r R)" 
    "\<forall>m' \<Gamma>'. (\<forall>mh \<Gamma>h. test (m \<Oplus> m' \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h) (pred\<^sub>r R)) \<and> (\<forall>v\<in>set locals. m v = m' v \<and> (\<Gamma> v \<longrightarrow> \<Gamma>' v) ) \<longrightarrow> (\<forall>m'a \<Gamma>''. test (m' \<Oplus> m'a) (\<Gamma>' \<Oplus> \<Gamma>'') Q)"
    "wellformed R G \<L> P" "\<forall>v\<in>set locals. \<Gamma> v \<longrightarrow> \<Gamma>' v"
  have "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') (R) = test (m \<mapsto> ?m) (\<Gamma> \<mapsto> \<Gamma>') (R)"
  proof (rule test_vars_det, goal_cases)
case 1
  then show ?case using a(3) unfolding wellformed_def onlyGlobals_def apply auto apply (case_tac v)
     apply simp
    apply simp
    apply (subgoal_tac "x2 \<notin> set locals")
     apply simp
    by (metis Primed.simps(6) Un_iff)
next
  case 2
  then show ?case using a(3) unfolding wellformed_def onlyGlobals_def by auto 
qed
    
  hence "\<forall>mh \<Gamma>h. test (m \<Oplus> ?m \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h) (pred\<^sub>r R)"
    using a(1) by simp

  hence b: "(\<forall>v\<in>set locals. m v = ?m v ) \<longrightarrow> (\<forall>m'a \<Gamma>''. test (?m \<Oplus> m'a) (\<Gamma>' \<Oplus> \<Gamma>'') Q)"
    using a by blast

  have "\<forall>x. (\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else (m' \<Oplus> m'') (n, x)) x = (?m \<Oplus> m'') x"
    apply (intro allI)
    apply (case_tac x)
    by (auto simp: merge_def split: nat.splits)
  hence m: "(\<lambda>(n, x). if x \<in> set locals \<and> n = 0 then m x else (m' \<Oplus> m'') (n, x)) = (?m \<Oplus> m'')"
    by blast

  have "test (?m \<Oplus> m'') (\<Gamma>' \<Oplus> \<Gamma>'') Q" using b by simp 
  thus "test (mergei m (set locals) (m' \<Oplus> m'')) ( (\<Gamma>' \<Oplus> \<Gamma>'')) Q"
    unfolding mergei_def m .
qed

subsection \<open>Stability Properties\<close>

lemma transitive_local: "transitive localR"
  unfolding localR_def transitive_def
  unfolding test_low test.simps eval.simps
  by fastforce

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G \<L> P"
  shows "stable (state (stabilize R Q)) (step (R \<and>\<^sub>p localR))"
  unfolding stable_def state_def step_def
proof (clarsimp)
  fix m \<Gamma> m' \<Gamma>'
  assume a: "asn m \<Gamma> (stabilize R Q)" "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R" "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') localR"
  have "\<forall>m'' \<Gamma>''. test (m' \<mapsto> m'') (\<Gamma>' \<mapsto> \<Gamma>'') R \<longrightarrow> test (m \<mapsto> m'') (\<Gamma> \<mapsto> \<Gamma>'') R"
    using assms a(2) unfolding  wellformed_def transitive_def by blast
  moreover have "\<forall>m'' \<Gamma>''. test (m' \<mapsto> m'') (\<Gamma>' \<mapsto> \<Gamma>'') localR \<longrightarrow> test (m \<mapsto> m'') (\<Gamma> \<mapsto> \<Gamma>'') localR"
    using transitive_local a(3) unfolding transitive_def by blast
  ultimately show "asn m' \<Gamma>' (stabilize R Q)" using a(1) by (auto simp: stabilize[OF wf])
qed

lemma stabilize_stable_secure [intro]:
  assumes wf: "wellformed R G \<L> Q"
  shows "stable (state (stabilize R P)) (invSec (policy \<L>) \<inter> step (R \<and>\<^sub>p localR))"
proof -
  have "stable (state (stabilize R P)) (step (R \<and>\<^sub>p localR))" using stabilize_stable[OF wf] by blast
  thus ?thesis by (auto simp: stable_def)
qed

text \<open>Show that a stabilized predicate is wellformed\<close>
lemma stabilize_str [intro]:
  assumes wf: "wellformed R G \<L> P"
  shows "str (state (stabilize R Q))"
proof (clarsimp simp add: )
  fix m \<Gamma> \<Gamma>' assume a: "asn m \<Gamma> (stabilize R Q)" "\<Gamma> \<ge>\<^sub>\<Gamma> \<Gamma>'"
  hence c: "\<forall>m' \<Gamma>'. test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') (R \<and>\<^sub>p localR) \<longrightarrow> asn m' \<Gamma>' Q" using stabilize[OF wf] by auto

  have b: "\<forall>m' \<Gamma>''. test (m \<mapsto> m') (\<Gamma>' \<mapsto> \<Gamma>'') (R \<and>\<^sub>p localR) \<longrightarrow> (test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>'') (R \<and>\<^sub>p localR))"
    using wf a(2) unfolding localR_def apply (simp add: type_ord_def wellformed_def)
    apply auto 
    by blast

  thus "asn m \<Gamma>' (stabilize R Q)" unfolding stabilize[OF wf] using c by blast
qed

lemma stabilize_wellformed [intro]:
  assumes "wellformed R G \<L> P"
  shows "wellformed R G \<L> (stabilize R Q)" (is "wellformed R G \<L> ?P")
proof -
  have "stable (state ?P) (invSec (policy \<L>) \<inter> step (R \<and>\<^sub>p localR))" 
    using stabilize_stable_secure assms by blast
  moreover have "str (state ?P)" 
    using stabilize_str assms unfolding wellformed_def wp.simps by blast
  ultimately show ?thesis using assms unfolding wellformed_def by blast
qed

text \<open>Show preservation of entail and equivalence across stabilization\<close>
lemma stabilize_entail [intro]:
  assumes "P \<turnstile>\<^sub>p Q"
  shows "stabilize R P \<turnstile>\<^sub>p stabilize R Q"
  using assms by (clarsimp simp add: entail_def stabilize_def)

lemma stabilize_equiv [intro]:
  assumes "P =\<^sub>p Q"
  shows "stabilize R P =\<^sub>p stabilize R Q"
  using assms stabilize_entail unfolding entail_def equiv_def by blast

lemma [intro]:
  "test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) localR"
  by (simp add: localR_def)

text \<open>Rephrase the above for easier use in proof\<close>
lemma stabilize_asnE:
  assumes "wellformed R G \<L> Q"
  assumes "asn m \<Gamma> (stabilize R P)"
  obtains "asn m \<Gamma> P"
  using assms 
  apply (auto simp: entail_def wellformed_def reflexive_def stabilize)
  apply (rule that)
  apply (subgoal_tac "test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) R \<and> test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) localR")
  by blast+

subsection \<open>Action Rules\<close>

text \<open>Rules to allow rewriting of \<Gamma>\<close>
lemma \<Gamma>_order:
  assumes "wellformed R G \<L> Q"
  assumes "asn m' (\<Gamma>(x := b\<^sub>1)) Q"
  assumes "b\<^sub>1 \<longrightarrow> b\<^sub>2"
  shows "asn m' (\<Gamma>(x := b\<^sub>2)) Q"
proof -
  have wf: "\<And>m \<Gamma> \<Gamma>'. asn m \<Gamma> Q \<Longrightarrow> \<Gamma> \<ge>\<^sub>\<Gamma> \<Gamma>' \<Longrightarrow> asn m \<Gamma>' Q" 
    using assms by (auto simp: wellformed_def)
  moreover have "\<Gamma>(x := b\<^sub>1) \<ge>\<^sub>\<Gamma> \<Gamma>(x := b\<^sub>2)"
    using assms by (simp add: type_ord_def)
  ultimately show ?thesis using assms by blast
qed

lemma \<Gamma>_flow:
  assumes "wellformed R G \<L> Q"
  assumes "asn m (\<Gamma>(x := b)) Q"
  assumes "b \<longrightarrow> (\<forall>x\<in>vars\<^sub>e (lift\<^sub>A e). \<Gamma> x)"
  shows "asn m (\<Gamma>(x := \<forall>x\<in>vars\<^sub>e (lift\<^sub>A e). \<Gamma> x)) Q"
  using assms \<Gamma>_order by simp

lemma \<Gamma>_order_env:
  assumes "wellformed R G \<L> Q"
  assumes "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>(x := b\<^sub>1)) G"
  assumes "b\<^sub>1 \<longrightarrow> b\<^sub>2"
  shows "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>(x := b\<^sub>2)) G"
proof -
  have wf: "\<And>m m' \<Gamma> \<Gamma>' \<Gamma>n \<Gamma>n'. test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') G \<Longrightarrow> \<Gamma>n \<ge>\<^sub>\<Gamma> \<Gamma> \<and> \<Gamma>' \<ge>\<^sub>\<Gamma> \<Gamma>n' \<Longrightarrow> 
                                test (m \<mapsto> m') (\<Gamma>n \<mapsto> \<Gamma>n') G" 
    using assms(1) by (auto simp: wellformed_def str_env_def step_def) 
  moreover have "\<Gamma>(x := b\<^sub>1) \<ge>\<^sub>\<Gamma> \<Gamma>(x := b\<^sub>2)"
    using assms by (auto simp add: type_ord_def)
  ultimately show ?thesis using assms
    unfolding type_ord_def type_ord_env_def
    by blast
qed

lemma \<Gamma>_flow_env:
  assumes "wellformed R G \<L> Q"
  assumes "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>(x := b)) G"
  assumes "b \<longrightarrow> (\<forall>x\<in>vars\<^sub>e (lift\<^sub>A e). \<Gamma> x)"
  shows "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>(x := (\<forall>x\<in>vars\<^sub>e (lift\<^sub>A e). \<Gamma> x))) G"
  using assms \<Gamma>_order_env by simp

text \<open>Show that weakestpre is enforced by wp\<close>
lemma weakestpreI [intro]:
  assumes wf: "wellformed R G \<L> Q"
  shows "weakestpre (secure (policy \<L>) \<inter> state (wp R G \<L> (WPLang.Act \<alpha>) Q)) (state Q) \<alpha>"
proof (cases \<alpha>)
  case (Load r x i)
  then show ?thesis
    unfolding weakestpre_def state_def
    apply (auto elim!: stabilize_asnE[OF wf] simp: \<Gamma>\<^sub>e_def intro!: \<Gamma>_flow[OF wf])
    apply (auto elim!: stabilize_asnE[OF wf] simp: \<Gamma>\<^sub>e_def intro!: \<Gamma>_flow[OF wf])
    by (rule \<Gamma>_order[OF wf]) blast+
qed (auto simp: weakestpre_def state_def \<Gamma>\<^sub>e_def elim!: stabilize_asnE[OF wf] intro!: \<Gamma>_flow[OF wf])+ 

text \<open>Show that executable is enforced by wp\<close>
lemma executableI [intro]:
  assumes "wellformed R G \<L> Q"
  shows "executable (secure (policy \<L>) \<inter> state (wp R G \<L> (WPLang.Act \<alpha>) Q)) \<alpha>"
proof (cases \<alpha>) (* The CAS case introduces a loop that confused auto, need special handling *)
  case (NCAS x e\<^sub>1 e\<^sub>2)
  then show ?thesis using low_exp[of _ _ e\<^sub>1 \<L>] 
    unfolding executable_def state_def mem_delta_def 
    by (clarsimp elim!: stabilize_asnE[OF assms])
next
  case (CAS x e\<^sub>1 e\<^sub>2)
  then show ?thesis using low_exp[of _ _ e\<^sub>1 \<L>]
    unfolding executable_def state_def mem_delta_def 
    by (clarsimp elim!: stabilize_asnE[OF assms]) metis
qed (auto simp: executable_def state_def elim!: low_expE low_guardE stabilize_asnE[OF assms])

text \<open>Show that actions conform to their security properties\<close>
lemma PO_secure:
  assumes wf: "wellformed R G \<L> Q"
  assumes "test m \<Gamma> (PO \<alpha> \<L>)"
  assumes "(m,m') \<in> update \<alpha>"
  shows "((m, \<Gamma>), (m', flow \<alpha> m \<Gamma>)) \<in> invSec (policy \<L>)"
  using assms 
  by (cases \<alpha>) (auto simp: wf\<^sub>\<L>_self[OF wf] preserve_def \<Gamma>\<^sub>e_def)

text \<open>Show that actions conform to their functional properties\<close>
lemma PO_functional:
  assumes wf: "wellformed R G \<L> Q"
  assumes "(m, \<Gamma>) \<in> secure (policy \<L>)"
  assumes "test m \<Gamma> (PO \<alpha> \<L>)"
  assumes "test m \<Gamma> (guar \<alpha> G \<L>)"
  assumes "(m,m') \<in> update \<alpha>"
  shows "test (m \<mapsto> m') (\<Gamma> \<mapsto> flow \<alpha> m \<Gamma>) G"
  using assms 
proof (cases \<alpha>)
  case (Load r x i) (* The Load has a strange \<Gamma> update, needs special handling *)
  then show ?thesis using assms 
    apply (auto simp: \<Gamma>\<^sub>e_def)
    by (rule \<Gamma>_order_env[OF wf]) auto
qed (auto intro!: \<Gamma>_flow_env[OF wf] simp: \<Gamma>\<^sub>e_def)

text \<open>Show that guarantee is enforced by wp\<close>
lemma guaranteeI [intro]:
  assumes wf: "wellformed R G \<L> Q"
  shows "guarantee (secure (policy \<L>) \<inter> state (wp R G \<L> (WPLang.Act \<alpha>) Q)) (invSec (policy \<L>) \<inter> step G) \<alpha>"
  unfolding guarantee_def state_def step_def
  by (auto elim!: stabilize_asnE[OF wf] intro!: PO_secure[OF wf] PO_functional[OF wf])

text \<open>Introduction rule for actions\<close>
lemma actI [intro]:
  assumes "wellformed R G \<L> Q"
  shows "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state (wp R G \<L> (Act \<alpha>) Q)) (Basic \<alpha>) (state Q)"
    (is "Valid ?R ?G ?\<L> ?P (Basic \<alpha>) ?Q")
proof (rule actRule)
  show "guarantee (secure (policy \<L>) \<inter> ?P) (invSec (policy \<L>) \<inter> step G) \<alpha>" using assms by blast
next
  show "weakestpre (secure (policy \<L>) \<inter> ?P) (state Q) \<alpha>" using assms by blast
next
  show "executable (secure (policy \<L>) \<inter> ?P) \<alpha>" using assms by blast
qed (insert assms, auto simp: wellformed_def)

text \<open>Preservation of wellformedness\<close>

lemma wellformed_actI [intro]:
  assumes "wellformed R G \<L> Q"
  shows "wellformed R G \<L> (wp R G \<L> (WPLang.Act \<alpha>) Q)" (is "wellformed R G \<L> ?P")
  apply simp using assms 
  by (meson stabilize_wellformed ) 

text \<open>Introduction rule for actions with precontext rewrite\<close>
lemma actI_rw [intro]:
  assumes "wellformed R G \<L> Q"
  assumes "P \<turnstile>\<^sub>p wp R G \<L> (WPLang.Act \<alpha>) Q"
  shows "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state P) (Basic \<alpha>) (state Q)"
  using actI[OF assms(1)]
proof (rule rewriteRule)
  show "state P \<subseteq> state (wp R G \<L> (WPLang.Act \<alpha>) Q)"
    using assms(2) by (auto simp: asn_def entail_def state_def)
qed auto

subsection \<open>Abstract Definitions\<close>

text \<open>Convert the While language into the general version\<close>
fun lift\<^sub>c :: "('Var, nat, 'Aexp, 'Bexp) WPLang \<Rightarrow> ('Var, 'Aexp, 'Bexp) Action Stmt"
  where
    "lift\<^sub>c Skip = Stmt.Skip" |
    "lift\<^sub>c (Act \<alpha>) = (Basic \<alpha>)"|
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = (Stmt.Seq (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2))" |
    "lift\<^sub>c (If \<alpha> c\<^sub>1 c\<^sub>2) = (Choice (Stmt.Seq (Basic \<alpha>) (lift\<^sub>c c\<^sub>1)) (Stmt.Seq (Basic (negate \<alpha>)) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While \<alpha> I c) = (Stmt.Seq ((Stmt.Seq (Basic \<alpha>) (lift\<^sub>c c))*) (Basic (negate \<alpha>)))" |
    "lift\<^sub>c (DoWhile c I \<alpha>) = (Stmt.Seq (lift\<^sub>c c) (Stmt.Seq ((Stmt.Seq (Basic \<alpha>) (lift\<^sub>c c))*) (Basic (negate \<alpha>))))"

text \<open>An ordering property on contexts\<close>
definition context_order :: "('Var,nat) rpred \<Rightarrow> ('Var,nat) rpred \<Rightarrow> ('Var,'Bexp) policy \<Rightarrow> ('Var,nat) ipred \<Rightarrow> ('Var, nat) ipred \<Rightarrow> bool" 
  ("_,_,_ \<turnstile> _ \<ge> _")
  where "context_order R G \<L> P Q \<equiv> (P \<turnstile>\<^sub>p Q) \<and> (wellformed R G \<L> Q \<longrightarrow> wellformed R G \<L> P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid :: "('Var,nat) rpred \<Rightarrow> (_,_) rpred \<Rightarrow> (_,_) policy \<Rightarrow> (_,_) ipred \<Rightarrow> (_,_,'Aexp,'Bexp) WPLang \<Rightarrow> (_,_) ipred \<Rightarrow> bool" 
  ("_,_,_ \<turnstile> _ {_} _")
  where "valid R G \<L> P c Q \<equiv> wellformed R G \<L> Q \<longrightarrow> 
    (Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state P) (lift\<^sub>c c) (state Q) \<and> wellformed R G \<L> P)"

text \<open>Show the ordering property is reflexive\<close>
lemma context_order_refl [intro]:
  "R,G,\<L> \<turnstile> P \<ge> P"
  unfolding context_order_def by auto

subsection \<open>Introduction Rules\<close>

text \<open>Sequential Composition Rule\<close>
lemma seqWP:
  "R,G,\<L> \<turnstile> P {c\<^sub>1} Q \<Longrightarrow> R,G,\<L> \<turnstile> M {c\<^sub>2} P \<Longrightarrow> R,G,\<L> \<turnstile> M {c\<^sub>2 ; c\<^sub>1} Q"
  unfolding valid_def by auto

text \<open>Simplified Rewrite Rule, intended to rewrite the precontext\<close>
lemma rewriteWP:
  "R,G,\<L> \<turnstile> P {c} Q \<Longrightarrow> R,G,\<L> \<turnstile> M \<ge> P \<Longrightarrow> R,G,\<L> \<turnstile> M {c} Q"
proof (clarsimp simp add: valid_def context_order_def)
  assume a: "M \<turnstile>\<^sub>p P"
  assume "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state P) (lift\<^sub>c c) (state Q)"
  thus "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state M) (lift\<^sub>c c) (state Q)"
    by (rule rewriteRule) (insert a, auto simp: state_def entail_def asn_def)
qed

text \<open>Skip Rule\<close>
lemma skipWP:
  "R,G,\<L> \<turnstile> Q {Skip} Q"
  by (auto simp: context_order_def valid_def wellformed_def)

text \<open>General Skip Rule, achieved with combination with rewrite\<close>
lemma skipWP_rewrite:
  assumes "R,G,\<L> \<turnstile> P \<ge> Q" 
  shows "R,G,\<L> \<turnstile> P {Skip} Q"
  using rewriteWP[OF skipWP assms] .

text \<open>Act Rule\<close>
lemma actWP:
  "R,G,\<L> \<turnstile> wp R G \<L> (WPLang.Act \<alpha>) Q {Act \<alpha>} Q"
  unfolding valid_def lift\<^sub>c.simps by blast

text \<open>General Act Rule, achieved with combination with rewrite\<close>
lemma actWP_rewrite:
  assumes "R,G,\<L> \<turnstile> P \<ge> (wp R G \<L> (WPLang.Act \<alpha>) Q)"
  shows "R,G,\<L> \<turnstile> P {Act \<alpha>} Q"
  using rewriteWP[OF actWP assms] .

method act_tac = intro actI_rw; simp; intro stabilize_entail

lemma negate_guar:
  "pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>) \<turnstile>\<^sub>p pred\<^sub>0 (guar (negate \<alpha>) G \<L> \<and>\<^sub>p PO (negate \<alpha>) \<L>)"
  by (cases \<alpha>) auto

text \<open>If Rule\<close>
lemma ifWP:
  assumes "R,G,\<L> \<turnstile> P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G,\<L> \<turnstile> P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G,\<L> \<turnstile> stabilize R (pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>) \<and>\<^sub>p (wp\<^sub>Q \<alpha> P\<^sub>1 \<L>) \<and>\<^sub>p (wp\<^sub>Q (negate \<alpha>) P\<^sub>2 \<L>)) {If \<alpha> c\<^sub>1 c\<^sub>2} Q"
  using assms
  apply (clarsimp simp add: valid_def)
  apply (intro impI conjI choiceRule seqRule stabilize_wellformed; assumption?)
  by (act_tac; insert negate_guar; auto simp: entail_def)+

text \<open>General If Rule, achieved with combination with rewrite\<close>
lemma ifWP_rewrite:
  assumes "R,G,\<L> \<turnstile> P \<ge> (stabilize R (pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>) \<and>\<^sub>p (wp\<^sub>Q \<alpha> P\<^sub>1 \<L>) \<and>\<^sub>p (wp\<^sub>Q (negate \<alpha>) P\<^sub>2 \<L>)))"
  assumes "R,G,\<L> \<turnstile> P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G,\<L> \<turnstile> P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G,\<L> \<turnstile> P {If \<alpha> c\<^sub>1 c\<^sub>2} Q"
  using rewriteWP[OF ifWP[OF assms(2,3)] assms(1)] . 

lemma whileWP:
  assumes "pred\<^sub>0 I \<turnstile>\<^sub>p pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>)"
  assumes "pred\<^sub>0 I \<turnstile>\<^sub>p wp\<^sub>Q \<alpha> P \<L>"
  assumes "pred\<^sub>0 I \<turnstile>\<^sub>p wp\<^sub>Q (negate \<alpha>) Q \<L>"
  assumes "R,G,\<L> \<turnstile> P {c} (stabilize R (pred\<^sub>0 I))"
  shows "R,G,\<L> \<turnstile> stabilize R (pred\<^sub>0 I) {While \<alpha> I c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI choiceRule seqRule stabilize_wellformed; assumption?)
  assume "wellformed R G \<L> Q"
  thus "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state (stabilize R (pred\<^sub>0 I))) (Basic (negate \<alpha>)) (state Q)"
    using assms(1,2,3) negate_guar by act_tac (auto simp: entail_def) 
next
  assume wf: "wellformed R G \<L> Q"
  hence "wellformed R G \<L> (stabilize R (pred\<^sub>0 I))"  by auto
  thus "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state (stabilize R (pred\<^sub>0 I))) ((Basic \<alpha> ;; lift\<^sub>c c)*)
     (state (stabilize R (pred\<^sub>0 I)))"
    using wf assms(4) unfolding valid_def
    apply (intro loopRule seqRule stabilize_stable_secure; simp)
    apply blast
    using assms(1,2,3) by act_tac auto
qed

lemma whileWP_rewrite:
  assumes order: "R,G,\<L> \<turnstile> N \<ge> (stabilize R (pred\<^sub>0 I))"
  assumes recur: "R,G,\<L> \<turnstile> P {c} (stabilize R (pred\<^sub>0 I))"
  assumes side: "pred\<^sub>0 I \<turnstile>\<^sub>p pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>)" "pred\<^sub>0 I \<turnstile>\<^sub>p wp\<^sub>Q \<alpha> P \<L>" "pred\<^sub>0 I \<turnstile>\<^sub>p wp\<^sub>Q (negate \<alpha>) Q \<L>" 
  shows "R,G,\<L> \<turnstile> N {While \<alpha> I c} Q"
  using rewriteWP[OF whileWP[OF side recur] order] .

lemma doWhileWP:
  assumes "pred\<^sub>0 I \<turnstile>\<^sub>p pred\<^sub>0 (guar \<alpha> G \<L> \<and>\<^sub>p PO \<alpha> \<L>)"
  assumes "pred\<^sub>0 I \<turnstile>\<^sub>p wp\<^sub>Q \<alpha> P \<L>"
  assumes "pred\<^sub>0 I \<turnstile>\<^sub>p wp\<^sub>Q (negate \<alpha>) Q \<L>"
  assumes "R,G,\<L> \<turnstile> P {c} (stabilize R (pred\<^sub>0 I))"
  shows "R,G,\<L> \<turnstile> P {DoWhile c I \<alpha>} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI choiceRule seqRule stabilize_wellformed; assumption?)
  assume "wellformed R G \<L> Q"
  thus "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state (stabilize R (pred\<^sub>0 I))) (Basic (negate \<alpha>)) (state Q)"
    using assms(1,2,3) negate_guar by act_tac (auto simp: entail_def) 
next
  assume wf: "wellformed R G \<L> Q"
  hence "wellformed R G \<L> (stabilize R (pred\<^sub>0 I))" by auto
  thus "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state (stabilize R (pred\<^sub>0 I))) ((Basic \<alpha> ;; lift\<^sub>c c)*)
     (state (stabilize R (pred\<^sub>0 I)))"
    using wf assms(4) unfolding valid_def
    apply (intro loopRule seqRule stabilize_stable_secure; simp)
    apply blast
    using assms(1,2,3) by act_tac auto
qed (insert assms(4), auto simp: valid_def)

definition if_secure ("0_,_ \<turnstile> R: _ /G: _ /{_}" [0, 0, 0, 0, 0] 61)
  where "if_secure R G \<L> P c \<equiv> Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state (pred\<^sub>0 P)) (lift\<^sub>c c) (state (Pb True))"

lemma if_secureI:
  assumes wf: "transitive R" "reflexive R" "reflexive G" "wf\<^sub>\<L> \<L>" "str_env (step G)" "str_env (step R)" "onlyGlobals R"
  assumes v: "R,G,\<L> \<turnstile> P {c} (Pb True)"
  assumes e: "pred\<^sub>0 P\<^sub>0 \<turnstile>\<^sub>p P"
  shows "if_secure R G \<L> P\<^sub>0 c"
  unfolding if_secure_def
proof (rule rewriteRule)
  have "stable (state (Pb True)) (invSec (policy \<L>) \<inter> step (R \<and>\<^sub>p localR))" 
    unfolding stable_def state_def asn_def by auto
  moreover have "str (state (Pb True))" unfolding str_def state_def asn_def by auto
  ultimately have "wellformed R G \<L> (Pb True)"
    using wf unfolding wellformed_def by simp
  thus "Valid (step (R \<and>\<^sub>p localR)) (step G) (policy \<L>) (state P) (lift\<^sub>c c) (state (Pb True))"
    using v e unfolding valid_def by auto
next
  show "state (pred\<^sub>0 P\<^sub>0) \<subseteq> state P" using e by (auto simp: state_def entail_def asn_def)
qed auto

definition invar :: "('Var,nat) pred \<Rightarrow> ('Var,nat) rpred" where
  "invar P \<equiv> orig P \<longrightarrow>\<^sub>p Primed_Typed_Predicate_Language.prime P"

end

end