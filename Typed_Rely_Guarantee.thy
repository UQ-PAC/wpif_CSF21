theory Typed_Rely_Guarantee
  imports Typed_Memory Bisimulation
begin

section \<open>Locale\<close>

definition secure :: "('Var, 'Val) Sec \<Rightarrow> ('Var, 'Val) TState"
  where "secure \<L> \<equiv> {(m,\<Gamma>). \<forall>x. m \<in> \<L> x \<longrightarrow> \<Gamma> x}"

locale typed_rely_guarantee = typed_memory + rg: bisimulation eval
  for eval :: "'Act \<Rightarrow> (('Var,'Val) Mem \<times> ('Var,'Val) Mem) set" +
  fixes flow :: "'Act \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> ('Var) Type \<Rightarrow> ('Var) Type"
  assumes flow_sound: "(m\<^sub>1,m\<^sub>1') \<in> eval \<alpha> \<Longrightarrow> (m\<^sub>2,m\<^sub>2') \<in> eval \<alpha> \<Longrightarrow> flow \<alpha> m\<^sub>1 (m\<^sub>1 \<triangle> m\<^sub>2) \<ge>\<^sub>\<Gamma> m\<^sub>1' \<triangle> m\<^sub>2'"

context typed_rely_guarantee
begin

subsection \<open>Lifting Properties\<close>
text \<open>
This theory file maps the predicate language concepts to the complete theory found in BisimRG.
As a result, it must lift predicate language definitions into the memory set encoding found in
the complete theory.
\<close>
definition liftState :: "('Var, 'Val) TState \<Rightarrow> ('Var, 'Val) Mem rg.state"
  where "liftState P \<equiv> {(m\<^sub>1,m\<^sub>2). (m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2) \<in> P \<and> (m\<^sub>2,m\<^sub>1 \<triangle> m\<^sub>2) \<in> P}"

definition liftStep :: "('Var, 'Val) TStep \<Rightarrow> ('Var, 'Val) Mem rg.step"
  where "liftStep R \<equiv> {((m\<^sub>1,m\<^sub>2),(m\<^sub>1',m\<^sub>2')). 
                ((m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2),(m\<^sub>1',m\<^sub>1' \<triangle> m\<^sub>2')) \<in> R \<and>
                ((m\<^sub>2,m\<^sub>1 \<triangle> m\<^sub>2),(m\<^sub>2',m\<^sub>1' \<triangle> m\<^sub>2')) \<in> R}"

definition stable :: "('Var, 'Val) TState \<Rightarrow> ('Var, 'Val) TStep \<Rightarrow> bool" where
  "stable \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f \<longrightarrow> (x, y) \<in> g \<longrightarrow> y \<in> f)"

abbreviation invSec :: "('Var, 'Val) Sec \<Rightarrow> ('Var, 'Val) TStep"
  where "invSec \<L> \<equiv> preserve (secure \<L>)"

abbreviation lift\<^sub>R :: "('Var, 'Val) TStep \<Rightarrow> ('Var, 'Val) Sec \<Rightarrow> ('Var, 'Val) Mem rg.step"
  where "lift\<^sub>R R \<L> \<equiv> liftStep (invSec \<L> \<inter> R)"

abbreviation lift\<^sub>G :: "('Var, 'Val) TStep \<Rightarrow> ('Var, 'Val) Sec \<Rightarrow> ('Var, 'Val) Mem rg.step"
  where "lift\<^sub>G G \<L> \<equiv> liftStep (invSec \<L> \<inter> G)"

abbreviation lift\<^sub>Q :: "('Var, 'Val) TState \<Rightarrow> ('Var, 'Val) Sec \<Rightarrow> ('Var, 'Val) Mem rg.state"
  where "lift\<^sub>Q Q \<L> \<equiv> liftState (secure \<L> \<inter> Q)"

text \<open>Lift the meaning of entailment from the predicate language to sets of memory states\<close>
lemma lift_entail [intro]:
  shows "P \<subseteq> Q \<Longrightarrow> (liftState P \<subseteq> liftState Q)"
  by (auto simp: liftState_def)

lemma lift_step_entail [intro]:
  shows "P \<subseteq> Q \<Longrightarrow> (liftStep P \<subseteq> liftStep Q)"
  by (auto simp: liftStep_def)

lemma lift\<^sub>Q_entail:
  shows "P \<subseteq> Q \<Longrightarrow> (lift\<^sub>Q P \<L> \<subseteq> lift\<^sub>Q Q \<L>)"
  by (auto simp: liftState_def)

lemma lift\<^sub>G_entail:
  shows "P \<subseteq> Q \<Longrightarrow> (lift\<^sub>G P \<L> \<subseteq> lift\<^sub>G Q \<L>)"
  by (auto simp: liftStep_def)

text \<open>Lift the predicate language based definition of stability\<close>
lemma lift_stable [intro]:
  "stable P R \<Longrightarrow> rg.stable (liftState P) (liftStep R)"
  by (clarsimp simp add: stable_def rg.stable_def liftState_def liftStep_def)

text \<open>Support conjunction over stable predicates\<close>
lemma stable_conjI [intro]:
  assumes "stable P R" "stable Q R"
  shows "stable (P \<inter> Q) R"
  using assms by (auto simp: stable_def)

text \<open>Support preservation of an invariant over a stable predicate\<close>
lemma stable_invarI [intro]:
  assumes "stable Q R"
  shows "stable (P \<inter> Q) (preserve P \<inter> R)"
  using assms unfolding stable_def preserve_def by auto

lemma stable_invarI' [intro]:
  assumes "stable Q (invSec \<L> \<inter> R)"
  shows "stable (secure \<L> \<inter> Q) (invSec \<L> \<inter> R)"
  using assms unfolding stable_def preserve_def by auto

text \<open>Support simplification of conjunction in lifted predicates\<close>
lemma [simp]:
  "lift\<^sub>Q (P\<^sub>1 \<inter> P\<^sub>2) \<L> = lift\<^sub>Q P\<^sub>1 \<L> \<inter> lift\<^sub>Q P\<^sub>2 \<L>" 
  by (auto simp: liftState_def)

lemma [simp]:
  "lift\<^sub>G (R\<^sub>1 \<inter> R\<^sub>2) \<L> = lift\<^sub>G R\<^sub>1 \<L> \<inter> lift\<^sub>G R\<^sub>2 \<L>"
  by (auto simp: liftStep_def)

text \<open>A wellformed security policy results in a wellformed environment predicate\<close>
lemma str_env_\<L> [intro]:
  shows "str_env (invSec \<L>)"
  by (auto simp: str_env_def preserve_def secure_def type_ord_def)

subsection \<open>Executable\<close>
text \<open>
The executable property captures the idea of incomplete actions, 
such as expressions that may not be defined and guards that cannot resolve to be true.
This property can be resolved in a few different ways:
  - If the expression is only influenced by low variables, then it does not have to be executable 
    under all conditions. This is the approach used for guards.
  - If the expression is influenced by high variables, then it must be consistently executable or 
    not under the current context. This is used for some partial expression evaluations.
\<close>
definition executable :: "('Var, 'Val) TState \<Rightarrow> 'Act \<Rightarrow> bool"
  where "executable P \<alpha> \<equiv> 
    \<forall>m\<^sub>1 m\<^sub>2. (m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2) \<in> P \<and> (m\<^sub>2,m\<^sub>1 \<triangle> m\<^sub>2) \<in>  P \<longrightarrow> (\<exists>m. (m\<^sub>1,m) \<in> eval \<alpha>) \<longrightarrow>  (\<exists>m. (m\<^sub>2,m) \<in> eval \<alpha>)"

lemma executable1:
  assumes "executable P \<alpha>"
  shows "\<forall>m\<^sub>1 m\<^sub>2. (m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2) \<in> P \<and> (m\<^sub>2,m\<^sub>1 \<triangle> m\<^sub>2) \<in>  P \<longrightarrow> (\<exists>m. (m\<^sub>1,m) \<in> eval \<alpha>) \<longrightarrow>  (\<exists>m. (m\<^sub>2,m) \<in> eval \<alpha>)"
  using assms by (simp add: executable_def)

lemma executable2:
  assumes "executable P \<alpha>"
  shows "\<forall>m\<^sub>1 m\<^sub>2. (m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2) \<in> P \<and> (m\<^sub>2,m\<^sub>1 \<triangle> m\<^sub>2) \<in>  P \<longrightarrow> (\<exists>m. (m\<^sub>2,m) \<in> eval \<alpha>) \<longrightarrow>  (\<exists>m. (m\<^sub>1,m) \<in> eval \<alpha>)"
  using assms by (metis executable_def mem_delta_flip)

lemma executable [intro]:
  assumes "executable (secure \<L> \<inter> P) \<alpha>"
  shows "rg.bisim_act (lift\<^sub>Q P \<L>) \<alpha>"
  using executable1 executable2 assms
  by (simp add: rg.bisim_act_def rg.progress_def liftState_def)

subsection \<open>Guarantee\<close>
text \<open>
The guarantee property ensures the action conforms to the thread's guarantee and security policy.
As the logic is incomplete, it requires a wellformed guarantee, 
such that inaccuracies due to over-approximating type flow cannot invalidate the state.
\<close>

definition guarantee
  where "guarantee P G \<alpha> \<equiv> \<forall>m m' \<Gamma>. (m,\<Gamma>) \<in> P \<longrightarrow> (m,m') \<in> eval \<alpha> \<longrightarrow> ((m,\<Gamma>),(m',(flow \<alpha> m \<Gamma>))) \<in> G"

lemma guarantee_step:
  assumes "str_env G"
  assumes "guarantee (secure \<L> \<inter> P) G \<alpha>"
  assumes "(m\<^sub>1,m\<^sub>1') \<in> eval \<alpha>" "(m\<^sub>2,m\<^sub>2') \<in> eval \<alpha>"
  assumes "(m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2) \<in> secure \<L> \<inter> P"
  shows "((m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2),(m\<^sub>1',m\<^sub>1' \<triangle> m\<^sub>2')) \<in> G"
  using assms flow_sound unfolding str_env_def guarantee_def type_ord_def
  by metis

lemma guarantee [intro]:
  assumes "str_env G"
  assumes "guarantee (secure \<L> \<inter> P) G \<alpha>"
  shows "rg.lift\<^sub>P (lift\<^sub>Q P \<L>) \<inter> rg.lift\<^sub>a \<alpha> \<subseteq> liftStep G"
  using guarantee_step[OF assms] 
  by (clarsimp simp add: rg.lift\<^sub>a_def liftState_def liftStep_def rg.lift\<^sub>P_def, metis mem_delta_flip)

lemma guarantee_conjE[elim]:
  assumes "guarantee P (A \<inter> B) \<alpha>" 
  obtains "guarantee P A \<alpha>" "guarantee P B \<alpha>"
  using assms by (auto simp: guarantee_def)

subsection \<open>Weakest Precondition\<close>
text \<open>
The weakest precondition property ensures proof obligations are preserved across actions.
As the logic is incomplete, it requires a wellformed postcondition, 
such that inaccuracies due to over-approximating type flow cannot invalidate the state.
\<close>
definition weakestpre
  where "weakestpre P Q \<alpha> \<equiv> \<forall>m m' \<Gamma>. (m,\<Gamma>) \<in> P \<longrightarrow> (m,m') \<in> eval \<alpha> \<longrightarrow> (m',flow \<alpha> m \<Gamma>) \<in> Q"

lemma weakestpre_step:
  assumes "str Q"
  assumes "weakestpre P Q \<alpha>"
  assumes "(m\<^sub>1,m\<^sub>1') \<in> eval \<alpha>" "(m\<^sub>2,m\<^sub>2') \<in> eval \<alpha>"
  assumes "(m\<^sub>1,m\<^sub>1 \<triangle> m\<^sub>2) \<in> P"
  shows "(m\<^sub>1',m\<^sub>1' \<triangle> m\<^sub>2') \<in> Q"
  using assms flow_sound unfolding weakestpre_def str_def by blast

lemma weakestpreQ [intro]:
  assumes "str Q"
  assumes "weakestpre (secure \<L> \<inter> P) Q \<alpha>"
  shows "(lift\<^sub>Q P \<L>)+[rg.lift\<^sub>a \<alpha>] \<subseteq> liftState Q"
  using weakestpre_step[OF assms]
  by (clarsimp simp add: rg.lift\<^sub>a_def rg.trans_def liftState_def; metis mem_delta_flip)

lemma weakestpre\<L> [intro]:
  assumes "guarantee (secure \<L> \<inter> P) (invSec \<L>) \<alpha>"
  shows "(lift\<^sub>Q P \<L>)+[rg.lift\<^sub>a \<alpha>] \<subseteq> liftState (secure \<L>)"
  using guarantee_step[OF str_env_\<L>[of \<L>] assms(1)]
  apply (clarsimp simp add: rg.lift\<^sub>a_def rg.trans_def liftState_def preserve_def)
  by (metis mem_delta_flip)

lemma weakestpre_conj [intro]:
  assumes "(lift\<^sub>Q P \<L>)+[rg.lift\<^sub>a \<alpha>] \<subseteq> liftState A"
  assumes "(lift\<^sub>Q P \<L>)+[rg.lift\<^sub>a \<alpha>] \<subseteq> liftState B"
  shows "(lift\<^sub>Q P \<L>)+[rg.lift\<^sub>a \<alpha>] \<subseteq> liftState (A \<inter> B)"
  using assms by (auto simp: liftState_def)

subsection \<open>Rules\<close>
text \<open>
A set of rules that specialise the general set seen in Rely_Guarantee for:
  - Consideration of a single memory and a type context
  - An invariant security policy \<L>
\<close>

definition Valid :: "('Var,'Val) TStep \<Rightarrow> ('Var,'Val) TStep \<Rightarrow> ('Var,'Val) Sec \<Rightarrow> ('Var,'Val) TState \<Rightarrow> 'Act Stmt \<Rightarrow> ('Var,'Val) TState \<Rightarrow> bool"
  ("_,_ \<turnstile>\<^sub>_ _ {_} _" [20, 20, 20, 20] 20)
  where "Valid R G \<L> P c Q \<equiv> rg.rules (lift\<^sub>R R \<L>) (lift\<^sub>G G \<L>) (lift\<^sub>Q P \<L>) (c) (lift\<^sub>Q Q \<L>)"

lemma skipRule [intro]:
  "stable P (invSec \<L> \<inter> R) \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { Skip } P"
  unfolding Valid_def by blast

lemma seqRule [intro]:
  "R,G \<turnstile>\<^sub>\<L> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { c\<^sub>1 ;; c\<^sub>2 } M"
  unfolding Valid_def by blast

lemma choiceRule [intro]:
  "R,G \<turnstile>\<^sub>\<L> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" 
  unfolding Valid_def by blast

lemma loopRule [intro]:
  "stable P (invSec \<L> \<inter> R) \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { c } P \<Longrightarrow> R,G \<turnstile>\<^sub>\<L> P { c* } P"
  unfolding Valid_def by blast

lemma parallelRule [intro]:
  "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>\<L> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>\<L> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>\<L> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } Q\<^sub>1 \<inter> Q\<^sub>2"
  unfolding Valid_def by (intro rg.parallelI, auto simp: liftStep_def)

lemma rewriteRule [intro]:
  "R,G \<turnstile>\<^sub>\<L> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                      R',G' \<turnstile>\<^sub>\<L> P' { c } Q'"
  unfolding Valid_def by (rule rg.rewrite, auto intro!: lift\<^sub>Q_entail lift\<^sub>G_entail)

lemma falseRule [intro]:
  "R,G \<turnstile>\<^sub>\<L> {} { c } Q"
proof -
  have "rg.rules (lift\<^sub>R R \<L>) (lift\<^sub>G G \<L>) {} (c) {}" using rg.false by auto
  thus ?thesis unfolding Valid_def by (rule rg.rewrite, auto simp: liftState_def)
qed

lemma loopRuleAlt [intro]:
  assumes "stable P (invSec \<L> \<inter> R)" "R,G \<turnstile>\<^sub>\<L> P {c} P" "P \<subseteq> Q" 
  shows "R,G \<turnstile>\<^sub>\<L> P {c*} Q"
proof (rule rewriteRule)
  show "R,G \<turnstile>\<^sub>\<L> P {c*} P" using assms by auto
qed (insert assms(3), auto)

lemma actRule [intro]:
  assumes "stable P (invSec \<L> \<inter> R)" "stable Q (invSec \<L> \<inter> R)"
  assumes "str Q" "str_env G"
  assumes "guarantee (secure \<L> \<inter> P) (invSec \<L> \<inter> G) \<alpha>"
  assumes "weakestpre (secure \<L> \<inter> P) Q \<alpha>"
  assumes "executable (secure \<L> \<inter> P) \<alpha>" 
  shows "R,G \<turnstile>\<^sub>\<L> P { Basic \<alpha> } Q"
  using assms unfolding Valid_def
  by (intro rg.act guarantee weakestpre_conj weakestpre\<L> weakestpreQ executable) auto

end

end