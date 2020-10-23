theory Language_Lift
  imports Security_Policy
begin

text \<open>
Link a language definition to the deeply embedded predicate language,
to enable reasoning about the language's operations within the logic.
The language is assumed to consist of expressions over one type of values
and boolean operations over these same values.
Additionally, the boolean operations must support negation.
Moreover, the operations are assumed to be deterministic.
\<close>

datatype ('var, 'aexp, 'bexp) Action =
  Assign "'var" "'aexp"  (infix "\<leftarrow>" 999)
  | Guard "'bexp" ("\<lbrace>_\<rbrace>" [0] 999)
  | CAS "'var" "'aexp" "'aexp"
  | NCAS "'var" "'aexp" "'aexp"
  | Store "'var list" "'aexp" "'aexp"
  | Load "'var" "'var list" "'aexp"
  | Nop
  | Stop

locale language_lift = 
  security_policy all_vars 
  for all_vars :: "'Var list" +
  fixes eval\<^sub>A :: "('Var, nat) Mem \<Rightarrow> 'Aexp \<Rightarrow> nat"
  fixes eval\<^sub>B :: "('Var, nat) Mem \<Rightarrow> 'Bexp \<Rightarrow> bool"
  fixes lift\<^sub>A :: "'Aexp \<Rightarrow> ('Var,nat) exp"
  fixes lift\<^sub>B :: "'Bexp \<Rightarrow> ('Var,nat) pred"
  fixes vars\<^sub>A :: "'Aexp \<Rightarrow> 'Var list"
  fixes vars\<^sub>B :: "'Bexp \<Rightarrow> 'Var list"
  fixes not :: "'Bexp \<Rightarrow> 'Bexp"
  assumes lift\<^sub>A_correct[simp]: "\<And>e mem. eval mem (lift\<^sub>A e) = eval\<^sub>A mem e"
  assumes lift\<^sub>B_correct[simp]: "\<And>e mem \<Gamma>. test mem \<Gamma> (lift\<^sub>B e) = eval\<^sub>B mem e"
  assumes not_correct [simp]: "\<And>e mem. eval\<^sub>B mem (not e) = (\<not> eval\<^sub>B mem e)"
  assumes not_vars [simp]: "vars\<^sub>B (not b) = vars\<^sub>B b"
  assumes vars\<^sub>A_correct [simp]: "\<And>e. set (vars\<^sub>A e) = vars\<^sub>e (lift\<^sub>A e)"
  assumes vars\<^sub>B_correct [simp]: "\<And>e. set (vars\<^sub>B e) = vars\<^sub>p (lift\<^sub>B e)"

context language_lift
begin

lemma eval\<^sub>A_det:
  assumes "\<forall>x \<in> vars\<^sub>e (lift\<^sub>A e). mem\<^sub>1 x = mem\<^sub>2 x" (is "\<forall>x \<in> vars\<^sub>e ?e. ?eq x")
  shows "eval\<^sub>A mem\<^sub>1 e = eval\<^sub>A mem\<^sub>2 e"
proof -
  have "eval\<^sub>A mem\<^sub>1 e = eval mem\<^sub>1 ?e" "eval\<^sub>A mem\<^sub>2 e = eval mem\<^sub>2 ?e" 
    using lift\<^sub>A_correct by auto
  moreover have "eval mem\<^sub>1 ?e = eval mem\<^sub>2 ?e" using assms 
    by (auto simp del: lift\<^sub>A_correct intro!: eval_vars_det)
  ultimately show ?thesis by auto
qed

lemma eval\<^sub>B_det:
  assumes "\<forall>x \<in> vars\<^sub>p (lift\<^sub>B e). mem\<^sub>1 x = mem\<^sub>2 x" (is "\<forall>x \<in> vars\<^sub>p ?e. ?eq x")
  shows "eval\<^sub>B mem\<^sub>1 e = eval\<^sub>B mem\<^sub>2 e"
proof -
  have "\<forall>\<Gamma>. eval\<^sub>B mem\<^sub>1 e = test mem\<^sub>1 \<Gamma> ?e" "\<forall>\<Gamma>. eval\<^sub>B mem\<^sub>2 e = test mem\<^sub>2 \<Gamma> ?e" 
    using lift\<^sub>B_correct by auto
  moreover obtain \<Gamma> where "test mem\<^sub>1 \<Gamma> ?e = test mem\<^sub>2 \<Gamma> ?e" using assms 
    by (auto simp del: lift\<^sub>B_correct intro!: test_vars_det)
  ultimately show ?thesis by blast
qed

fun update :: "('Var, 'Aexp, 'Bexp) Action \<Rightarrow> ('Var, nat) Mem rel"
  where
  "update (\<lbrace>b\<rbrace>) = {(m,m'). m' = m \<and> eval\<^sub>B m b}" |
  "update (x \<leftarrow> e) = {(m,m'). m' = m(x := eval\<^sub>A m e)}" |
  "update (CAS x e\<^sub>1 e\<^sub>2) = {(m,m'). m x = eval\<^sub>A m e\<^sub>1 \<and> m' = m(x := eval\<^sub>A m e\<^sub>2)}" |
  "update (NCAS x e\<^sub>1 e\<^sub>2) = {(m,m'). m x \<noteq> eval\<^sub>A m e\<^sub>1 \<and> m' = m}" |
  "update Nop = {(m,m'). m = m'}" |
  "update Stop = {}" |
  "update (Store x i e) = {(m,m'). set x \<inter> set (vars\<^sub>A i) = {} \<and> length x > (eval\<^sub>A m i) \<and> m' = m((x ! (eval\<^sub>A m i)) := eval\<^sub>A m e)}" |
  "update (Load r x i) = {(m,m'). length x > (eval\<^sub>A m i) \<and> m' = m(r := (m (x ! (eval\<^sub>A m i))))}" 

fun negate :: "('Var, 'Aexp, 'Bexp) Action \<Rightarrow> ('Var, 'Aexp, 'Bexp) Action"
  where
  "negate (\<lbrace>b\<rbrace>) = (\<lbrace>not b\<rbrace>)" |
  "negate Stop = Nop" |
  "negate (CAS x e\<^sub>1 e\<^sub>2) = (NCAS x e\<^sub>1 e\<^sub>2)" |
  "negate (NCAS x e\<^sub>1 e\<^sub>2) = (CAS x e\<^sub>1 e\<^sub>2)" |
  "negate _ = Stop"

end

end