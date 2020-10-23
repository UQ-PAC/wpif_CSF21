theory Typed_Memory
  imports Main
begin

type_synonym ('var,'val) Mem = "'var \<Rightarrow> 'val"
type_synonym ('Var,'Val) Sec = "'Var \<Rightarrow> ('Var,'Val) Mem set"
type_synonym ('var) Type = "'var \<Rightarrow> bool"
type_synonym ('var,'val) TState = "(('var,'val) Mem \<times> 'var Type) set"
type_synonym ('var,'val) TStep = "(('var,'val) Mem \<times> 'var Type) rel"

definition mem_delta :: "('var,'val) Mem \<Rightarrow> ('var,'val) Mem \<Rightarrow> ('var) Type"
  (infix "\<triangle>" 150)
  where "mem_delta m\<^sub>1 m\<^sub>2 \<equiv> \<lambda>v. m\<^sub>1 v = m\<^sub>2 v"

definition type_ord :: "('var) Type \<Rightarrow> ('var) Type \<Rightarrow> bool" 
  (infix "\<ge>\<^sub>\<Gamma>" 50)
  where "type_ord \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> \<forall>x. \<Gamma>\<^sub>1 x \<longrightarrow> \<Gamma>\<^sub>2 x"

definition type_ord_env :: "('var) Type \<Rightarrow> ('var) Type \<Rightarrow> ('var) Type \<Rightarrow> ('var) Type \<Rightarrow> bool" 
  where "type_ord_env \<Gamma> \<Gamma>' \<Gamma>n \<Gamma>n' \<equiv> \<forall>x. (\<Gamma> x = \<Gamma>n x \<and> (\<Gamma>' x \<longrightarrow> \<Gamma>n' x)) \<or> (\<not> \<Gamma> x \<and> \<not> \<Gamma>' x \<and> \<Gamma>n x \<and> \<Gamma>n' x)"


locale typed_memory

context typed_memory
begin

definition str :: "('Var,'Val) TState \<Rightarrow> bool"
  where "str P \<equiv> \<forall>m \<Gamma> \<Gamma>'. (m,\<Gamma>) \<in> P \<and> \<Gamma> \<ge>\<^sub>\<Gamma> \<Gamma>' \<longrightarrow> (m,\<Gamma>') \<in> P"

definition str_env :: "('Var,'Val) TStep \<Rightarrow> bool"
  where "str_env G \<equiv> \<forall>m m' \<Gamma> \<Gamma>' \<Gamma>n \<Gamma>n'. ((m,\<Gamma>),(m',\<Gamma>')) \<in> G \<and> \<Gamma>n \<ge>\<^sub>\<Gamma> \<Gamma> \<and> \<Gamma>' \<ge>\<^sub>\<Gamma> \<Gamma>n' \<longrightarrow> ((m,\<Gamma>n),(m',\<Gamma>n')) \<in> G"

definition preserve :: "('Var, 'Val) TState \<Rightarrow> ('Var, 'Val) TStep"
  where "preserve P \<equiv> {((m,\<Gamma>),(m',\<Gamma>')). (m,\<Gamma>) \<in> P \<longrightarrow> (m',\<Gamma>') \<in> P}"

lemma mem_delta_flip:
  "m\<^sub>1 \<triangle> m\<^sub>2 = m\<^sub>2 \<triangle> m\<^sub>1"
  by (auto simp: mem_delta_def)

lemma str_env_conj [intro]:
  assumes "str_env P" "str_env Q"
  shows "str_env (P \<inter> Q)"
  using assms by (auto simp: str_env_def)

lemma \<Gamma>_ord_refl [intro]:
  shows "\<Gamma> \<ge>\<^sub>\<Gamma> \<Gamma>"
  by (auto simp: type_ord_def)

end

end