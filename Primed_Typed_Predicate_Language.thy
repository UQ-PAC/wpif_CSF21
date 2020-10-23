theory Primed_Typed_Predicate_Language
  imports Typed_Predicate_Language
begin                   

text \<open>
Extend the predicate language with a concept of original and primed variables
\<close>

datatype 'var Primed = 
  Orig "'var" ("_\<^sup>o" [1000] 1000)
| Prime "'var" ("_`" [1000] 1000)

type_synonym ('var,'val) rexp = "('var Primed,'val) exp"
type_synonym ('var,'val) rpred = "('var Primed,'val) pred"

abbreviation transition (infixr "\<mapsto>" 50)
  where "transition m\<^sub>1 m\<^sub>2 \<equiv> case_Primed m\<^sub>1 m\<^sub>2"

definition reflexive :: "('var,'val) rpred \<Rightarrow> bool"
  where "reflexive R \<equiv> \<forall>m \<Gamma>. test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) R"

definition transitive :: "('var,'val) rpred \<Rightarrow> bool"
  where "transitive R \<equiv> \<forall>m \<Gamma> m' \<Gamma>' m'' \<Gamma>''. 
    test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R \<longrightarrow> test (m' \<mapsto> m'') (\<Gamma>' \<mapsto> \<Gamma>'') R \<longrightarrow> test (m \<mapsto> m'') (\<Gamma> \<mapsto> \<Gamma>'') R"

definition preserved :: "('var,'val) pred \<Rightarrow> ('var,'val) rpred"
  where "preserved P \<equiv> map\<^sub>p Orig P \<longrightarrow>\<^sub>p  map\<^sub>p Prime P"

definition \<Gamma>_env_wf :: "('Var,'Val) rpred \<Rightarrow> bool"
  where "\<Gamma>_env_wf P \<equiv> \<forall>m m' \<Gamma> \<Gamma>' \<Gamma>n \<Gamma>n'. test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') P \<and> \<Gamma> \<sqsupseteq> \<Gamma>n \<and> \<Gamma>n' \<sqsupseteq> \<Gamma>' \<longrightarrow> test (m \<mapsto> m') (\<Gamma>n \<mapsto> \<Gamma>n') P"

(* Functions to lift predicates over one memory to two *)
definition orig\<^sub>e :: "('var, 'val) exp \<Rightarrow> ('var Primed, 'val) exp"
  where "orig\<^sub>e P \<equiv> map\<^sub>e Orig P"

definition orig :: "('var, 'val) pred \<Rightarrow> ('var , 'val) rpred"
  where "orig P \<equiv> map\<^sub>p Orig P"

definition prime :: "('var, 'val) pred \<Rightarrow> ('var , 'val) rpred"
  where "prime P \<equiv> map\<^sub>p Prime P"

(* Functions to drop predicates over two memories to one *)
definition unprime\<^sub>r :: "('var, 'val) rpred \<Rightarrow> ('var, 'val) pred"
  where "unprime\<^sub>r P \<equiv> map\<^sub>p (case_Primed id id) P"

lemma test_unprime [simp]:
  "test m \<Gamma> (unprime\<^sub>r G) = (test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) G)"
proof -
  have "test (m \<mapsto> m) (\<Gamma> \<mapsto> \<Gamma>) G = test  m \<Gamma> (unprime\<^sub>r G)"
    by (auto intro!: map\<^sub>p_vars_det simp: unprime\<^sub>r_def split: Primed.splits)
  thus ?thesis by auto
qed

lemma [simp]:
  "(m \<mapsto> m')(x` := e) = (m \<mapsto> (m'(x := e)))" (is "?l = ?r")
proof -
  have "\<forall>x. ?l x = ?r x" by (auto split: Primed.splits)
  thus ?thesis by blast
qed

lemma [simp]:
  "eval (m \<mapsto> m') (orig\<^sub>e e) = eval m e"
proof -
  have "eval m e = eval (m \<mapsto> m') (orig\<^sub>e e)"
    by (auto intro!: map\<^sub>e_vars_det simp: orig\<^sub>e_def)
  thus ?thesis by auto
qed

lemma [simp]:
  "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') (orig e) = test m \<Gamma> e"
proof -
  have "test m \<Gamma> e = test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') (orig e)"
    by (auto intro!: map\<^sub>p_vars_det simp: orig_def)
  thus ?thesis by auto
qed

end