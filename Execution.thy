theory Execution
  imports Trace
begin

section \<open>Execution\<close>

text \<open>
Given a reordering relation and evaluation behaviour of a language,
convert a trace into manipulations over memory.
\<close>

locale execution =
  fixes eval :: "'a \<Rightarrow> 's rel" 

context execution
begin

inductive trace_mem
  where 
    "trace_mem m [] m" | 
    "(m'', m) \<in> eval \<alpha> \<Longrightarrow> trace_mem m t m' \<Longrightarrow> trace_mem m'' (\<alpha>#t) m'"

definition ev :: "'a Stmt \<Rightarrow> 's \<Rightarrow> 'a Trace \<Rightarrow> 'a Stmt  \<Rightarrow> 's \<Rightarrow> bool"
  ("\<langle>_,_\<rangle> \<rightarrow>_\<^sup>* \<langle>_,_\<rangle>" [50,40,40] 70)
  where "\<langle>c,m\<rangle> \<rightarrow>t\<^sup>* \<langle>c',m'\<rangle> \<equiv> trace_mem m t m' \<and> c \<mapsto>t\<^sup>* c'"

end

end