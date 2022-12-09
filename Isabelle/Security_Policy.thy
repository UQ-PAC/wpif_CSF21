theory Security_Policy
  imports Typed_Predicate_Language
begin

text \<open>
Locale for defining and managing an invariant security policy
\<close>

type_synonym ('Var,'Val) policy = "'Var \<Rightarrow> ('Var,'Val) pred"

locale security_policy =
  fixes all_vars :: "'Var list"
  assumes all_vars_correct[simp]: "set all_vars = UNIV"

context security_policy
begin


end

end