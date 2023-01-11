theory Indexed_Typed_Predicate_Language
  imports Primed_Typed_Predicate_Language
begin

text \<open>
Extend the predicate language with a concept of indexed variables
\<close>

type_synonym ('var,'val) iexp = "(nat\<times>'var,'val) exp"
type_synonym ('var,'val) ipred = "(nat\<times>'var,'val) pred"

definition merge (infixr "\<Oplus>" 50)
  where "merge m\<^sub>1 m\<^sub>2 \<equiv> \<lambda>(n,x). (case (n::nat) of 0 \<Rightarrow> m\<^sub>1 x | Suc m \<Rightarrow> m\<^sub>2 (m,x))"

abbreviation orig_var ("_\<^sup>0" [1000] 1000) 
  where "x\<^sup>0 \<equiv> (0,x)"

abbreviation prime_var ("_\<^sup>1" [1000] 1000) 
  where "x\<^sup>1 \<equiv> (Suc 0,x)"

definition prime
  where "prime P ign \<equiv> map\<^sub>o (\<lambda>x. if snd x \<in> ign \<and> fst x = 0 then (Suc (fst x), snd x) else x) 
                       (map\<^sub>p (\<lambda>x. if snd x \<in> ign \<and> fst x = 0 then x else (Suc (fst x), snd x)) P)"

definition unprime
  where "unprime P \<equiv> map\<^sub>p (\<lambda>x. case x of (0,v) \<Rightarrow> (0,v) | (Suc n,v) \<Rightarrow> (n, v)) P"

definition exp\<^sub>0 :: "('Var,'Val) exp \<Rightarrow> ('Var,'Val) iexp"
  where "exp\<^sub>0 P = map\<^sub>e (\<lambda>x. (0,x)) P"

definition pred\<^sub>0 :: "('Var,'Val) pred \<Rightarrow> ('Var,'Val) ipred"
  where "pred\<^sub>0 P = map\<^sub>p (\<lambda>x. (0,x)) P"

definition pred\<^sub>r :: "('Var,'Val) rpred \<Rightarrow> ('Var,'Val) ipred"
  where "pred\<^sub>r P \<equiv> map\<^sub>p (case_Primed (Pair 0) (Pair 1)) P"

definition asn :: "('var,'val) Mem \<Rightarrow> 'var Type \<Rightarrow> ('var,'val) ipred \<Rightarrow> bool"
  where "asn m \<Gamma> P \<equiv> \<forall>m' \<Gamma>'. test (m \<Oplus> m') (\<Gamma> \<Oplus> \<Gamma>') P"

definition mergei 
  where "mergei m\<^sub>1 i m\<^sub>2 \<equiv> \<lambda>(n,x). if x \<in> i \<and> n = 0 then m\<^sub>1 (x) else m\<^sub>2 (n,x)"

lemma prime [simp]:
  "test (m' \<Oplus> m'') (\<Gamma>' \<Oplus> \<Gamma>'') (prime Q i) = test (mergei m' i m'') (\<Gamma>'') Q"
proof -
  let ?\<Gamma>="(\<lambda>x. if snd x \<in> i \<and> fst x = 0 then \<Gamma>'' x else (\<Gamma>' \<Oplus> \<Gamma>'') x)"

  have a: "test (mergei m' i m'') \<Gamma>'' Q = test (m' \<Oplus> m'') ?\<Gamma> (map\<^sub>p (\<lambda>x. if snd x \<in> i \<and> fst x = 0 then x else (Suc (fst x), snd x)) Q)"
    unfolding prime_def
    apply (intro allI map\<^sub>p_vars_det)
    by (auto simp: merge_def mergei_def split: nat.splits)
  have b: "test (m' \<Oplus> m'') ?\<Gamma> (map\<^sub>p (\<lambda>x. if snd x \<in> i \<and> fst x = 0 then x else (Suc (fst x), snd x)) Q) = 
           test (m' \<Oplus> m'') (\<Gamma>' \<Oplus> \<Gamma>'') (map\<^sub>o (\<lambda>x. if snd x \<in> i \<and> fst x = 0 then (Suc (fst x), snd x) else x) (map\<^sub>p (\<lambda>x. if snd x \<in> i \<and> fst x = 0 then x else (Suc (fst x), snd x)) Q))"
    apply (intro allI map\<^sub>o_vars_det)
    by (auto simp: merge_def mergei_def split: nat.splits)

  show ?thesis
    unfolding prime_def
    using a b
    by blast
qed

lemma test_pred\<^sub>r [simp]:
  "test (m \<Oplus> m' \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h) (pred\<^sub>r R) = test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R"
proof -
  have "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R = test (m \<Oplus> m' \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h) (pred\<^sub>r R)"
    unfolding pred\<^sub>r_def
    apply (intro map\<^sub>p_vars_det)
    by (auto simp: merge_def split: nat.splits Primed.splits)
  thus ?thesis by blast
qed

lemma test_pred\<^sub>r_alt:
  "(\<forall>mh \<Gamma>h. test (m \<Oplus> m' \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h) (pred\<^sub>r R)) = test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R"
  by (simp)

lemma merge_split:
  obtains m' mh' where "mh = (m' \<Oplus> mh')"
proof -
  have "\<forall>y. mh y = ((\<lambda>x. mh (0,x)) \<Oplus> (\<lambda>(n,x). mh (Suc n,x))) y" 
    by (auto simp: merge_def split: nat.splits)
  hence "mh = ((\<lambda>x. mh (0,x)) \<Oplus> (\<lambda>(n,x). mh (Suc n,x)))" by blast
  thus ?thesis using that by auto
qed

lemma test_pred\<^sub>r' [elim!]:
  assumes "test mh \<Gamma>h (pred\<^sub>r R)"
  obtains m \<Gamma> m' \<Gamma>' mh' \<Gamma>h' where "test (m \<mapsto> m') (\<Gamma> \<mapsto> \<Gamma>') R" "mh = (m \<Oplus> m' \<Oplus> mh')" "\<Gamma>h = (\<Gamma> \<Oplus> \<Gamma>' \<Oplus> \<Gamma>h')"
proof -
  obtain m \<Gamma> mh' \<Gamma>h' where s: "mh = (m \<Oplus> mh')" "\<Gamma>h = (\<Gamma> \<Oplus> \<Gamma>h')" using merge_split by smt
  obtain m' \<Gamma>' mh'' \<Gamma>h'' where s': "mh' = (m' \<Oplus> mh'')" "\<Gamma>h' = (\<Gamma>' \<Oplus> \<Gamma>h'')" using merge_split by smt
  show ?thesis using that assms unfolding s s' by (auto simp add: )
qed

lemma [simp]:
  "asn m \<Gamma> (P \<and>\<^sub>p Q) = (asn m \<Gamma> P \<and> asn m \<Gamma> Q)"
  unfolding asn_def by auto

lemma asn_unprime [simp]:
  "asn m \<Gamma> (unprime G) = (\<forall>mh \<Gamma>h. test (m \<Oplus> m \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma> \<Oplus> \<Gamma>h) G)"
proof -
  have "\<forall>mh \<Gamma>h. test (m \<Oplus> m \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma> \<Oplus> \<Gamma>h) G = 
              (test (m \<Oplus> mh) (\<Gamma> \<Oplus> \<Gamma>h) (map\<^sub>p (\<lambda>(a, v). case a of 0 \<Rightarrow> v\<^sup>0 | Suc n \<Rightarrow> (n, v)) G))"
    apply (intro allI map\<^sub>p_vars_det)
    by (auto simp: merge_def split: nat.splits)
  thus ?thesis unfolding asn_def unprime_def by blast
qed

lemma eval_exp\<^sub>0 [simp]:
  "eval (m \<Oplus> mh) (exp\<^sub>0 ( e)) = eval m ( e)"
proof -
  have "eval m ( e) = eval (m \<Oplus> mh) (exp\<^sub>0 ( e))"
    by (auto intro!: map\<^sub>e_vars_det simp: exp\<^sub>0_def merge_def)
  thus ?thesis by auto
qed

lemma test_pred\<^sub>0 [simp]:
  "test (m \<Oplus> m') (\<Gamma> \<Oplus> \<Gamma>') (pred\<^sub>0 P) = test m \<Gamma> P"
proof -
  have "test m \<Gamma> P = test (m \<Oplus> m') (\<Gamma> \<Oplus> \<Gamma>')  (pred\<^sub>0 P)"
    by (auto intro!: map\<^sub>p_vars_det simp: pred\<^sub>0_def merge_def)
  thus ?thesis by auto
qed

lemma asn_pred\<^sub>0[simp]:
  "asn m \<Gamma> (pred\<^sub>0 (P :: ('a, 'b) pred)) = test m \<Gamma> P"
  unfolding asn_def by simp

lemma [simp]:
  "asn m \<Gamma> (pred\<^sub>0 P \<longrightarrow>\<^sub>p Q) = (test m \<Gamma> P \<longrightarrow> asn m \<Gamma> Q)"
  unfolding asn_def by simp

lemma merge_0[simp]:
  "(m \<Oplus> m')(x\<^sup>0 := e) = (m(x := e) \<Oplus> m')" (is "?l = ?r")
proof -
  have "\<forall>y. ?l y = ?r y" by (auto simp: merge_def split: nat.splits)
  thus ?thesis by blast
qed

lemma merge_1[simp]:
  "(m \<Oplus> m' \<Oplus> mh)(x\<^sup>1 := e) = (m \<Oplus> m'(x := e) \<Oplus> mh)" (is "?l = ?r")
proof -
  have "\<forall>y. ?l y = ?r y" by (auto simp: merge_def split: nat.splits)
  thus ?thesis by blast
qed

lemma asn_subst\<^sub>\<Gamma>[simp]:
  "asn m \<Gamma> (subst\<^sub>\<Gamma> Q x\<^sup>0 (pred\<^sub>0 e)) = asn m (\<Gamma>(x := test m \<Gamma> e)) Q"
  unfolding asn_def by simp

lemma asn_subst\<^sub>p[simp]:
  "asn m \<Gamma> (subst\<^sub>p Q x\<^sup>0 (exp\<^sub>0 e)) = asn (m(x := eval m e)) \<Gamma> Q"
  unfolding asn_def by simp

lemma merge_eq [simp]:
  "( (m1 \<Oplus> m1') = (m2 \<Oplus> m2') ) = (m1 = m2 \<and> m1' = m2')"
proof 
  assume "(m1 \<Oplus> m1') = (m2 \<Oplus> m2')"
  hence "\<forall>x. (m1 \<Oplus> m1') (0,x) = (m2 \<Oplus> m2') (0,x)" 
        "\<forall>x n. (m1 \<Oplus> m1') (Suc n,x) = (m2 \<Oplus> m2') (Suc n,x)" by auto
  thus "m1 = m2 \<and> m1' = m2'" by (auto simp: merge_def)
qed auto

lemma pred\<^sub>0_entail [intro]:
  assumes "P \<turnstile>\<^sub>p Q" 
  shows "pred\<^sub>0 P \<turnstile>\<^sub>p pred\<^sub>0 Q"
  unfolding entail_def 
proof (clarsimp)
  fix mh \<Gamma>h assume "test mh \<Gamma>h (pred\<^sub>0 P :: ('a,'b) ipred)"
  moreover obtain m \<Gamma> mh' \<Gamma>h' where "mh = (m \<Oplus> mh')" "\<Gamma>h = (\<Gamma> \<Oplus> \<Gamma>h')" using merge_split by smt
  ultimately show "test mh \<Gamma>h (pred\<^sub>0 Q)" using assms by (simp add: entail_def)
qed

abbreviation wp\<^sub>a
  where "wp\<^sub>a x e t Q \<equiv> subst\<^sub>\<Gamma> (subst\<^sub>p Q x\<^sup>0 (exp\<^sub>0 e)) x\<^sup>0 (pred\<^sub>0 t)"

abbreviation wp\<^sub>b
  where "wp\<^sub>b b Q \<equiv> pred\<^sub>0 b \<longrightarrow>\<^sub>p Q"

definition wp\<^sub>l
  where "wp\<^sub>l x i e t \<equiv> foldi 0 (\<lambda>j v. wp\<^sub>a v (Ternary (Const j) i e (Var v)) (PTer (Const j) i t (Low v))) x"

text \<open>Show that wpl is the weakest precondition for a list store\<close>
lemma asn_foldi_nop [simp]:
  assumes "eval m i < k"
  shows "asn m \<Gamma> (foldi k (\<lambda>j v Q. subst\<^sub>\<Gamma> (subst\<^sub>p Q v\<^sup>0 (exp\<^sub>0 (Ternary (Const j) i e (Var v)))) v\<^sup>0 (pred\<^sub>0 (PTer (Const j) i t (Low v)))) x Q) = asn m \<Gamma> Q"
  using assms by (induct x arbitrary: k Q) simp+

lemma wp\<^sub>l [simp]:
  assumes "eval m i < length x"
  assumes "set x \<inter> vars\<^sub>e i = {}"
  shows "asn m \<Gamma> (wp\<^sub>l x i e t Q) = asn (m(x ! eval m i := eval m e)) (\<Gamma>(x ! eval m i := test m \<Gamma> t)) Q"
proof -
  have "\<And>k Q. k \<le> eval m i \<Longrightarrow> eval m i - k < length x \<Longrightarrow> set x \<inter> vars\<^sub>e i = {} \<Longrightarrow> asn m \<Gamma> (foldi k (\<lambda>j v. wp\<^sub>a v (Ternary (Const j) i e (Var v)) (PTer (Const j) i t (Low v))) x Q) = asn (m(x ! (eval m i - k) := eval m e)) (\<Gamma>(x ! (eval m i - k) := test m \<Gamma> t)) Q"
  proof (induct x)
    case (Cons a x)
    then show ?case
    proof (cases "eval m i = k")
      case True
      moreover have "m(a := eval m e) = (\<lambda>b. if b = a then eval m e else m b)" by auto
      moreover have "\<Gamma>(a := test m \<Gamma> t) = (\<lambda>x. (x = a \<longrightarrow> test m \<Gamma> t) \<and> (x \<noteq> a \<longrightarrow> \<Gamma> x))" by auto
      ultimately show ?thesis by auto
    next
      case False
      have "asn m \<Gamma> (foldi (Suc k) (\<lambda>j v. wp\<^sub>a v (Ternary (Const j) i e (Var v)) (PTer (Const j) i t (Low v))) x (subst\<^sub>\<Gamma> (subst\<^sub>p Q a\<^sup>0 (exp\<^sub>0 (Ternary (Const k) i e (Var a)))) a\<^sup>0 (pred\<^sub>0 (PTer (Const k) i t (Low a))))) = 
            asn (m(x ! (eval m i -(Suc k)) := eval m e)) (\<Gamma>(x ! (eval m i - (Suc k)) := test m \<Gamma> t)) (subst\<^sub>\<Gamma> (subst\<^sub>p Q a\<^sup>0 (exp\<^sub>0 (Ternary (Const k) i e (Var a)))) a\<^sup>0 (pred\<^sub>0 (PTer (Const k) i t (Low a))))"
        using False Cons(2,3,4) by (intro Cons(1)) auto
      also have "... = asn (m((a # x) ! (eval m i - k) := eval m e)) (\<Gamma>((a # x) ! (eval m i - k) := test m \<Gamma> t)) Q"
      proof -
        have noMod: "eval (m(x ! (eval m i - Suc k) := eval m e)) i = eval m i"
        proof (intro eval_vars_det ballI impI)
          fix v assume a: "v \<in> vars\<^sub>e i"
          have "x ! (eval m i - Suc k) \<in> set x" using Cons False by auto
          hence "v \<noteq> x ! (eval m i - Suc k)" using Cons(4) a by auto
          thus "(m(x ! (eval m i - Suc k) := eval m e)) v = m v" by auto
        qed
        have "(a # x) ! (eval m i - k) = x ! (eval m i - Suc k)" using Cons(2) False by auto
        thus ?thesis using noMod False by (auto simp: fun_upd_twist)
      qed
      finally show ?thesis by fastforce
    qed
  qed simp
  thus ?thesis using assms by (auto simp: wp\<^sub>l_def)
qed

end