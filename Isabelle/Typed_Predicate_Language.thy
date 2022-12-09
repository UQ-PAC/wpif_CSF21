theory Typed_Predicate_Language
  imports Typed_Memory
begin

datatype ('var,'val) exp =
  Var "'var"
  | Const "'val"
  | Op "('val \<Rightarrow> 'val \<Rightarrow> 'val)" "('var,'val) exp" "('var,'val) exp"
  | Ternary "('var,'val) exp" "('var,'val) exp" "('var,'val) exp" "('var,'val) exp"

datatype ('var, 'val) pred =
  Pb "bool" 
  | PDisj "('var,'val) pred" "('var,'val) pred" (infixr "\<or>\<^sub>p" 30)
  | PConj "('var,'val) pred" "('var,'val) pred" (infixr "\<and>\<^sub>p" 35)
  | PImp  "('var,'val) pred" "('var,'val) pred" (infixr "\<longrightarrow>\<^sub>p" 25)
  | PNeg  "('var,'val) pred"
  | PCmp  "('val \<Rightarrow> 'val \<Rightarrow> bool)" "('var,'val) exp" "('var,'val) exp"
  | PBoo  "bool \<Rightarrow> ('var, 'val) pred"
  | Low   "('var)"
  | PTer "('var,'val) exp" "('var,'val) exp" "('var,'val) pred" "('var,'val) pred"

primrec
  eval :: "('var,'val) Mem \<Rightarrow> ('var,'val) exp \<Rightarrow> 'val"
where
  "eval m (Var v) = m v" |
  "eval m (Const c) = c" |
  "eval m (Op bop e f) = bop (eval m e) (eval m f)" |
  "eval m (Ternary v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (if (eval m v\<^sub>1) = (eval m v\<^sub>2) then (eval m e\<^sub>1) else (eval m e\<^sub>2))"

primrec
  test :: "('var,'val) Mem \<Rightarrow> 'var Type \<Rightarrow> ('var,'val) pred \<Rightarrow> bool"
where
  "test m \<Gamma> (Pb v) = v" |
  "test m \<Gamma> (PDisj p q) = (test m \<Gamma> p \<or> test m \<Gamma> q)" |
  "test m \<Gamma> (PConj p q) = (test m \<Gamma> p \<and> test m \<Gamma> q)" |
  "test m \<Gamma> (PImp p q) = (test m \<Gamma> p \<longrightarrow> test m \<Gamma> q)" |
  "test m \<Gamma> (PNeg p) = (\<not> test m \<Gamma> p)" |
  "test m \<Gamma> (PCmp c e f) = (c (eval m e) (eval m f))" |
  "test m \<Gamma> (PBoo p) = (\<forall>c. test m \<Gamma> (p c))" |
  "test m \<Gamma> (Low v) = (\<Gamma> v)" |
  "test m \<Gamma> (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (if (eval m v\<^sub>1) = (eval m v\<^sub>2) then (test m \<Gamma> e\<^sub>1) else (test m \<Gamma> e\<^sub>2))"

primrec
  vars\<^sub>e :: "('var,'val) exp \<Rightarrow> ('var) set"
where
  "vars\<^sub>e (Var v) = { v }" |
  "vars\<^sub>e (Const c) = {}" |
  "vars\<^sub>e (Op bop e f) = (vars\<^sub>e e \<union> vars\<^sub>e f)" |
  "vars\<^sub>e (Ternary v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (vars\<^sub>e v\<^sub>1 \<union> vars\<^sub>e v\<^sub>2 \<union> vars\<^sub>e e\<^sub>1 \<union> vars\<^sub>e e\<^sub>2)"

primrec
  vars\<^sub>p :: "('var,'val) pred \<Rightarrow> ('var) set"
where
  "vars\<^sub>p (Pb v) = {}" |
  "vars\<^sub>p (PNeg p) = vars\<^sub>p p" |
  "vars\<^sub>p (PConj p q) = (vars\<^sub>p p \<union> vars\<^sub>p q)" |
  "vars\<^sub>p (PDisj p q) = (vars\<^sub>p p \<union> vars\<^sub>p q)" |
  "vars\<^sub>p (PImp p q) = (vars\<^sub>p p \<union> vars\<^sub>p q)" |
  "vars\<^sub>p (PCmp cmp e f) = (vars\<^sub>e e \<union> vars\<^sub>e f)" |
  "vars\<^sub>p (PBoo p) = (\<Union>v. vars\<^sub>p (p v))" |
  "vars\<^sub>p (Low v) = {}" |
  "vars\<^sub>p (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (vars\<^sub>e v\<^sub>1 \<union> vars\<^sub>e v\<^sub>2 \<union> vars\<^sub>p e\<^sub>1 \<union> vars\<^sub>p e\<^sub>2)"

primrec
  vars\<^sub>\<Gamma> :: "('var, 'val) pred \<Rightarrow> ('var) set"
where
  "vars\<^sub>\<Gamma> (Pb v) = {}" |
  "vars\<^sub>\<Gamma> (PNeg p) = vars\<^sub>\<Gamma> p" |
  "vars\<^sub>\<Gamma> (PConj p q) = (vars\<^sub>\<Gamma> p \<union> vars\<^sub>\<Gamma> q)" |
  "vars\<^sub>\<Gamma> (PDisj p q) = (vars\<^sub>\<Gamma> p \<union> vars\<^sub>\<Gamma> q)" |
  "vars\<^sub>\<Gamma> (PImp p q) = (vars\<^sub>\<Gamma> p \<union> vars\<^sub>\<Gamma> q)" |
  "vars\<^sub>\<Gamma> (PCmp cmp e f) = {}" |
  "vars\<^sub>\<Gamma> (PBoo p) = (\<Union>v. vars\<^sub>\<Gamma> (p v))" |
  "vars\<^sub>\<Gamma> (Low v) = {v}" |
  "vars\<^sub>\<Gamma> (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (vars\<^sub>\<Gamma> e\<^sub>1 \<union> vars\<^sub>\<Gamma> e\<^sub>2)"

primrec
  subst\<^sub>e :: "('var,'val) exp \<Rightarrow> ('var) \<Rightarrow> ('var,'val) exp \<Rightarrow> ('var,'val) exp"
where
  "subst\<^sub>e (Var v) x e = (if v = x then e else Var v)" |
  "subst\<^sub>e (Const c) x e = (Const c)" |
  "subst\<^sub>e (Op bop f s) x e = (Op bop (subst\<^sub>e f x e) (subst\<^sub>e s x e))" |
  "subst\<^sub>e (Ternary v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) x e = (Ternary (subst\<^sub>e v\<^sub>1 x e) (subst\<^sub>e v\<^sub>2 x e) (subst\<^sub>e e\<^sub>1 x e) (subst\<^sub>e e\<^sub>2 x e))"

primrec
  subst\<^sub>p :: "('var,'val) pred \<Rightarrow> ('var) \<Rightarrow> ('var,'val) exp \<Rightarrow> ('var,'val) pred"
where
  "subst\<^sub>p (Pb v) x e = (Pb v)" |
  "subst\<^sub>p (PNeg p) x e = (PNeg (subst\<^sub>p p x e))" |
  "subst\<^sub>p (PConj p q) x e = (PConj (subst\<^sub>p p x e) (subst\<^sub>p q x e))" |
  "subst\<^sub>p (PDisj p q) x e = (PDisj (subst\<^sub>p p x e) (subst\<^sub>p q x e))" |
  "subst\<^sub>p (PCmp cmp f s) x e = (PCmp cmp (subst\<^sub>e f x e) (subst\<^sub>e s x e))" |
  "subst\<^sub>p (PImp p q) x e = (PImp (subst\<^sub>p p x e) (subst\<^sub>p q x e))" |
  "subst\<^sub>p (PBoo p) x e = PBoo (\<lambda>v . subst\<^sub>p (p v ) x e)" |
  "subst\<^sub>p (Low p) x e = Low p" |
  "subst\<^sub>p (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) x e = (PTer (subst\<^sub>e v\<^sub>1 x e) (subst\<^sub>e v\<^sub>2 x e) (subst\<^sub>p e\<^sub>1 x e) (subst\<^sub>p e\<^sub>2 x e))"

primrec
  subst\<^sub>\<Gamma> :: "('var,'val) pred \<Rightarrow> ('var) \<Rightarrow> ('var,'val) pred \<Rightarrow> ('var,'val) pred"
where
  "subst\<^sub>\<Gamma> (Pb v) x e = (Pb v)" |
  "subst\<^sub>\<Gamma> (PNeg p) x e = (PNeg (subst\<^sub>\<Gamma> p x e))" |
  "subst\<^sub>\<Gamma> (PConj p q) x e = (PConj (subst\<^sub>\<Gamma> p x e) (subst\<^sub>\<Gamma> q x e))" |
  "subst\<^sub>\<Gamma> (PDisj p q) x e = (PDisj (subst\<^sub>\<Gamma> p x e) (subst\<^sub>\<Gamma> q x e))" |
  "subst\<^sub>\<Gamma> (PCmp cmp f s) x e = (PCmp cmp f s)" |
  "subst\<^sub>\<Gamma> (PImp p q) x e = (PImp (subst\<^sub>\<Gamma> p x e) (subst\<^sub>\<Gamma> q x e))" |
  "subst\<^sub>\<Gamma> (PBoo p) x e = PBoo (\<lambda>v . subst\<^sub>\<Gamma> (p v ) x e)" |
  "subst\<^sub>\<Gamma> (Low p) x e = (if p = x then e else Low p)" |
  "subst\<^sub>\<Gamma> (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) x e = (PTer (v\<^sub>1) (v\<^sub>2) (subst\<^sub>\<Gamma> e\<^sub>1 x e) (subst\<^sub>\<Gamma> e\<^sub>2 x e))"

primrec
  map\<^sub>e :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'val) exp \<Rightarrow> ('b, 'val) exp"
  where
  "map\<^sub>e f (Var p) = (Var (f p))" |
  "map\<^sub>e f (Const v) = (Const v)" |
  "map\<^sub>e f (Op c e g) = (Op c (map\<^sub>e f e) (map\<^sub>e f g))" |
  "map\<^sub>e f (Ternary v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (Ternary (map\<^sub>e f v\<^sub>1) (map\<^sub>e f v\<^sub>2) (map\<^sub>e f e\<^sub>1) (map\<^sub>e f e\<^sub>2))"

primrec
  map\<^sub>p :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'val) pred \<Rightarrow> ('b, 'val) pred"
where
  "map\<^sub>p f (Pb v) = (Pb v)" |
  "map\<^sub>p f (PNeg p) = PNeg (map\<^sub>p f p)" |
  "map\<^sub>p f (PConj p q) = (PConj (map\<^sub>p f p) (map\<^sub>p f q))" |
  "map\<^sub>p f (PDisj p q) = (PDisj (map\<^sub>p f p) (map\<^sub>p f q))" |
  "map\<^sub>p f (PCmp cmp e g) = (PCmp cmp (map\<^sub>e f e) (map\<^sub>e f g))" |
  "map\<^sub>p f (PImp p q) = (PImp (map\<^sub>p f p) (map\<^sub>p f q))" |
  "map\<^sub>p f (PBoo p) = PBoo (\<lambda>v. map\<^sub>p f (p v))" |
  "map\<^sub>p f (Low p) = (Low (f p))" |
  "map\<^sub>p f (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (PTer (map\<^sub>e f v\<^sub>1) (map\<^sub>e f v\<^sub>2) (map\<^sub>p f e\<^sub>1) (map\<^sub>p f e\<^sub>2))"

primrec
  map\<^sub>o :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'val) pred \<Rightarrow> ('a, 'val) pred"
where
  "map\<^sub>o f (Pb v) = (Pb v)" |
  "map\<^sub>o f (PNeg p) = PNeg (map\<^sub>o f p)" |
  "map\<^sub>o f (PConj p q) = (PConj (map\<^sub>o f p) (map\<^sub>o f q))" |
  "map\<^sub>o f (PDisj p q) = (PDisj (map\<^sub>o f p) (map\<^sub>o f q))" |
  "map\<^sub>o f (PCmp cmp e g) = (PCmp cmp ( e) ( g))" |
  "map\<^sub>o f (PImp p q) = (PImp (map\<^sub>o f p) (map\<^sub>o f q))" |
  "map\<^sub>o f (PBoo p) = PBoo (\<lambda>v. map\<^sub>o f (p v))" |
  "map\<^sub>o f (Low p) = (Low (f p))" |
  "map\<^sub>o f (PTer v\<^sub>1 v\<^sub>2 e\<^sub>1 e\<^sub>2) = (PTer ( v\<^sub>1) ( v\<^sub>2) (map\<^sub>o f e\<^sub>1) (map\<^sub>o f e\<^sub>2))"

definition entail :: "('Var,'Val) pred \<Rightarrow> ('Var,'Val) pred \<Rightarrow> bool"
  (infix "\<turnstile>\<^sub>p" 25)
  where "entail P P' \<equiv> \<forall>mem \<Gamma>. test mem \<Gamma> P \<longrightarrow> test mem \<Gamma> P'"

definition equiv :: "('Var,'Val) pred \<Rightarrow> ('Var,'Val) pred \<Rightarrow> bool"
  (infixl "=\<^sub>p" 50)
  where "equiv P P' \<equiv> \<forall>mem \<Gamma>. test mem \<Gamma> P = test mem \<Gamma> P'"

definition \<Gamma>_ord :: "('var) Type \<Rightarrow> ('var) Type \<Rightarrow> bool"
  (infix "\<sqsupseteq>" 50)
  where "\<Gamma>_ord \<Gamma> \<Gamma>' \<equiv> \<forall>x. \<Gamma>' x \<longrightarrow> \<Gamma> x"

definition \<Gamma>_wf :: "('Var,'Val) pred \<Rightarrow> bool"
  where "\<Gamma>_wf P \<equiv> \<forall>m \<Gamma> \<Gamma>'. test m \<Gamma> P \<and> \<Gamma>' \<sqsupseteq> \<Gamma> \<longrightarrow> test m \<Gamma>' P"

definition fold_conj :: "(_,_) pred list \<Rightarrow> (_,_) pred"
  where "fold_conj l \<equiv> fold PConj l (Pb True)"

definition forVars :: "'a list \<Rightarrow> ('a \<Rightarrow> (_,_) pred) \<Rightarrow> (_,_) pred"
  where "forVars V f = fold_conj (map f V)"

(*
definition for_all :: "'a list \<Rightarrow> (_,_) pred \<Rightarrow> (_,_) pred"
  where "for_all V P \<equiv> fold (\<lambda>x P. PBoo (\<lambda>b. PVal (\<lambda>v. subst\<^sub>\<Gamma> (subst\<^sub>p P x (Const v)) x (Pb b)))) V P"
*)

lemma entail_refl [intro]:
  "P \<turnstile>\<^sub>p P"
  by (auto simp: entail_def)

lemma eval_vars_det:
  "\<forall>v \<in> vars\<^sub>e e. mem v = mem' v \<Longrightarrow> eval mem e = eval mem' e"
  by (induct e, auto)

lemma test_vars_det:
  "\<forall>v \<in> vars\<^sub>p e. m v = m' v \<Longrightarrow> \<forall>v \<in> vars\<^sub>\<Gamma> e. \<Gamma> v = \<Gamma>' v \<Longrightarrow> test m \<Gamma> e = test m' \<Gamma>' e"
proof (induct e)
  case (PCmp c e1 e2)
  hence "\<forall>v\<in>vars\<^sub>e e1. m v = m' v" "\<forall>v\<in>vars\<^sub>e e2. m v = m' v"
    by auto
  hence "eval m e1 = eval m' e1" "eval m e2 = eval m' e2" 
    using eval_vars_det by blast+
  then show ?case by auto
next
  case (PTer e1 e2 v1 v2)
  hence "\<forall>v\<in>vars\<^sub>e e1. m v = m' v" "\<forall>v\<in>vars\<^sub>e e2. m v = m' v"        
    by auto
  hence "eval m e1 = eval m' e1" "eval m e2 = eval m' e2" 
    using eval_vars_det by blast+
  then show ?case using PTer by auto
qed (auto)

lemma map\<^sub>e_vars_det:
  "\<forall>v \<in> vars\<^sub>e e. mem v = mem' (f v) \<Longrightarrow> eval mem e = eval mem' (map\<^sub>e f e)"
  by (induct e, auto)

subsection \<open> subste \<close>

lemma subst\<^sub>e_mem_upd:
  assumes "(\<And>y. y \<noteq> x \<Longrightarrow> mem' y = mem y)"
  assumes "eval mem' e = mem x"
  shows "eval mem' (subst\<^sub>e f x e) = eval mem f"
  using assms by (induct f, auto)

lemma subst\<^sub>e_nop [simp]:
  assumes "x \<notin> vars\<^sub>e f"
  shows "subst\<^sub>e f x v = f"
  using assms by (induct f, auto)

lemma subst\<^sub>e_vars [simp]:
  shows "vars\<^sub>e (subst\<^sub>e f x e) = vars\<^sub>e f - {x} \<union> (if x \<in> vars\<^sub>e f then vars\<^sub>e e else {})"
  by (induct f, auto)

subsection \<open> substp \<close>

lemma subst\<^sub>p_mem_upd:
  assumes "\<And>y. y \<noteq> x \<Longrightarrow> mem' y = mem y"
  assumes "eval mem' e = mem x"
  shows "test mem' \<Gamma> (subst\<^sub>p P x e) = test mem \<Gamma> P"
  using assms
  by (induct P, auto simp: subst\<^sub>e_mem_upd)

lemma subst\<^sub>p_nop [simp]:
  shows "x \<notin> vars\<^sub>p P \<Longrightarrow> subst\<^sub>p P x v = P"
  by (induct P, auto)

lemma subst\<^sub>p_vars\<^sub>p [simp]:
  shows "vars\<^sub>p (subst\<^sub>p P x v) = vars\<^sub>p P - {x} \<union> (if x \<in> vars\<^sub>p P then vars\<^sub>e v else {})"
proof (induct P)

  case (PBoo z)
  hence "vars\<^sub>p (subst\<^sub>p (PBoo z) x v) = (\<Union>y. vars\<^sub>p (z y) - {x} \<union> (if x \<in> vars\<^sub>p (z y) then vars\<^sub>e v else {}))"
    by auto
  also have "... = (\<Union>y. vars\<^sub>p (z y) - {x}) \<union> (\<Union>y. (if x \<in> vars\<^sub>p (z y) then vars\<^sub>e v else {}))"
    by blast
  finally show ?case by simp
qed auto

lemma subst\<^sub>p_vars\<^sub>\<Gamma> [simp]:
  "vars\<^sub>\<Gamma> (subst\<^sub>p P x v) = vars\<^sub>\<Gamma> P"
  by (induct P, auto)

subsection \<open> subst\<Gamma> \<close>

lemma subst\<^sub>\<Gamma>_mem_upd:
  assumes "\<And>y. y \<noteq> x \<Longrightarrow> \<Gamma>' y = \<Gamma> y"
  assumes "test mem \<Gamma>' e = \<Gamma> x"
  shows "test mem \<Gamma>' (subst\<^sub>\<Gamma> P x e) = test mem \<Gamma> P"
  using assms
  by (induct P, auto simp: subst\<^sub>e_mem_upd)

lemma subst\<^sub>\<Gamma>_nop [simp]:
  shows "x \<notin> vars\<^sub>\<Gamma> P \<Longrightarrow> subst\<^sub>\<Gamma> P x v = P"
  by (induct P, auto)

lemma subst\<^sub>\<Gamma>_vars [simp]:
  shows "vars\<^sub>\<Gamma> (subst\<^sub>\<Gamma> P x v) = vars\<^sub>\<Gamma> P - {x} \<union> (if x \<in> vars\<^sub>\<Gamma> P then vars\<^sub>\<Gamma> v else {})"
proof (induct P)

  case (PBoo z)
  hence "vars\<^sub>\<Gamma> (subst\<^sub>\<Gamma> (PBoo z) x v) = (\<Union>y. vars\<^sub>\<Gamma> (z y) - {x} \<union> (if x \<in> vars\<^sub>\<Gamma> (z y) then vars\<^sub>\<Gamma> v else {}))"
    by auto
  also have "... = (\<Union>y. vars\<^sub>\<Gamma> (z y) - {x}) \<union> (\<Union>y. (if x \<in> vars\<^sub>\<Gamma> (z y) then vars\<^sub>\<Gamma> v else {}))"
    by blast
  finally show ?case by simp
qed auto

lemma subst\<^sub>\<Gamma>_vars\<^sub>p [simp]:
  "vars\<^sub>p (subst\<^sub>\<Gamma> P x v) = vars\<^sub>p P \<union> (if x \<in> vars\<^sub>\<Gamma> P then vars\<^sub>p v else {})"
proof (induct P)

  case (PBoo z)
  hence "vars\<^sub>p (subst\<^sub>\<Gamma> (PBoo z) x v) = (\<Union>y. vars\<^sub>p (z y)  \<union> (if x \<in> vars\<^sub>\<Gamma> (z y) then vars\<^sub>p v else {}))"
    by auto
  also have "... = (\<Union>y. vars\<^sub>p (z y)) \<union> (\<Union>y. (if x \<in> vars\<^sub>\<Gamma> (z y) then vars\<^sub>p v else {}))"
    by blast
  finally show ?case by simp
qed auto 

lemma map\<^sub>p_vars_det:
  shows "\<forall>v \<in> vars\<^sub>p P. mem v = mem' (f v) \<Longrightarrow> \<forall>v \<in> vars\<^sub>\<Gamma> P. \<Gamma> v = \<Gamma>' (f v) \<Longrightarrow> test mem \<Gamma> P = test mem' \<Gamma>' (map\<^sub>p f P)"
proof (induct P)
  case (PCmp c e1 e2)
  then show ?case using map\<^sub>e_vars_det 
    by (metis (no_types, lifting) map\<^sub>p.simps(5) subset_iff sup_ge1 sup_ge2 test.simps(6) vars\<^sub>p.simps(6)) 
next
  case (PTer e1 e2 v1 v2)
  then show ?case using map\<^sub>e_vars_det 
    by (metis (no_types, lifting) UnCI map\<^sub>p.simps(9) test.simps(9) vars\<^sub>\<Gamma>.simps(9) vars\<^sub>p.simps(9))
qed auto

lemma map\<^sub>o_vars_det:
  shows "\<forall>v \<in> vars\<^sub>\<Gamma> P. \<Gamma> v = \<Gamma>' (f v) \<Longrightarrow> test mem \<Gamma> P = test mem \<Gamma>' (map\<^sub>o f P)"
  by (induct P) auto

lemma vars_map\<^sub>e [simp]:
  "vars\<^sub>e (map\<^sub>e f e) = f ` vars\<^sub>e e"
  by (induct e) auto

lemma vars_map\<^sub>p [simp]:
  "vars\<^sub>p (map\<^sub>p f e) = f ` vars\<^sub>p e"
  by (induct e) auto

lemma vars_map\<^sub>\<Gamma> [simp]:
  "vars\<^sub>\<Gamma> (map\<^sub>p f e) = f ` vars\<^sub>\<Gamma> e"
  by (induct e) auto

lemma \<Gamma>_ord_refl [intro]:
  shows "\<Gamma> \<sqsupseteq> \<Gamma>"
  by (auto simp: \<Gamma>_ord_def)

lemma entail_trans[trans]:
  "P \<turnstile>\<^sub>p Q \<Longrightarrow> Q \<turnstile>\<^sub>p R \<Longrightarrow> P \<turnstile>\<^sub>p R"
  by (auto simp: entail_def)

lemma entail_conj1[intro]:
  "P \<and>\<^sub>p Q \<turnstile>\<^sub>p Q"
  by (auto simp: entail_def)

lemma entail_conj2[intro]:
  "P \<and>\<^sub>p Q \<turnstile>\<^sub>p P"
  by (auto simp: entail_def)

lemma test_fold:
  "test e \<Gamma> (fold (\<and>\<^sub>p) (map f L) P) = ((\<forall>v \<in> set L. test e \<Gamma> (f v)) \<and> test e \<Gamma> P)"
  by (induct L arbitrary: P, auto)

lemma test_low [simp]:
  "test e \<Gamma> (forVars (V :: 'a list) f) = (\<forall>v \<in> set V. test e \<Gamma> (f v))"
  using test_fold[of e \<Gamma> f] by (auto simp: forVars_def fold_conj_def)

lemma test_subst\<^sub>\<Gamma> [simp]:
  "test m \<Gamma> (subst\<^sub>\<Gamma> P y Q) = test m (\<Gamma> (y := test m \<Gamma> Q)) P"
  by (intro subst\<^sub>\<Gamma>_mem_upd, auto)

lemma test_subst\<^sub>p [simp]:
  "test m \<Gamma> (subst\<^sub>p P y e) = test (m (y := eval m e)) \<Gamma> P"
  by (intro subst\<^sub>p_mem_upd, auto)

lemma wf_subst\<^sub>p[intro]:
  assumes "\<Gamma>_wf Q"
  shows "\<Gamma>_wf (subst\<^sub>p Q x e)"
  using assms by (auto simp: \<Gamma>_wf_def)

lemma vars_const [elim]:
  assumes "vars\<^sub>p Q = {}" "vars\<^sub>\<Gamma> Q = {}"
  obtains (T) "Q =\<^sub>p Pb True" | (F) "Q =\<^sub>p Pb False"
  using assms
proof (cases "\<exists>m \<Gamma>. test m \<Gamma> Q")
  case True
  then obtain m' \<Gamma>' where t: "test m' \<Gamma>' Q" by blast
  have "\<forall>m \<Gamma>. test m \<Gamma> Q"
  proof (intro allI)
    fix m \<Gamma>
    have "test m \<Gamma> Q = test m' \<Gamma>' Q" using test_vars_det[of Q m m' \<Gamma> \<Gamma>'] assms by auto
    thus "test m \<Gamma> Q" using t by auto
  qed
  then show ?thesis using that by (auto simp: equiv_def)
next
  case False
  then show ?thesis using that by (auto simp: equiv_def)
qed

lemma equiv_trans [trans]:
  shows "P1 =\<^sub>p P2 \<Longrightarrow> P2 =\<^sub>p P3 \<Longrightarrow> P1 =\<^sub>p P3"
  unfolding equiv_def by metis

lemma entail_conj [intro]:
  "A \<turnstile>\<^sub>p B \<Longrightarrow> A \<turnstile>\<^sub>p C \<Longrightarrow> A \<turnstile>\<^sub>p B \<and>\<^sub>p C"
  by (auto simp: entail_def)

lemma entail_imp [intro]:
  "A \<and>\<^sub>p B \<turnstile>\<^sub>p C \<Longrightarrow> A \<turnstile>\<^sub>p (B \<longrightarrow>\<^sub>p C)"
  by (auto simp: entail_def)

lemma entail_true [intro]:
  "A \<turnstile>\<^sub>p Pb True"
  by (auto simp: entail_def)

lemma entail_imp_pres[intro]:
  "A \<turnstile>\<^sub>p B \<Longrightarrow> (C \<longrightarrow>\<^sub>p A) \<turnstile>\<^sub>p (C \<longrightarrow>\<^sub>p B)" 
  by (auto simp: entail_def)

primrec foldi :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  fold_Nil:  "foldi n f [] = id" |
  fold_Cons: "foldi n f (x # xs) = foldi (Suc n) f xs \<circ> f n x"

definition index_assert
  where "index_assert x i P \<equiv> foldi 0 (\<lambda>j v Q. Q \<and>\<^sub>p (PCmp (=) i (Const j) \<longrightarrow>\<^sub>p P v)) x (Pb True)"

definition list\<^sub>e
  where "list\<^sub>e x i \<equiv> foldi 0 (\<lambda>j v. Ternary (Const j) i (Var v)) x (Const 0)"

definition list\<^sub>t
  where "list\<^sub>t x i f \<equiv> foldi 0 (\<lambda>j v. PTer (Const j) i (f v)) x (Pb False)"

text \<open>Show that liste is equivalent to evaluating a list read for values\<close>
lemma eval_foldi_nop [simp]:
  assumes "eval m i < k"
  shows "eval m (foldi k (\<lambda>y v. Ternary (Const y) i (Q v)) x q) = eval m q"
  using assms
proof (induct x arbitrary: k q)
  case (Cons a x)
  thus ?case using Cons(1)[of "Suc k" "Ternary (Const k) i (Q a) q"] by simp
qed simp

lemma list\<^sub>e [simp]:
  assumes "eval m i < length x"
  shows "eval m (list\<^sub>e x i) = m (x ! eval m i)"
proof -
  have "\<And>k Q. k \<le> eval m i \<Longrightarrow> eval m i - k < length x \<Longrightarrow> eval m (foldi k (\<lambda>j v. Ternary (Const j) i (Var v)) x Q) = m (x ! (eval m i - k))"
  proof (induct x)
    case (Cons a x)
    then show ?case 
    proof (cases "eval m i = k")
      case False
      have "eval m (foldi (Suc k) (\<lambda>j v. Ternary (Const j) i (Var v)) x (Ternary (Const k) i (Var a) Q)) = m (x ! (eval m i - Suc k))"
        using False Cons(2,3) by (intro Cons(1)) auto
      thus ?thesis using False Cons(2) by simp
    qed auto
  qed simp
  thus ?thesis using assms by (auto simp: list\<^sub>e_def)
qed

text \<open>Show that liste is equivalent to evaluating a list read for types\<close>
lemma test_foldi_nop [simp]:
  assumes "eval m i < k"
  shows "test m \<Gamma> (foldi k (\<lambda>y v. PTer (Const y) i (Q v)) x q) = test m \<Gamma> q"
  using assms
proof (induct x arbitrary: k q)
  case (Cons a x)
  thus ?case using Cons(1)[of "Suc k" "PTer (Const k) i (Q a) q"] by simp
qed simp

lemma list\<^sub>t [simp]:
  assumes "eval m i < length x"
  shows "test m \<Gamma> (list\<^sub>t x i f) = test m \<Gamma> (f (x ! eval m i))"
proof -
  have "\<And>k Q. k \<le> eval m i \<Longrightarrow> eval m i - k < length x \<Longrightarrow> test m \<Gamma> (foldi k (\<lambda>j v. PTer (Const j) i (f v)) x Q) = test m \<Gamma> (f (x ! (eval m i - k)))"
  proof (induct x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
    then show ?case 
    proof (cases "eval m i = k")
      case False
      have "test m \<Gamma> (foldi (Suc k) (\<lambda>j v. PTer (Const j) i (f v)) x (PTer (Const k) i (f a) Q)) = test m \<Gamma> (f  (x ! (eval m i - Suc k)))"
        using False Cons(2,3) by (intro Cons(1)) auto
      thus ?thesis using False Cons(2) by simp
    qed auto
  qed
  thus ?thesis using assms by (auto simp: list\<^sub>t_def)
qed

text \<open>Show that index_assert is equivalent to asserting a property for a particular index\<close>
lemma test_foldi_nop_conj [simp]:
  assumes "eval m i < k"
  shows "test m \<Gamma> (foldi ( k) (\<lambda>j v Q. Q \<and>\<^sub>p (PCmp (=) i (Const j) \<longrightarrow>\<^sub>p P v)) x Q) = test m \<Gamma> Q"
  using assms by (induct x arbitrary: k Q) auto

lemma test_index [simp]:
  assumes "eval m i < length x"
  shows "test m \<Gamma> (index_assert x i P) = test m \<Gamma> (P (x ! eval m i))"
proof -
  have "\<And>k Q. k \<le> eval m i \<Longrightarrow> eval m i - k < length x \<Longrightarrow> test m \<Gamma> (foldi k (\<lambda>j v Q. Q \<and>\<^sub>p (PCmp (=) i (Const j) \<longrightarrow>\<^sub>p P v)) x Q) = test m \<Gamma> (P (x ! (eval m i - k)) \<and>\<^sub>p Q)"
  proof (induct x)
    case (Cons a x)
    then show ?case
    proof (cases "eval m i = k")
      case False
      have "test m \<Gamma> (foldi (Suc k) (\<lambda>j v Q. Q \<and>\<^sub>p (PCmp (=) i (Const j) \<longrightarrow>\<^sub>p P v)) x (Q \<and>\<^sub>p (PCmp (=) i (Const k) \<longrightarrow>\<^sub>p P a))) = 
            test m \<Gamma> (P (x ! (eval m i - (Suc k))) \<and>\<^sub>p (Q \<and>\<^sub>p (PCmp (=) i (Const k) \<longrightarrow>\<^sub>p P a)))"
        using False Cons(2,3) by (intro Cons(1)) auto
      then show ?thesis using False Cons(2) by simp
    qed auto
  qed simp
  thus ?thesis using assms by (auto simp: index_assert_def)
qed

end