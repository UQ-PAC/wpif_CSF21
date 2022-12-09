theory PSC
  imports Main
begin

type_synonym ('a,'b) m = "'a \<Rightarrow> 'b"

datatype ('a,'b) event =
  W "'a" "'b" |
  R "'a" "'b" |
  MF |
  FL "'a" |
  FO "'a"

datatype ('t,'b) pevent =
  PFO "'t" |
  PW "'b"

type_synonym ('t,'b) pbuffer = "('t,'b) pevent list"

type_synonym ('a,'t,'b) pbuffers = "'a \<Rightarrow> ('t,'b) pevent list"

fun last_write :: "('t,'b) pbuffer \<Rightarrow> 'b option"
  where
    "last_write [] = None" |
    "last_write (PW b#xs) = (case last_write xs of Some v \<Rightarrow> Some v | None \<Rightarrow> Some b)" |
    "last_write (a#xs) = last_write xs"

fun get :: "('a,'b) m \<Rightarrow> ('t,'b) pbuffer \<Rightarrow> 'a \<Rightarrow> 'b"
  where
    "get m p a = (case last_write p of Some v \<Rightarrow> v | None \<Rightarrow> m a)"

definition bufapp :: "('a,'t,'b) pbuffers \<Rightarrow> 'a \<Rightarrow> ('t,'b) pevent \<Rightarrow> ('a,'t,'b) pbuffers"
  where "bufapp P x e \<equiv> P(x := (P x)@[e])"

type_synonym ('a,'t,'b) state = "('a,'b) m \<times> ('a,'t,'b) pbuffers"

abbreviation persistent :: "('a,'t,'b) state \<Rightarrow> ('a,'b) m"
  where "persistent m \<equiv> fst m"

abbreviation buffers :: "('a,'t,'b) state \<Rightarrow> ('a,'t,'b) pbuffers"
  where "buffers m \<equiv> snd m"

definition view :: "('a,'b) m \<times> ('a,'t,'b) pbuffers \<Rightarrow> ('a,'b) m"
  where "view m a \<equiv> get (persistent m) (buffers m a) a"

inductive step :: "('a,'t,'b) state \<Rightarrow> 't \<Rightarrow> ('a,'b) event \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -_,_\<rightarrow> \<langle>_\<rangle>")
  where
  wr: "\<langle>(m,P)\<rangle> -t,W x v\<rightarrow> \<langle>(m,bufapp P x (PW v))\<rangle>" |
  rd: "get m (P x) x = v \<Longrightarrow> \<langle>(m,P)\<rangle> -t,R x v\<rightarrow> \<langle>(m,P)\<rangle>" |
  mf: "\<forall>y. PFO t \<notin> set (P y) \<Longrightarrow> \<langle>(m,P)\<rangle> -t,MF\<rightarrow> \<langle>(m,P)\<rangle>" |
  fl: "P x = [] \<Longrightarrow> \<langle>(m,P)\<rangle> -t,FL x\<rightarrow> \<langle>(m,P)\<rangle>" |
  fo: "\<langle>(m,P)\<rangle> -t,FO x\<rightarrow> \<langle>(m,bufapp P x (PFO t))\<rangle>" 

inductive env :: "('a,'t,'b) state \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -e\<rightarrow> \<langle>_\<rangle>")
  where
  pwr: "P x = (PW v)#p \<Longrightarrow> \<langle>(m,P)\<rangle> -e\<rightarrow> \<langle>(m(x := v),P(x := p))\<rangle>" |
  pfo: "P x = (PFO t)#p \<Longrightarrow> \<langle>(m,P)\<rangle> -e\<rightarrow> \<langle>(m,P(x := p))\<rangle>"

inductive trace :: "('a,'t,'b) state \<Rightarrow> ('t \<times> ('a,'b) event) list \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  where
  nil:  "trace a [] a" |
  step: "\<langle>m\<rangle> -thr,a\<rightarrow> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m ((thr,a)#t) m''" |
  env:  "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m t m''"

lemma view_empty:
  assumes "(snd m) x = []"
  shows "view m x = (fst m) x"
  using assms unfolding view_def by auto

lemma view_now:
  assumes "last_write ((snd m) x) = None"
  shows "view m x = (fst m) x"
  using assms unfolding view_def by auto

lemma env_empty:
  assumes "env m m'"
  assumes "(snd m) x = []"
  shows "(snd m') x = []"
  using assms by (induct) auto

lemma env_now:
  assumes "env m m'"
  assumes "last_write ((snd m) x) = None"
  shows "last_write ((snd m') x) = None"
  using assms 
proof (induct)
  case (pwr P x v p m)
  then show ?case
    by (auto split: option.splits)
next
  case (pfo P x t p m)
  then show ?case by auto
qed

lemma env_now_eq:
  assumes "env m m'"
  assumes "last_write ((snd m) x) = None"
  shows "fst m x = fst m' x"
  using assms 
proof (induct)
  case (pwr P x v p m)
  then show ?case
    by (auto split: option.splits)
next
  case (pfo P x t p m)
  then show ?case by auto
qed

lemma env_view:
  assumes "env m m'"
  shows "view m x = view m' x"
  using assms 
proof (induct)
  case (pwr P x v p m)
  then show ?case by (auto simp: view_def split: option.splits)
next
  case (pfo P x t p m)
  then show ?case by (auto simp: view_def split: option.splits)
qed

lemma env_buffers:
  assumes "env m m'"
  shows "set (buffers m' x) \<subseteq> set (buffers m x)"
  using assms 
proof (induct)
  case (pwr P x v p m)
  then show ?case by (auto simp: view_def split: option.splits)
next
  case (pfo P x t p m)
  then show ?case by (auto simp: view_def split: option.splits)
qed


lemma envt_empty:
  assumes "env\<^sup>*\<^sup>* m m'"
  assumes "(snd m) x = []"
  shows "(snd m') x = []"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_empty by fast
qed

lemma envt_now:
  assumes "env\<^sup>*\<^sup>* m m'"
  assumes "last_write ((snd m) x) = None"
  shows "last_write ((snd m') x) = None"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_now by fastforce
qed

lemma envt_now_eq:
  assumes "env\<^sup>*\<^sup>* m m'"
  assumes "last_write ((snd m) x) = None"
  shows "fst m x = fst m' x"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_now_eq envt_now by metis
qed

lemma envt_view:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "view m x = view m' x"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_view by metis
qed

lemma envt_buffers:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "set (buffers m' x) \<subseteq> set (buffers m x)"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_buffers
    by (metis (no_types, lifting) dual_order.trans)
qed

lemma [simp]:
  assumes "x \<noteq> y"
  shows "(bufapp P x e)(y := p) = bufapp (P(y := p)) x e"
  using assms unfolding bufapp_def by auto

lemma [simp]:
  shows "(bufapp P x e)(x := p) = P ( x:= p)"
  unfolding bufapp_def by auto

lemma [simp]:
  assumes "x \<noteq> y"
  shows "bufapp P\<^sub>1 x e y = P\<^sub>1 y"
  using assms unfolding bufapp_def by auto

lemma [simp]:
  shows "bufapp P\<^sub>1 x e x = P\<^sub>1 x @ [e]"
  unfolding bufapp_def by auto

lemma pre_postE:
  assumes "A @ [e] = s # B"
  obtains (empty) "A = []" "B = []" "e = s" |
          (mid) l where "A = s # l" "B = l @ [e]"
  using assms
proof (induct A arbitrary: s B)
  case Nil
  then show ?case by auto
next
  case (Cons a A)
  hence [simp]: "a = s"  "B = A @ [e]" by auto

  show ?case
  proof (cases "A = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    then obtain a' A' where "A = a'#A'" by (cases A, auto)
    hence a: "A @ [e] = a' # (A' @ [e])" by auto

    show ?thesis
    proof (rule Cons(1)[OF _ _ a], goal_cases)
      case 1
      then show ?case by auto
    next
      case (2 l)
      then show ?case using Cons(3) by auto
    qed
  qed
qed

lemma pre_postE':
  assumes "s # B = A @ [e]"
  obtains (empty) "A = []" "B = []" "e = s" |
          (mid) l where "A = s # l" "B = l @ [e]"
  using assms
  using pre_postE by metis


lemma env_bufappE:
  assumes "env (m\<^sub>1, bufapp P\<^sub>1 x e) (m\<^sub>2, P\<^sub>2)"
  obtains (orth) P\<^sub>3 where "env (m\<^sub>1, P\<^sub>1) (m\<^sub>2, P\<^sub>3)" "P\<^sub>2 = bufapp P\<^sub>3 x e" |
          (wr) v where "e = PW v" "m\<^sub>2 = m\<^sub>1 (x := v)" "P\<^sub>2 = P\<^sub>1" "P\<^sub>1 x = []" |
          (fo) v where "e = PFO v" "m\<^sub>2 = m\<^sub>1" "P\<^sub>2 = P\<^sub>1" "P\<^sub>1 x = []"
  using assms
proof cases
  case (pwr y v p)
  then show ?thesis
  proof (cases "x = y")
    case True
    then show ?thesis
    proof (cases "P\<^sub>1 x")
      case Nil
      then show ?thesis using True wr pwr apply auto by force
    next
      case (Cons a list)
      then show ?thesis
        using True orth[of "P\<^sub>1(y := list)"] pwr
        by (auto simp: bufapp_def intro: env.intros)
    qed
  next
    case False
    then show ?thesis using pwr orth[of "P\<^sub>1(y := p)"] by (auto intro: env.intros)     
  qed
next
  case (pfo y t p)
  then show ?thesis
  proof (cases "x = y")
    case True
    then show ?thesis
    proof (cases "P\<^sub>1 x")
      case Nil
      then show ?thesis using True fo pfo apply auto by force
    next
    next
      case (Cons a list)
      then show ?thesis
        using True orth[of "P\<^sub>1(y := list)"] pfo
        by (auto simp: bufapp_def intro: env.intros)
    qed
  next
    case False
    then show ?thesis using pfo orth[of "P\<^sub>1(y := p)"] by (auto intro: env.intros)     
  qed
qed

(* 
  x got written, how?
    
*)

lemma bufappE:
  assumes "env\<^sup>*\<^sup>* (m\<^sub>1, bufapp P\<^sub>1 x e) (m\<^sub>2, P\<^sub>2)"
  obtains (orth) P\<^sub>3 where "env\<^sup>*\<^sup>* (m\<^sub>1, P\<^sub>1) (m\<^sub>2,P\<^sub>3)" "P\<^sub>2 = bufapp P\<^sub>3 x e" |
          (wr) m\<^sub>3 v where "e = PW v" "env\<^sup>*\<^sup>* (m\<^sub>1, P\<^sub>1) (m\<^sub>3, P\<^sub>2)" "m\<^sub>2 = m\<^sub>3 (x := v)" "P\<^sub>2 x = []" |
          (fo) v where "e = PFO v" "env\<^sup>*\<^sup>* (m\<^sub>1, P\<^sub>1) (m\<^sub>2, P\<^sub>2)" "P\<^sub>2 x = []" 
  using assms
proof (induct "(m\<^sub>1,bufapp P\<^sub>1 x e)" "(m\<^sub>2,P\<^sub>2)" arbitrary: m\<^sub>2 P\<^sub>2)
  case rtrancl_refl
  then show ?case by blast
next
  case (rtrancl_into_rtrancl b)
  obtain m' P' where b: "b = (m',P')" by (cases b) 
  then show ?case
  proof (rule rtrancl_into_rtrancl(2), goal_cases)
    case (1 P\<^sub>3)
    hence "env (m', bufapp P\<^sub>3 x e) (m\<^sub>2, P\<^sub>2)" using rtrancl_into_rtrancl(3) unfolding b by auto
    then show ?case
    proof (cases rule: env_bufappE)
      case (orth P\<^sub>4)
      then show ?thesis using 1 rtrancl_into_rtrancl(4)
        by (metis rtranclp.rtrancl_into_rtrancl) 
    next
      case (wr v)
      then show ?thesis using 1 rtrancl_into_rtrancl(5) by blast
    next
      case (fo v)
      then show ?thesis using 1  rtrancl_into_rtrancl(6) by blast
    qed
  next
    case (2 v m\<^sub>3)
    obtain m\<^sub>4 where "\<langle>(m\<^sub>3, P')\<rangle> -e\<rightarrow> \<langle>(m\<^sub>4, P\<^sub>2)\<rangle>" "m\<^sub>2 = m\<^sub>4(x := v)" "P\<^sub>2 x = []"
      using rtrancl_into_rtrancl(3) 2(4) unfolding b 2(3)
    proof (cases rule: env.cases)
      case (pwr y v' p)
      then show ?thesis using 2(4)  
        apply (cases "x = y")
        apply (auto intro: that)
        using that[of "m\<^sub>3( y := v')"]
        using env.intros(1)
        by fastforce
    next
      case (pfo y t p)
      then show ?thesis using 2(4)
        apply (cases "x = y")
        apply (auto intro: that)
        using that[of "m\<^sub>3"]
        using env.intros(2)
        by fastforce
    qed

    then show ?case using 2 rtrancl_into_rtrancl(3) rtrancl_into_rtrancl(5)[of v m\<^sub>4] unfolding b 
      by (meson rtranclp.rtrancl_into_rtrancl)
  next
    case (3 v)
    then show ?case using 3 rtrancl_into_rtrancl(3) rtrancl_into_rtrancl(6)[of ] unfolding b
      by (metis env_empty rtranclp.rtrancl_into_rtrancl snd_conv)
  qed
qed


lemma last_write_app [simp]:
  "last_write (a @ [PW v]) = Some v"
proof (induct a)
  case Nil
  then show ?case by auto
next
  case (Cons a1 a2)
  then show ?case by (cases a1; auto)
qed

lemma view_bufapp [simp]:
  shows "view (a,bufapp b x (PW v)) = (view (a, b))(x := v)"
  unfolding view_def bufapp_def by auto


lemma view_empty_buf_upd [simp]:
  assumes "b x = []"
  shows "(view (a,b))(x := v) = (view (a(x := v), b))"
  using assms unfolding view_def fun_eq_iff by (auto  split: option.splits)

section \<open>Predicate Language\<close>

text \<open>Predicate abstraction to simplify specification\<close>
type_synonym ('a,'b) pred = "(('a,'b) m \<times> ('a,'b) m \<times> ('a,'b) m) set"

definition contains :: "'a list \<Rightarrow> ('a) \<Rightarrow> bool"
  where "contains l f \<equiv> f \<in> set l"

fun isPFO
  where "isPFO (PFO _) = True" | "isPFO _ = False"

fun foslice :: "'t \<Rightarrow> ('t,'b) pevent list \<Rightarrow> 'b option"
  where 
    "foslice t [] = None" |
    "foslice t (PFO _#xs) = (if \<not>(contains xs (PFO t)) then None else foslice t xs)" |
    "foslice t (PW x#PFO t'#xs) = (if t' = t \<and> \<not>(contains xs (PFO t)) then Some x else foslice t (PW x#xs) )" |
    "foslice t (PW x#xs) = foslice t xs"

definition foget :: "'t \<Rightarrow> ('a,'b) m \<times> ('a,'t,'b) pbuffers \<Rightarrow> ('a,'b) m"
  where "foget t m a \<equiv> (case foslice t (buffers m a) of Some v \<Rightarrow> v | None \<Rightarrow> persistent m a)"

definition sat :: "'t \<Rightarrow> ('a,'b) pred \<Rightarrow> ('a,'b) m \<times> ('a,'t,'b) pbuffers \<Rightarrow> bool"
  where "sat t Q m \<equiv> \<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> (view m', persistent m', foget t m') \<in> Q"

fun wp :: "('a,'b) event \<Rightarrow> ('a,'b) pred \<Rightarrow> ('a,'b) pred"
  where
    "wp (W x v) Q = {(m,p,f). (m(x:=v),p,f) \<in> Q \<and> (m(x:=v),p(x:=v),f(x:=v)) \<in> Q }" |
    "wp (R x v) Q = {(m,p,f). m x = v \<longrightarrow> (m,p,f) \<in> Q}" |
    "wp (FL x) Q = {(m,p,f). m x = p x \<and> m x = f x \<longrightarrow> (m,p,f) \<in> Q}" |
    "wp MF Q = {(m,p,f). p = f \<longrightarrow> (m,p,f) \<in> Q}" |
    "wp (FO x) Q = {(m,p,f). (m,p,f(x := m x)) \<in> Q}"

fun wpl :: "'t \<Rightarrow> ('t \<times> ('a,'b) event) list \<Rightarrow> ('a,'b) pred \<Rightarrow> ('a,'b) pred"
  where
    "wpl t [] A = A" |
    "wpl t ((t',x)#xs) A = (if t = t' then wp x (wpl t xs A) else wpl t xs A)"

lemma foget_empty:
  "buffers m x = [] \<Longrightarrow> foget t m x = persistent m x"
  unfolding foget_def by auto

lemma [simp]:
  "foslice t (p @ [PW v]) = foslice t p"
  by (induct t "p" rule: foslice.induct) (auto simp: contains_def)

lemma foget_bufapp [simp]:
  shows "foget t (a,bufapp b x (PW v)) = (foget t (a, b))"
  unfolding foget_def bufapp_def fun_eq_iff by (auto split: option.splits)

lemma foget_empty_buf_upd [simp]:
  assumes "b x = []"
  shows "(foget t (a,b))(x := v) = (foget t (a(x := v), b))"
  using assms unfolding foget_def fun_eq_iff by (auto  split: option.splits)

lemma [simp]:
  "last_write (p @ [PFO t]) = last_write p"
proof (induct p)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case by (cases a) auto
qed

lemma [simp]:
  "view (a, bufapp b x (PFO t)) = view (a, b)"
  unfolding view_def bufapp_def fun_eq_iff by (auto split: option.splits)

lemma [simp]:
  "foslice t (l @ [PFO t]) = last_write l"
proof (induct t "l@[PFO t]" arbitrary: l rule: foslice.induct )
  case (1 t)
  then show ?case by auto
next
  case (2 t uu xs)
  then show ?case by (auto simp: contains_def elim!: pre_postE' split: option.splits)
next
  case (3 t x t' xs)
  then show ?case by (auto simp: contains_def elim!: pre_postE' split: option.splits)
next
  case ("4_1" t x)
  then show ?case by auto
next
  case ("4_2" t x vb va)
  then show ?case by (auto elim!: pre_postE' split: option.splits)
qed

lemma [simp]:
  "foget t (a, bufapp b x (PFO t)) x = view (a, b) x"
  unfolding view_def foget_def bufapp_def by (auto split: option.splits)

lemma [simp]:
  "foget t (a, bufapp b x (PFO t)) = (foget t (a, b)) (x := view (a,b) x)"
  unfolding view_def foget_def bufapp_def by (auto split: option.splits)

lemma foslice_npfo:
  assumes "PFO t \<notin> set l" 
  shows "foslice t l = None"
  using assms by (induct t l rule: foslice.induct) auto

lemma foget_npfo [simp]:
  assumes "\<forall>y. PFO t \<notin> set (buffers m y)" 
  shows "foget t m = fst m"
  using assms unfolding foget_def fun_eq_iff 
  apply (auto split: option.splits)
  by (simp add: foslice_npfo)

lemma wp_sound:
  assumes "\<langle>m\<rangle> -t,a\<rightarrow> \<langle>m'\<rangle>" "sat t (wp a Q) m"
  shows "sat t Q m'"
  using assms
proof (induct)
  case (wr m P t x v)
  then show ?case
    apply auto
    unfolding sat_def
    apply auto
    apply (elim bufappE)
      apply (auto)
    by fastforce
next
  case (rd m P x v t)
  hence "view (m,P) x = v" by (auto simp: view_def)
  then show ?case using rd(2) by (auto simp add: sat_def envt_view)
next
  case (mf t P m)
  then show ?case
    unfolding sat_def wp.simps
    apply auto
    using foget_npfo 
    apply (subgoal_tac " \<forall>y. PFO t \<notin> set (buffers (a,b) y)")
     apply (subgoal_tac "foget t  (a,b) = persistent  (a,b)")
      apply auto[2]
    using envt_buffers
    by fastforce
next
  case (fl P x m t)
  then show ?case
    unfolding sat_def wp.simps
    using view_empty envt_empty foget_empty
    by (smt (verit, ccfv_SIG) case_prodD mem_Collect_eq snd_eqD)
next
  case (fo m P t x)
  then show ?case
    unfolding sat_def 
    apply auto
    apply (elim bufappE)
      apply auto
     apply (metis (no_types, opaque_lifting) foget_empty fun_upd_triv snd_conv view_empty)
    done    
qed

lemma sat_env_stable:
  assumes "sat t Q m" "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  shows "sat t Q m'"
  using assms unfolding sat_def
  by (meson converse_rtranclp_into_rtranclp)
  
lemma wpl_sound:
  assumes "trace m t m'" "sat thr (wpl t Q) m"
  shows "sat thr Q m'"
  using assms
proof (induct arbitrary: Q)
  case (nil a)
  then show ?case by auto
next
  case (step m u a m' t m'')
  then show ?case using wp_sound by fastforce
next
  case (env m m' t m'')
  then show ?case using sat_env_stable by fastforce
qed

end