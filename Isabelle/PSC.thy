theory PSC
  imports Main
begin

type_synonym ('a,'b) m = "'a \<Rightarrow> 'b"

section \<open>List Utilities\<close>

lemma post_preE:
  assumes "A @ [e] = s # B"
  obtains (empty) "A = []" "B = []" "e = s" |
          (mid) l where "A = s # l" "B = l @ [e]"
  using assms by (cases A) auto

lemma pre_postE:
  assumes "s # B = A @ [e]"
  obtains (empty) "A = []" "B = []" "e = s" |
          (mid) l where "A = s # l" "B = l @ [e]"
  using assms by (cases A) auto

subsection \<open>lastf\<close>

fun lastf
  where 
    "lastf f [] = None" |
    "lastf f (e#l) = (case lastf f l of Some v \<Rightarrow> Some v | None \<Rightarrow> (if f e then Some e else None))"

lemma lastf_none [simp]:
  assumes "\<forall>x \<in> set l. \<not> f x"
  shows "lastf f l = None"
  using assms by (induct l) (auto)

lemma lastf_append [simp]:
  assumes "f a"
  shows "lastf f (p @ [a]) = Some a"
  using assms by (induct p) (auto)

lemma lastf_concat [simp]:
  "lastf f (p@l) = (case lastf f l of Some v \<Rightarrow> Some v  | None \<Rightarrow> lastf f p)"
  by (induct p) (auto split: option.splits)

lemma lastf_some [intro]:
  "lastf f l = Some a \<Longrightarrow> f a"
  by (induct l) (auto split: option.splits if_splits)

section \<open>Events\<close>

datatype ('a,'b) event =
  W "'a" "'b" |
  R "'a" "'b" |
  MF |
  FL "'a" |
  FO "'a" |
  RMW "'a" "'b" "'b" |
  RMF "'a" "'b"

section \<open>Persistent Buffer Events\<close>

datatype ('t,'b) pevent =
  PFO "'t" |
  PW "'b"

fun isPW :: "('t,'b) pevent \<Rightarrow> bool"
  where 
    "isPW (PW _) = True" |
    "isPW _ = False"

fun isPFO :: "('t,'b) pevent \<Rightarrow> bool"
  where 
    "isPFO (PFO _) = True" | 
    "isPFO _ = False"

section \<open>State\<close>

record ('a,'t,'b) state =
  persistent :: "('a,'b) m"
  buffers :: "'a \<Rightarrow> ('t,'b) pevent list"

definition get :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> 'b"
  where "get m a \<equiv> (case lastf isPW (buffers m a) of Some (PW v) \<Rightarrow> v | _ \<Rightarrow> persistent m a)"

abbreviation persistent_set :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>p= _\<rbrakk>" [900,0,0] 900)
  where "persistent_set m x v \<equiv> persistent_update (\<lambda>b. b(x := v)) m"

abbreviation buffer_set :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> ('t,'b) pevent list \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>b= _\<rbrakk>" [900,0,0] 900)
  where "buffer_set m x p \<equiv> buffers_update (\<lambda>b. b(x := p)) m"

abbreviation buffer_app :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> ('t,'b) pevent \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>@= _\<rbrakk>" [900,0,0] 900)
  where "buffer_app m x e \<equiv> m\<lbrakk>x \<^sub>b= (buffers m x)@[e] \<rbrakk>"

lemma get_no_pw[simp]:
  assumes "\<forall>e \<in> set (buffers m x). \<not> isPW e"
  shows "get m x = persistent m x"
  using assms by (auto simp: get_def fun_eq_iff split: option.splits pevent.splits)

lemma get_no_pw'[simp]:
  assumes "\<forall>e \<in> set (buffers m x). \<not> isPW e"
  shows "get (m\<lbrakk>x \<^sub>p= v\<rbrakk>) = (get m)(x := v)"
  using assms by (auto simp: get_def fun_eq_iff split: option.splits pevent.splits)

lemma [simp]:
  shows "(lastf isPW p = Some (PFO v)) = False"
  by (rule iffI,drule lastf_some) auto

lemma get_simps [simp]:
  "x \<noteq> y \<Longrightarrow> get (m\<lbrakk>y \<^sub>b= p\<rbrakk>) x = get m x"
  "x \<noteq> y \<Longrightarrow> get (m\<lbrakk>y \<^sub>p= a\<rbrakk>) x = get m x"

  "get (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) = (get m)(x := v)"
  "get (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = get m"

  "(get (m\<lbrakk>x \<^sub>p= v\<rbrakk>))(x := v) = (get m)(x := v)"
  "get (m\<lbrakk>x \<^sub>b= []\<rbrakk>) = (get m)(x := persistent m x)"
  by (auto simp: get_def fun_eq_iff split: option.splits pevent.splits)

lemma [simp]:
  "(\<lambda>b. b(y := c)) \<circ> (\<lambda>b. b(x := g b)) = (\<lambda>b. b(x := g b, y := c))"
  by auto

lemma redundant_buffer_set [simp]:
  assumes "buffers m y = p"
  shows "m\<lbrakk>y \<^sub>b= p\<rbrakk> = m"
  using assms by auto

lemma pers_buf_twist:
  "buffers_update g (persistent_update f m) = persistent_update f (buffers_update g m)"
  by (metis surjective update_convs(1,2))

subsection \<open>remainder\<close>

fun rem :: "'t \<Rightarrow> ('t,'b) pevent list \<Rightarrow> ('t,'b) pevent list"
  where 
    "rem t [] = []" |
    "rem t (a#xs) = (if PFO t \<in> set xs then rem t xs else if a = PFO t then xs else a#xs)"

lemma [simp]:
  "PFO s \<notin> set (rem s l)"
  by (induct l) auto

section \<open>Semantics\<close>

inductive step :: "('a,'t,'b) state \<Rightarrow> 't \<Rightarrow> ('a,'b) event \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -_,_\<rightarrow> \<langle>_\<rangle>")
  where
  wr: "\<langle>m\<rangle> -t,W x v\<rightarrow> \<langle>m\<lbrakk>x \<^sub>@= PW v\<rbrakk>\<rangle>" |
  rd: "get m x = v \<Longrightarrow> \<langle>m\<rangle> -t,R x v\<rightarrow> \<langle>m\<rangle>" |
  mf: "\<forall>y. PFO t \<notin> set (buffers m y) \<Longrightarrow> \<langle>m\<rangle> -t,MF\<rightarrow> \<langle>m\<rangle>" |
  fl: "buffers m x = [] \<Longrightarrow> \<langle>m\<rangle> -t,FL x\<rightarrow> \<langle>m\<rangle>" |
  fo: "\<langle>m\<rangle> -t,FO x\<rightarrow> \<langle>m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>\<rangle>" |
  rmw: "get m x = v\<^sub>R \<Longrightarrow> \<forall>y. PFO t \<notin> set (buffers m y) \<Longrightarrow> \<langle>m\<rangle> -t,RMW x v\<^sub>R v\<^sub>W\<rightarrow> \<langle>m\<lbrakk>x \<^sub>@= PW v\<^sub>W\<rbrakk>\<rangle>" |
  rmf: "get m x = v\<^sub>R \<Longrightarrow> \<forall>y. PFO t \<notin> set (buffers m y) \<Longrightarrow> \<langle>m\<rangle> -t,RMF x v\<^sub>R\<rightarrow> \<langle>m\<rangle>"

definition eval :: "'t \<times> ('a,'b) event \<Rightarrow> ('a,'t,'b) state rel"
  where "eval a = {(m,m'). \<langle>m\<rangle> -fst a,snd a\<rightarrow> \<langle>m'\<rangle>}"

lemma step_det:
  assumes "\<langle>m\<rangle> -t,\<alpha>\<rightarrow> \<langle>m'\<rangle>"
  assumes "\<langle>m\<rangle> -t,\<alpha>\<rightarrow> \<langle>m''\<rangle>"
  shows "m' = m''"
  using assms by (induct) (auto elim: step.cases)

lemma eval_det:
  assumes "(m,m') \<in> eval \<alpha>"
  assumes "(m,m'') \<in> eval \<alpha>"
  shows "m' = m''"
  using assms by (auto simp: eval_def intro: step_det)

section \<open>Persistent Environment Steps\<close>

inductive env :: "('a,'t,'b) state \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -e\<rightarrow> \<langle>_\<rangle>")
  where
  pwr: "buffers m x = (PW v)#p \<Longrightarrow> \<langle>m\<rangle> -e\<rightarrow> \<langle>m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>\<rangle>" |
  pfo: "buffers m x = (PFO t)#p \<Longrightarrow> \<langle>m\<rangle> -e\<rightarrow> \<langle>m\<lbrakk>x \<^sub>b= p\<rbrakk>\<rangle>"

lemma pwrI [intro]:
  assumes "buffers m x = (PW v)#p"
  assumes "m' = m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>"
  shows "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  using env.intros(1) assms by metis

lemma pfoI [intro]:
  assumes "buffers m x = (PFO t)#p"
  assumes "m' = m\<lbrakk>x \<^sub>b= p\<rbrakk>"
  shows "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  using env.intros(2) assms by metis

inductive trace :: "('a,'t,'b) state \<Rightarrow> ('t \<times> ('a,'b) event) list \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  where
  nil:  "trace a [] a" |
  step: "\<langle>m\<rangle> -thr,a\<rightarrow> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m ((thr,a)#t) m''" |
  env:  "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m t m''"

subsection \<open>Persistent Properties\<close>

lemma env_get [simp]:
  assumes "env m m'"
  shows "get m x = get m' x"
  using assms by cases (auto simp: get_def split: option.splits pevent.splits)

lemma envt_get [simp]:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "get m x = get m' x"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_get by metis
qed

lemma env_pers_setE:
  assumes "env (m\<^sub>1\<lbrakk>x \<^sub>p= v\<rbrakk>) m\<^sub>2"
  obtains (orth) m\<^sub>3 where "env m\<^sub>1 m\<^sub>3" "m\<^sub>2 = m\<^sub>3\<lbrakk>x \<^sub>p= v\<rbrakk>" |
          (wr) v' l where "m\<^sub>2 = m\<^sub>1\<lbrakk>x \<^sub>p= v'\<rbrakk>\<lbrakk>x \<^sub>b= l\<rbrakk>" "buffers m\<^sub>1 x = (PW v')#l"
  using assms
proof cases
  case (pwr y v' p)
  have e: "\<langle>m\<^sub>1\<rangle> -e\<rightarrow> \<langle>m\<^sub>1\<lbrakk>y \<^sub>p= v'\<rbrakk>\<lbrakk>y \<^sub>b= p\<rbrakk>\<rangle>" using pwr by (auto intro: env.pwr)
  then show ?thesis
  proof (cases "x = y")
    case True
    then show ?thesis using pwr wr by auto
  next
    case False
    then show ?thesis using pwr orth[OF e] by (simp add: fun_upd_twist)
  qed
next
  case (pfo y t p)
  then show ?thesis using orth[of "m\<^sub>1\<lbrakk>y \<^sub>b= p\<rbrakk>"] by (auto intro: env.pfo)
qed

subsection \<open>Buffer Properties\<close>

lemma env_buffers:
  assumes "env m m'"
  obtains pre where "buffers m x = pre @ buffers m' x"
  using assms 
proof cases
  case (pwr y v p)
  then show ?thesis using that by (cases "x = y") auto
next
  case (pfo y t p)
  then show ?thesis using that by (cases "x = y") auto
qed

lemma env_buffer_empty:
  assumes "env m m'"
  assumes "buffers m x = []"
  shows "buffers m' x = []"
  using assms env_buffers
  by (metis Nil_is_append_conv)

lemma envt_buffers:
  assumes "env\<^sup>*\<^sup>* m m'"
  obtains pre where "buffers m x = pre @ buffers m' x"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_buffers by (metis append.assoc)
qed

lemma envt_buffer_empty:
  assumes "env\<^sup>*\<^sup>* m m'"
  assumes "buffers m x = []"
  shows "buffers m' x = []"
  using assms by (auto elim!: envt_buffers[where x = x])

lemma envt_buffer_subset:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "set (buffers m' x) \<subseteq> set (buffers m x)"
  using assms by (auto elim!: envt_buffers[where x = x])

subsubsection \<open>Introduction\<close>

lemma env_buffer_appI:
  assumes "env m m'"
  shows "env (m\<lbrakk>x \<^sub>@= b\<rbrakk>) (m'\<lbrakk>x \<^sub>@= b\<rbrakk>)"
  using assms
proof cases
  case (pwr y v p)
  thus ?thesis by (cases "x = y") (auto intro!: pwrI[where x=y] simp add: fun_upd_twist)
next
  case (pfo y t p)
  thus ?thesis by (cases "x = y") (auto intro!: pfoI[where x=y] simp add: fun_upd_twist)
qed

lemma envt_buffer_appI:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "env\<^sup>*\<^sup>* (m\<lbrakk>x \<^sub>@= b\<rbrakk>) (m'\<lbrakk>x \<^sub>@= b\<rbrakk>)"
  using assms
proof induct
  case base
  thus ?case by auto
next
  case (step y z)
  thus ?case by (blast intro: env_buffer_appI rtranclp.rtrancl_into_rtrancl)
qed

lemma envt_full_evalI:
  shows "env\<^sup>*\<^sup>* (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) (m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= []\<rbrakk>)"
proof (induct "buffers m x" arbitrary: m)
  case Nil
  hence "env (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) (m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= []\<rbrakk>)" by auto
  then show ?case by blast
next
  case (Cons pe p)
  then show ?case  
  proof (cases pe)
    case (PFO t)
    hence "env (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) (m\<lbrakk>x \<^sub>b= p @ [PW v]\<rbrakk>)" using Cons(2) by (intro pfoI[where t=t]) auto
    then show ?thesis using Cons(1)[of "m\<lbrakk>x \<^sub>b= p\<rbrakk>"] by auto
  next
    case (PW v')
    hence "env (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) (m\<lbrakk>x \<^sub>p= v'\<rbrakk>\<lbrakk>x \<^sub>b= p @ [PW v]\<rbrakk>)" using Cons(2) by (intro pwrI) auto
    then show ?thesis using Cons(1)[of "m\<lbrakk>x \<^sub>p= v'\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>"] by auto
  qed
qed

lemma envt_buffer_app_evalI:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "env\<^sup>*\<^sup>* (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) (m'\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= []\<rbrakk>)"
  using envt_buffer_appI[OF assms] envt_full_evalI by (metis (mono_tags) rtranclp_trans)

subsubsection \<open>Elimination\<close>

lemma env_buffer_appE:
  assumes "env (m\<^sub>1\<lbrakk>x \<^sub>@= e\<rbrakk>) m\<^sub>2"
  obtains (orth) m\<^sub>3 where "env m\<^sub>1 m\<^sub>3" "m\<^sub>2 = m\<^sub>3\<lbrakk>x \<^sub>@= e\<rbrakk>" |
          (wr) v where "e = PW v" "m\<^sub>2 = m\<^sub>1\<lbrakk>x \<^sub>p= v\<rbrakk>" "buffers m\<^sub>1 x = []" |
          (fo) v where "e = PFO v" "m\<^sub>2 = m\<^sub>1" "buffers m\<^sub>1 x = []"
  using assms
proof cases
  case (pwr y v p)
  then show ?thesis
  proof (cases "x = y")
    case True
    hence "buffers m\<^sub>1 y @ [e] = PW v # p" using pwr by auto
    then show ?thesis 
    proof (cases rule: post_preE)
      case empty
      then show ?thesis using wr pwr True by auto
    next
      case (mid l)
      then show ?thesis using orth[of "m\<^sub>1\<lbrakk>y \<^sub>p= v\<rbrakk>\<lbrakk>y \<^sub>b= l\<rbrakk>"] pwr True by auto
    qed
  next
    case False
    then show ?thesis using pwr
      by (intro orth[of "m\<^sub>1\<lbrakk>y \<^sub>p= v\<rbrakk>\<lbrakk>y \<^sub>b= p\<rbrakk>"] pwrI) (auto simp: fun_upd_twist)
  qed
next
  case (pfo y t p)
  then show ?thesis
  proof (cases "x = y")
    case True
    hence "buffers m\<^sub>1 y @ [e] = PFO t # p" using pfo by auto
    then show ?thesis 
    proof (cases rule: post_preE)
      case empty
      then show ?thesis using fo pfo True by auto
    next
      case (mid l)
      then show ?thesis using orth[of "m\<^sub>1\<lbrakk>y \<^sub>b= l\<rbrakk>"] pfo True by auto
    qed
  next
    case False
    then show ?thesis using pfo
      by (intro orth[of "m\<^sub>1\<lbrakk>y \<^sub>b= p\<rbrakk>"] pfoI) (auto simp: fun_upd_twist)
  qed
qed

lemma envt_buffer_appE:
  assumes "env\<^sup>*\<^sup>* (m\<^sub>1\<lbrakk>x \<^sub>@= e\<rbrakk>) m\<^sub>2"
  obtains (orth) m\<^sub>3 where "env\<^sup>*\<^sup>* m\<^sub>1 m\<^sub>3" "m\<^sub>2 = m\<^sub>3\<lbrakk>x \<^sub>@= e\<rbrakk>" |
          (pwr) m\<^sub>3 v where "e = PW v" "env\<^sup>*\<^sup>* m\<^sub>1 m\<^sub>3" "m\<^sub>2 = m\<^sub>3\<lbrakk>x \<^sub>p= v\<rbrakk>" "buffers m\<^sub>2 x = []" |
          (pfo) v where "e = PFO v" "env\<^sup>*\<^sup>* m\<^sub>1 m\<^sub>2" "buffers m\<^sub>2 x = []" 
  using assms
proof (induct "m\<^sub>1\<lbrakk>x \<^sub>@= e\<rbrakk>" m\<^sub>2)
  case rtrancl_refl
  then show ?case by blast
next
  case (rtrancl_into_rtrancl m\<^sub>3 m\<^sub>4)
  show ?case
  proof (rule rtrancl_into_rtrancl(2), goal_cases)
    case (1 m\<^sub>5)
    hence "env (m\<^sub>5\<lbrakk>x \<^sub>@= e\<rbrakk>) m\<^sub>4" using rtrancl_into_rtrancl(3) by simp
    then show ?case
    proof (cases rule: env_buffer_appE)
      case (orth m\<^sub>3')
      then show ?thesis using rtrancl_into_rtrancl(4) 1(1) 
        by (blast intro: rtranclp.rtrancl_into_rtrancl)
    next
      case (wr v)
      then show ?thesis using 1 rtrancl_into_rtrancl(5) by simp
    next
      case (fo v)
      then show ?thesis using 1 rtrancl_into_rtrancl(6) by simp
    qed
  next
    case (2 v m\<^sub>5)
    show ?case using rtrancl_into_rtrancl(3) unfolding 2
    proof (cases rule: env_pers_setE)
      case (orth m\<^sub>6)
      then show ?thesis using 2 rtrancl_into_rtrancl(3,5)
        by (blast intro: env_buffer_empty rtranclp.rtrancl_into_rtrancl)
    next
      case (wr v' l)
      then show ?thesis using 2 by auto
    qed
  next
    case (3 v)
    then show ?case using rtrancl_into_rtrancl(3,6) 
      by (metis env_buffer_empty rtranclp.rtrancl_into_rtrancl)
  qed
qed

lemma simple:
  "m\<lbrakk>x \<^sub>b= p\<rbrakk>\<lbrakk>x \<^sub>b= q\<rbrakk>\<lbrakk>x \<^sub>p= f\<rbrakk> = m\<lbrakk>x \<^sub>b= q\<rbrakk>\<lbrakk>x \<^sub>p= f\<rbrakk>"
  by (auto)

lemma simple2:
  "(m\<lbrakk>x \<^sub>p= a\<rbrakk>\<lbrakk>y \<^sub>b= b\<rbrakk>\<lbrakk>x \<^sub>p= c\<rbrakk>) = (m\<lbrakk>y \<^sub>b= b\<rbrakk>\<lbrakk>x \<^sub>p= c\<rbrakk>)"
  by auto

lemma flush_x:
  shows "env\<^sup>*\<^sup>* m (m\<lbrakk>x \<^sub>b= []\<rbrakk>\<lbrakk>x \<^sub>p= get m x\<rbrakk>)"
proof (induct "buffers m x" arbitrary: m)
  case Nil
  hence "m\<lbrakk>x \<^sub>b= []\<rbrakk>\<lbrakk>x \<^sub>p= get m x\<rbrakk> = m" by auto
  then show ?case by (metis rtranclp.rtrancl_refl)
next
  case (Cons a p)
  hence t: "buffers m x = a # p" by auto

  then show ?case
  proof (cases a)
    case (PFO x1)
    hence "env\<^sup>*\<^sup>* (m\<lbrakk>x \<^sub>b= p\<rbrakk>) (m\<lbrakk>x \<^sub>b= p\<rbrakk>\<lbrakk>x \<^sub>b= []\<rbrakk>\<lbrakk>x \<^sub>p= get (m\<lbrakk>x \<^sub>b= p\<rbrakk>) x\<rbrakk>)"
      using Cons 
      by (metis (mono_tags, lifting) fun_upd_same select_convs(2) surjective update_convs(1,2))
    moreover have e: "\<langle>m\<rangle> -e\<rightarrow> \<langle>m\<lbrakk>x \<^sub>b= p\<rbrakk>\<rangle>" using PFO env.pfo t by blast
    ultimately show ?thesis  unfolding simple 
      by (smt (verit, best) converse_rtranclp_into_rtranclp env_get surjective update_convs(1))

  next
    case (PW v)
    let ?m="m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>"
    have "env\<^sup>*\<^sup>* ?m (?m\<lbrakk>x \<^sub>b= []\<rbrakk>\<lbrakk>x \<^sub>p= get ?m x\<rbrakk>)"
      using Cons PW
      by (smt (verit, best) fun_upd_same select_convs(2) surjective update_convs(1,2))
    moreover have e: "\<langle>m\<rangle> -e\<rightarrow> \<langle>m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>\<rangle>" using PW env.pwr t by blast
    moreover have "get (m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>) x = get m x"
      unfolding get_def t PW 
      by (auto split: option.splits pevent.splits)
    ultimately show ?thesis unfolding simple simple2 
      by (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp surjective update_convs(1))
  qed
qed



section \<open>Predicate Language\<close>

type_synonym ('a,'t) ord = "'a \<Rightarrow> 't \<Rightarrow> bool"

text \<open>Predicate abstraction to simplify specification, consisting of: 
      (volatile memory, persistent memory, memory after an mfence)\<close>
type_synonym ('a,'b,'t) pred = "(('a,'b) m \<times> ('a,'b) m \<times> ('a,'b) m) set"
type_synonym ('a,'b,'t) prel = "(('a,'b) m \<times> ('a,'b) m \<times> ('a,'b) m) rel"

subsection \<open>pre_fo\<close>

text \<open>Find a write before a PFO event in a buffer, returning None if there aren't any\<close>
fun pre_fo :: "'t \<Rightarrow> ('t,'b) pevent list \<Rightarrow> 'b option"
  where 
    "pre_fo t [] = None" |
    "pre_fo t (PFO _#xs) = (if PFO t \<in> set xs then pre_fo t xs else None)" |
    "pre_fo t (PW x#PFO s#xs) = (if s = t \<and> PFO t \<notin> set xs then Some x else pre_fo t (PW x#xs))" |
    "pre_fo t (PW x#xs) = pre_fo t xs"

lemma pre_fo_no_pfo [simp]:
  assumes "PFO t \<notin> set l" 
  shows "pre_fo t l = None"
  using assms by (induct l rule: pre_fo.induct) auto

lemma pre_fo_no_pw [simp]:
  assumes "\<forall>e \<in> set l. \<not> isPW e"
  shows "pre_fo t l = None"
  using assms by (induct l rule: pre_fo.induct) auto

lemma pre_fo_pfo [simp]:
  "pre_fo t (l @ [PFO t]) = (case lastf isPW l of Some (PW v) \<Rightarrow> Some v | _ \<Rightarrow> None)"
  by (induct "l@[PFO t]" arbitrary: l rule: pre_fo.induct)
      (auto elim!: pre_postE split: option.splits pevent.splits)

lemma pre_fo_pw [simp]:
  "pre_fo t (l @ [PW v]) = pre_fo t l"
  by (induct "l@[PW v]" arbitrary: l rule: pre_fo.induct)
      (auto elim!: pre_postE split: option.splits)

lemma pre_fo_other [simp]:
  "s \<noteq> t \<Longrightarrow> pre_fo t (l @ [PFO s]) = pre_fo t l"
  by (induct "l@[PFO t]" arbitrary: l rule: pre_fo.induct)
      (auto elim!: pre_postE split: option.splits pevent.splits)

subsection \<open>get for @{term PFO} effects\<close>

text \<open>Persistent memory after an @{term MF} is evaluated\<close>
definition get\<^sub>f :: "'t \<Rightarrow> ('a,'t,'b) state \<Rightarrow> ('a,'b) m"
  where "get\<^sub>f t m a \<equiv> case pre_fo t (buffers m a) of Some v \<Rightarrow> v | None \<Rightarrow> persistent m a"

lemma get\<^sub>f_no_pfo[simp]:
  assumes "\<forall>y. PFO t \<notin> set (buffers m y)"
  shows "get\<^sub>f t m = persistent m"
  using assms by (auto simp: get\<^sub>f_def fun_eq_iff split: option.splits)

lemma get\<^sub>f_no_pw[simp]:
  assumes "\<forall>e \<in> set (buffers m x). \<not> isPW e"
  shows "get\<^sub>f t m x = persistent m x"
  using assms by (auto simp: get\<^sub>f_def fun_eq_iff split: option.splits pevent.splits)

lemma get\<^sub>f_app_pfo [simp]:
  "get\<^sub>f t (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = (get\<^sub>f t m)(x := get m x)"
  by (auto simp: get_def fun_eq_iff get\<^sub>f_def split: option.splits pevent.splits)

lemma [simp]:
  assumes "\<forall>e \<in> set (buffers m x). \<not> isPW e"
  shows "get\<^sub>f t (m\<lbrakk>x \<^sub>p= v\<rbrakk>) = (get\<^sub>f t m)(x := v)"
  using assms by (auto simp: get\<^sub>f_def fun_eq_iff split: option.splits pevent.splits)

lemma get\<^sub>f_app_simps [simp]:
  "get\<^sub>f t (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) = (get\<^sub>f t m)"
  by (auto simp: get_def get\<^sub>f_def fun_eq_iff split: option.splits pevent.splits)

lemma [simp]:
  "get\<^sub>f t m x = c \<Longrightarrow> (get\<^sub>f t m)(x := c) = get\<^sub>f t m"
  by auto

lemma [simp]:
  "get\<^sub>f t (m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= []\<rbrakk>) = (get\<^sub>f t m)(x := v)"
  unfolding get\<^sub>f_def fun_eq_iff by (auto split: option.splits)

lemma [simp]:
  "s \<noteq> t \<Longrightarrow> get\<^sub>f s (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = get\<^sub>f s m"
  by (auto simp: get\<^sub>f_def fun_eq_iff split: option.splits)

subsection \<open>sat\<close>

definition sat :: "'t \<Rightarrow> ('a,'b,'t) pred \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  where "sat t Q m \<equiv> \<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> (get m', persistent m', get\<^sub>f t m') \<in> Q"

lemma sat_env_stable:
  assumes "sat t Q m" "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  shows "sat t Q m'"
  using assms unfolding sat_def
  by (meson converse_rtranclp_into_rtranclp)

subsection \<open>wp\<close>

fun wp :: "('a,'b) event \<Rightarrow> ('a,'b,'t) pred \<Rightarrow> ('a,'b,'t) pred"
  where
    "wp (W x v) Q = {(m,p,f). (m(x:=v),p,f) \<in> Q \<and> (m(x:=v),p(x:=v),f(x:=v)) \<in> Q}" |
    "wp (R x v) Q = {(m,p,f). m x = v \<longrightarrow> (m,p,f) \<in> Q}" |
    "wp (FL x) Q = {(m,p,f). (m,p(x := m x),f(x := m x)) \<in> Q}" |
    "wp MF Q = {(m,p,f). (m,f,f) \<in> Q}" |
    "wp (FO x) Q = {(m,p,f). (m,p,f(x := m x)) \<in> Q}" |
    "wp (RMW x v\<^sub>R v\<^sub>W) Q = {(m,p,f). m x = v\<^sub>R \<longrightarrow> (m(x:=v\<^sub>W),f,f) \<in> Q \<and> (m(x:=v\<^sub>W),f(x:=v\<^sub>W),f(x:=v\<^sub>W)) \<in> Q}" |
    "wp (RMF x v\<^sub>R) Q = {(m,p,f). m x = v\<^sub>R \<longrightarrow> (m,f,f) \<in> Q}"

lemma wp_sound:
  assumes "\<langle>m\<rangle> -t,a\<rightarrow> \<langle>m'\<rangle>" 
  shows "sat t (wp a Q) m \<longrightarrow> sat t Q m'"
  using assms
proof (cases)
  case (wr x v)
  thus ?thesis
    apply (clarsimp simp: sat_def)
    apply (elim envt_buffer_appE)
    by auto
next
  case (rd x v)
  thus ?thesis by (auto simp: sat_def)
next
  case mf
  hence "\<forall>y m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> PFO t \<notin> set (buffers m' y)" by (meson envt_buffer_subset in_mono)
  thus ?thesis using mf by (auto simp: sat_def)
next
  case (fl x)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> buffers m' x = []" using envt_buffer_empty by metis
  thus ?thesis using fl by (auto simp: sat_def)
next
  case (fo x)
  thus ?thesis by (auto elim!: envt_buffer_appE simp: sat_def)
next
  case (rmw x v\<^sub>R v\<^sub>W)
  hence "\<forall>y m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> PFO t \<notin> set (buffers m' y)" by (meson envt_buffer_subset in_mono)
  then show ?thesis using rmw apply (clarsimp simp: sat_def)
    apply (elim envt_buffer_appE)
    by auto
next
  case (rmf x v\<^sub>R)
  hence "\<forall>y m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> PFO t \<notin> set (buffers m' y)" by (meson envt_buffer_subset in_mono)
  then show ?thesis using rmf by (auto simp: sat_def)
qed
 
subsection \<open>Concurrency\<close>

definition wpr
  where "wpr r Q \<equiv> {(m,p,f). \<forall>m' p' f'. ((m,p,f),(m',p',f')) \<in> r \<longrightarrow>  (m',p',f') \<in> Q}"

fun guar
  where
    "guar q (W x v) r = {(m,p,f). \<forall>s. ((m,p,s),(m(x := v),p,s)) \<in> r \<and> ((m,p,s),(m(x := v),p(x := v),s(x := v))) \<in> r}" |
    "guar q (RMW x v\<^sub>R v\<^sub>W) r = {(m,p,f). m x = v\<^sub>R \<longrightarrow> (\<forall>s. ((m,p,s),(m(x := v\<^sub>W),p,s)) \<in> r \<and> ((m,p,s),(m(x := v\<^sub>W),p(x := v\<^sub>W),s(x := v\<^sub>W))) \<in> r)}" |
    "guar q _ r = UNIV"

fun beh
  where
    "beh (W x v) = ({((m,p,f,s),(m(x := v),p,f,s))| m p f s. True} \<union> {((m,p,f,s),(m(x := v),p(x := v),f(x := v),s(x := v))) | m p s f. True})" |
    "beh (R x v) = {((m,p,f,s),(m,p,f,s))| m p f s. m x = v}" |
    "beh (FL x)  = {((m,p,f,s),(m,p(x := m x),f(x := m x),s(x := m x)))| m p f s. True}" |
    "beh MF      = {((m,p,f,s),(m,f,f,s))| m p f s. True}" |
    "beh (FO x)  = {((m,p,f,s),(m,p,f(x := m x),s))|m p f s. True}" |
    "beh (RMW x v\<^sub>R v\<^sub>W) = ({((m,p,f,s),(m(x := v\<^sub>W),f,f,s))| m p f s . m x = v\<^sub>R} \<union> {((m,p,f,s),(m(x := v\<^sub>W),p(x := v\<^sub>W),f(x := v\<^sub>W),s(x := v\<^sub>W))) | m p f s . m x = v\<^sub>R})" |
    "beh (RMF x v\<^sub>R) = {((m,p,f,s),(m,f,f,s))| m p f s. m x = v\<^sub>R}" 

lemma step_rw:
  assumes "\<langle>m\<rangle> -t,x\<rightarrow> \<langle>m'\<rangle>"
  assumes "persistent m' = persistent m''"
  assumes "buffers m' = buffers m''"
  assumes "more m' = more m''"
  shows "\<langle>m\<rangle> -t,x\<rightarrow> \<langle>m''\<rangle>"
  using assms equality by blast


lemma wpr_sound:
  assumes "\<langle>m\<rangle> -t,a\<rightarrow> \<langle>m'\<rangle>" "sat t (guar t a r) m" "s \<noteq> t"
  assumes "sat s (wpr (r) Q) m" "trans (r)"
  shows "sat s (wpr (r) Q) m'"
  using assms
proof (cases)
  case (wr x v)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms wr
    apply (clarsimp simp: sat_def wpr_def)
    apply (elim envt_buffer_appE; simp)
     apply (meson transD)
    by (meson transD)
next
  case (rd x v)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms(4) rd 
    by (clarsimp simp: sat_def wpr_def)
next
  case mf
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms(4) mf 
    by (clarsimp simp: sat_def wpr_def)
next
  case (fl x)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms(4) fl 
    by (clarsimp simp: sat_def wpr_def)
next
  case (fo x)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms(3,4) fo 
    apply (clarsimp simp: sat_def wpr_def)
    by (elim envt_buffer_appE; simp)
next
  case (rmw x v\<^sub>R v\<^sub>W)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms rmw
    apply (clarsimp simp: sat_def wpr_def)
    apply (elim envt_buffer_appE; simp)
     apply (meson transD)
    by (meson transD)
next                 
  case (rmf x v\<^sub>R)
  hence "\<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> get m = get m'" by auto
  then show ?thesis using assms(4) rmf 
    by (clarsimp simp: sat_def wpr_def)
qed

lemma guar_mono:
  assumes "r \<subseteq> g"
  shows "guar t a r \<subseteq> guar t a g"
  using assms by (cases a; clarsimp) blast+

subsection \<open>wpl\<close>

fun wpl :: "'t \<Rightarrow>  ('a,'b,'t) prel \<Rightarrow> ('a,'b,'t) prel \<Rightarrow> ('a,'b) event list \<Rightarrow> ('a,'b,'t) pred \<Rightarrow> ('a,'b,'t) pred"
  where
    "wpl t r g [] A = wpr r A" |
    "wpl t r g (x#xs) A = wpr r (wp x (wpl t r g xs A) \<inter> guar t x g)"

fun id_filter
  where 
    "id_filter t [] = []" |
    "id_filter t ((s,e)#p) = (if t = s then e#(id_filter t p) else id_filter t p)"

definition compat
  where "compat r g \<equiv> \<forall>i j. i \<noteq> j \<longrightarrow> g i \<subseteq> r j"

lemma wpr_pres:
  assumes "sat s (wpr r Q) m" "refl r"
  shows "sat s Q m"
  using assms unfolding sat_def wpr_def
  apply clarsimp
  by (metis UNIV_I refl_on_def)

lemma [simp]:
  "sat t (P \<inter> Q) m = (sat t P m \<and> sat t Q m)"
  unfolding sat_def by auto

lemma sat_imp:
  "sat t P m \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> sat t Q m"
  by (auto simp: sat_def)

lemma wp_mono:
  assumes "P \<subseteq> Q"
  shows "wp a P \<subseteq> wp a Q"
  using assms by (cases a) auto

lemma wp_mono':
  assumes "m \<in> wp a P"
  assumes "P \<subseteq> Q"
  shows "m \<in> wp a Q"
  using assms by (cases a) auto

lemma wpl_sound:
  assumes "trace m ts m'" "\<forall>t. sat t (wpl t (r t) (g t) (id_filter t ts) (Q t)) m"
  assumes compat: "compat r g" 
  assumes refl: "\<forall>t. refl (r t) \<and> trans (r t)"
  shows "\<forall>t. sat t (Q t) m'"
  using assms(1,2)
proof (induct arbitrary: Q)
  case (nil a)
  then show ?case
    apply simp
    using refl wpr_pres by metis
next
  case (step m t a m' ts m'')
  have t: "sat t (wpl t (r t) (g t) (id_filter t ((t, a) # ts)) (Q t)) m" using step(4) by blast
  hence g: "sat t (guar t a (g t)) m" 
    apply simp
    apply (drule wpr_pres, insert refl, blast)
    by auto

  show ?case 
  proof (rule step(3), intro allI)
    fix s 
    have a: "sat s (wpl s (r s) (g s) (id_filter s ((t, a) # ts)) (Q s)) m" using step by auto
    show "sat s (wpl s (r s) (g s) (id_filter s ts) (Q s)) m'"
    proof (cases "s = t")
      case True
      then show ?thesis
        using a step(1)
        apply simp
        by (drule wpr_pres, insert refl, blast) (simp add: wp_sound)
    next
      case False
      hence "g t \<subseteq> r s" using assms by (auto simp: compat_def)
      hence "guar t a (g t) \<subseteq> guar t a (r s)" by (rule guar_mono)
      hence g: "sat t (guar t a (r s)) m"
        using g sat_imp by meson

      show ?thesis
      proof (cases "id_filter s ts")
        case Nil
        then show ?thesis using refl False a wpr_sound[OF step(1) g False] by simp
      next
        case (Cons a list)
        then show ?thesis using refl False a wpr_sound[OF step(1) g False] by simp
      qed
    qed
  qed
next
  case (env m m' t m'')
  then show ?case using sat_env_stable by metis
qed

definition interleave
  where "interleave ts ts' \<equiv> \<forall>t. id_filter t ts = id_filter t ts'"    

lemma interleave_nil:
  "interleave [] []"
  by (auto simp: interleave_def)

lemma interleave_cons:
  "interleave x y \<Longrightarrow> interleave (a#x) (a#y)"
  by (cases a) (auto simp: interleave_def)

lemma tenv_traceI:
  assumes "env\<^sup>*\<^sup>* m m'" "trace m' ts m''"
  shows "trace m ts m''"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case 
    using env by blast 
qed

lemma sat_conj:
  assumes "sat t P m" "sat t Q m"
  shows "sat t (P \<inter> Q) m"
  using assms by (auto simp: sat_def)

lemma id_filter_remove_other [simp]: 
  "s \<noteq> t \<Longrightarrow> id_filter s (remove1 (t, x) ts) = id_filter s ts"
  by (induct ts) (auto split: if_splits)

lemma id_filter_remove:
  assumes "id_filter t ts = x#re"
  shows "id_filter t (remove1 (t,x) ts) = re"
  using assms
proof (induct ts arbitrary: re)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case by (cases a) auto
qed

lemma interleave_remove:
  assumes "interleave (remove1 (t, x) ts) ts'"
  assumes "id_filter t ts = x#p"
  shows "interleave ts ((t,x)#ts')"
  using assms
  unfolding interleave_def
  apply auto
   prefer 2
    apply (frule id_filter_remove_other[where ts=ts and x=x])
   apply simp
  apply (frule id_filter_remove)
  apply simp
  done

subsection \<open>raise\<close>

text \<open>Convert the predicate encoding into a minimal state\<close>
definition raise
  where "raise t v p f \<equiv> \<lparr> persistent = p , 
                           buffers = \<lambda>x. (if p x \<noteq> f x then [PW (f x), PFO t] else []) @
                                         (if v x \<noteq> f x then [PW (v x)] else []) \<rparr>"

lemma [simp]:
  "get (raise t v p f) = v"
  by (auto simp: fun_eq_iff raise_def get_def)

lemma [simp]:
  "persistent (raise t v p f) = p"
  by (auto simp: fun_eq_iff raise_def)

lemma [simp]:
  "get\<^sub>f t (raise t v p f) = f"
  by (auto simp: fun_eq_iff raise_def get\<^sub>f_def contains_def)


lemma sat_wprI':
  assumes "\<And>m' m'' . env\<^sup>*\<^sup>* m m' \<longrightarrow> ((get m', persistent m', get\<^sub>f t m'),(get m'', persistent m'', get\<^sub>f t m'')) \<in> r \<longrightarrow> sat t Q m''"
  shows "sat t (wpr r Q) m"
  using assms unfolding sat_def wpr_def
  apply auto
  apply (subgoal_tac "((get m', persistent m', get\<^sub>f t m'), (get (raise t m'a p' f'), persistent  (raise t m'a p' f'), get\<^sub>f t  (raise t m'a p' f'))) \<in> r")
  prefer 2
   apply auto[1]
  apply (subgoal_tac "(get (raise t m'a p' f'), persistent (raise t m'a p' f'), get\<^sub>f t (raise t m'a p' f')) \<in> Q")
   apply simp
  by blast




section \<open>Completeness\<close>

text \<open>
Implication is sound but not complete for this encoding.
To make it complete, its necessary to enforce a wellformedness property over the predicate 
representation, such that constraints on non-volatile variables can be observed by
their volatile equivalents.

The implications of this loss of completeness needs to be considered and either accepted
or a new @{term wp} transformer that preserves the wellformedness property implemented.
\<close>

definition wf
  where "wf P \<equiv> \<forall>v p f Fs Vs. (v,p,f) \<in> P \<longrightarrow> 
              (v,(override_on (override_on p f Fs) v Vs),(override_on f v Vs)) \<in> P"


text \<open>Prefix a series of buffers with a constant list\<close>
definition prefix
  where "prefix m X p \<equiv> buffers_update (\<lambda>b. \<lambda>y. if y \<in> X then p@(b y) else b y) m"

lemma [simp]:
  "get (prefix m X [PFO t]) = get m"
  by (auto simp: prefix_def get_def fun_eq_iff split: option.splits pevent.split)

lemma [simp]:
  "persistent (prefix m X [PFO t]) = persistent m"
  by (auto simp: prefix_def fun_eq_iff split: option.splits pevent.split)

lemma [simp]:
  "get\<^sub>f t (prefix m X [PFO t]) = get\<^sub>f t m"
  by (auto simp: prefix_def fun_eq_iff get\<^sub>f_def split: option.splits pevent.split)

lemma env_raise:
  assumes "env (prefix (raise t v p f) X [PFO t]) m"
  obtains (wrv) x X where "m = prefix (raise t v (p(x := v x)) (f(x := v x))) X [PFO t]" |
          (wrf) x where "m = prefix (raise t v (p(x := f x)) f) (insert x X) [PFO t]" "v x \<noteq> f x" |
          (fo) x where "m = prefix (raise t v p f) (X - {x}) [PFO t]"
  using assms
proof cases
  case (pwr x v' l)
  show ?thesis
  proof (cases "v x = f x \<or> p x = f x")
    case True
    hence "m = prefix (raise t v (p(x := v x)) (f(x := v x))) (if p x \<noteq> f x then insert x X else X) [PFO t]"
      using pwr by (clarsimp split: if_splits simp: raise_def fun_eq_iff prefix_def)
    then show ?thesis using wrv by blast
  next
    case False
    hence "m = prefix (raise t v (p(x := f x)) f) (insert x X) [PFO t]"
      using pwr by (clarsimp split: if_splits simp: prefix_def raise_def fun_eq_iff)
    then show ?thesis using wrf False by auto
  qed
next
  case (pfo x t' l)
  hence "m = prefix (raise t v p f) (X - {x}) [PFO t]"
    by (clarsimp split: if_splits simp: prefix_def raise_def fun_eq_iff)
  then show ?thesis using fo by auto
qed

lemma envt_raise:
  assumes "env\<^sup>*\<^sup>* (prefix (raise t v p f) X [PFO t]) m"
  obtains Fs Vs X' where "m = prefix (raise t v (override_on (override_on p f Fs) v Vs) (override_on f v Vs)) X' [PFO t]"
  using assms
proof (induct)
  case base
  show ?case using base[where Fs="{}" and Vs="{}"] by auto
next
  case (step m\<^sub>2 m\<^sub>3)
  show ?case
  proof (rule step(3), goal_cases)
    case (1 Fs Vs X')
    show ?case using step(2) unfolding 1
    proof (cases rule: env_raise)
      case (wrv x X)
      then show ?thesis 
        using step(4)[where Fs=Fs and Vs="insert x Vs" and X'=X]
        by (metis override_on_insert) 
    next
      case (wrf x)
      hence e: "x \<notin> Vs" by (auto simp: override_on_def)
      hence a: "override_on f v Vs x = f x" by (auto simp: override_on_def)
      have b: "\<And>q f v. (override_on q v Vs)(x := f x) = override_on (q(x:=f x)) v Vs"
        using e unfolding override_on_def by auto
      show ?thesis
        using wrf(1) step(4)[where Fs="insert x Fs" and Vs=Vs and X'="insert x X'"]
        unfolding override_on_insert a b by blast
    next
      case (fo x)
      then show ?thesis using step(4) by blast
    qed
  qed 
qed

subsection \<open>Implication\<close>

lemma imp_complete:
  assumes "wf P"
  assumes "\<forall>m. sat t P m \<longrightarrow> sat t Q m"
  shows "P \<subseteq> Q"
proof clarsimp
  fix v p f
  assume p: "(v,p,f) \<in> P"
  let ?m = "prefix (raise t v p f) {} [PFO t]"
  have "sat t P ?m" using p assms(1) unfolding wf_def sat_def by (clarsimp elim!: envt_raise)
  hence "sat t Q ?m" using assms by auto
  thus "(v,p,f) \<in> Q" by (auto simp: sat_def)
qed

lemma c[simp]:
  "override_on (p(x := e)) (f(x := e)) V = (override_on p f V)(x := e)"
  unfolding override_on_def fun_eq_iff by auto

lemma [simp]:
  "override_on (p(x := f x)) f V = (override_on p f V)(x := f x)"
  unfolding override_on_def fun_eq_iff by auto

lemma [simp]:
  "override_on f f Fs = f"
  by (auto simp: override_on_def)

lemma [simp]:
  "x \<notin> Vs \<Longrightarrow> override_on f (v(x := e)) Vs = override_on f v Vs"
  by (auto simp: override_on_def)

lemma d:
  "x \<in> Vs \<Longrightarrow> override_on (f(x := v x)) (v(x := e))
      (Vs - {x}) = override_on f v Vs"
  by (auto simp: override_on_def fun_eq_iff)

lemma [simp]:
  "(override_on f v (Vs - {x}))(x := e) = (override_on f v Vs)(x := e)"
  by (auto simp: override_on_def fun_eq_iff)

end