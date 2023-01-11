theory PTSO
  imports Main
begin

type_synonym ('a,'b) m = "'a \<Rightarrow> 'b"

lemma rtrancl_summ:
  assumes "A\<^sup>*\<^sup>* m m'"
  assumes sub: "\<forall>m m'. A m m' \<longrightarrow> B m m'"
  assumes refl: "\<forall>m. B m m"
  assumes trans: "\<forall>m m' m''. B m m' \<longrightarrow> B m' m'' \<longrightarrow> B m m''"
  shows "B m m'"
  using assms(1)
proof (induct)
  case base
  then show ?case using refl by auto
next
  case (step m' m'')
  then show ?case using sub trans by auto
qed

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
  SF |
  FL "'a" |
  FO "'a" 
(*
  RMW "'a" "'b" "'b" |
  RMF "'a" "'b" *)

fun vars
  where
    "vars (W x _) = {x}" |
    "vars (R x _) = {x}" |
    "vars (FL x) = {x}" |
    "vars (FO x) = {x}" |
    "vars _ = {}"

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
  tbuffers :: "'t \<Rightarrow> ('a,'b) event list"

fun isWX
  where "isWX x (W y v) = (x = y)" | "isWX _ _ = False"

definition get :: "'t \<Rightarrow> ('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> 'b"
  where "get t m a \<equiv> 
    (case lastf (isWX a) (tbuffers m t) of Some (W _ v) \<Rightarrow> v | _ \<Rightarrow>
    (case lastf isPW (buffers m a) of Some (PW v) \<Rightarrow> v | _ \<Rightarrow> 
      persistent m a))"


abbreviation persistent_set :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>p= _\<rbrakk>" [900,0,0] 900)
  where "persistent_set m x v \<equiv> persistent_update (\<lambda>b. b(x := v)) m"

abbreviation buffer_set :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> ('t,'b) pevent list \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>b= _\<rbrakk>" [900,0,0] 900)
  where "buffer_set m x p \<equiv> buffers_update (\<lambda>b. b(x := p)) m"

abbreviation tbuffer_set :: "('a,'t,'b) state \<Rightarrow> 't \<Rightarrow> ('a,'b) event list \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>t= _\<rbrakk>" [900,0,0] 900)
  where "tbuffer_set m x p \<equiv> tbuffers_update (\<lambda>b. b(x := p)) m"

abbreviation buffer_app :: "('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> ('t,'b) pevent \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>@= _\<rbrakk>" [900,0,0] 900)
  where "buffer_app m x e \<equiv> m\<lbrakk>x \<^sub>b= (buffers m x)@[e] \<rbrakk>"

abbreviation tbuffer_app :: "('a,'t,'b) state \<Rightarrow> 't \<Rightarrow> ('a,'b) event \<Rightarrow> ('a,'t,'b) state" 
  ("_\<lbrakk>_ \<^sub>q= _\<rbrakk>" [900,0,0] 900)
  where "tbuffer_app m x e \<equiv> m\<lbrakk>x \<^sub>t= (tbuffers m x)@[e] \<rbrakk>"

lemma [simp]:
  shows "(lastf isPW p = Some (PFO v)) = False"
  by (rule iffI,drule lastf_some) auto

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

section \<open>Semantics\<close>

inductive step :: "('a,'t,'b) state \<Rightarrow> 't \<Rightarrow> ('a,'b) event \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -_,_\<rightarrow> \<langle>_\<rangle>")
  where
  wr: "\<langle>m\<rangle> -t,W x v\<rightarrow> \<langle>m\<lbrakk>t \<^sub>q= W x v\<rbrakk>\<rangle>" |
  rd: "get t m x = v \<Longrightarrow> \<langle>m\<rangle> -t,R x v\<rightarrow> \<langle>m\<rangle>" |
  mf: "tbuffers m t = [] \<Longrightarrow> \<forall>y. PFO t \<notin> set (buffers m y) \<Longrightarrow> \<langle>m\<rangle> -t,MF\<rightarrow> \<langle>m\<rangle>" |
  fl: "\<langle>m\<rangle> -t,FL x\<rightarrow> \<langle>m\<lbrakk>t \<^sub>q= FL x\<rbrakk>\<rangle>" |
  fo: "\<langle>m\<rangle> -t,FO x\<rightarrow> \<langle>m\<lbrakk>t \<^sub>q= FO x\<rbrakk>\<rangle>" |
  sf: "\<langle>m\<rangle> -t,SF\<rightarrow> \<langle>m\<lbrakk>t \<^sub>q= SF\<rbrakk>\<rangle>" 

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
  "get\<^sub>f t (m'\<lbrakk>s \<^sub>t= p\<rbrakk>) = get\<^sub>f t m'"
  by (auto simp: get\<^sub>f_def fun_eq_iff option.splits)

subsection \<open>get for shared memory\<close>

text \<open>Persistent memory after an @{term MF} is evaluated\<close>
definition get\<^sub>s :: "('a,'t,'b) state \<Rightarrow> ('a,'b) m"
  where "get\<^sub>s m a \<equiv> (case lastf isPW (buffers m a) of Some (PW v) \<Rightarrow> v | _ \<Rightarrow> persistent m a)"

lemma get\<^sub>s_no_pw[simp]:
  assumes "\<forall>e \<in> set (buffers m x). \<not> isPW e"
  shows "get\<^sub>s m x = persistent m x"
  using assms by (auto simp: get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits)

lemma get\<^sub>f_app_pfo [simp]:
  "get\<^sub>f t (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = (get\<^sub>f t m)(x := get\<^sub>s m x)"
  by (auto simp: get_def fun_eq_iff get\<^sub>f_def get\<^sub>s_def split: option.splits pevent.splits)

lemma [simp]:
  assumes "\<forall>e \<in> set (buffers m x). \<not> isPW e"
  shows "get\<^sub>s (m\<lbrakk>x \<^sub>p= v\<rbrakk>) = (get\<^sub>s m)(x := v)"
  using assms by (auto simp: get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits)

lemma get\<^sub>s_app_simps [simp]:
  "get\<^sub>s (m\<lbrakk>x \<^sub>@= PW v\<rbrakk>) = (get\<^sub>s m)(x := v)"
  "get\<^sub>s (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = (get\<^sub>s m)"
  by (auto simp: get_def get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits)

lemma [simp]:
  "get\<^sub>s (m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= []\<rbrakk>) = (get\<^sub>s m)(x := v)"
  unfolding get\<^sub>s_def fun_eq_iff by (auto split: option.splits pevent.splits)

section \<open>Persistent Environment Steps\<close>

inductive prp :: "('a,'t,'b) state \<Rightarrow> 't \<Rightarrow> ('a,'b) event \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -_,_\<leadsto> \<langle>_\<rangle>")
  where
  prpw:  "tbuffers m t = (W x v)#p \<Longrightarrow> \<langle>m\<rangle> -t,W x v\<leadsto> \<langle>m\<lbrakk>t \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>@= PW v\<rbrakk>\<rangle>" |
  prpfl: "tbuffers m t = (FL x)#p \<Longrightarrow> buffers m x = [] \<Longrightarrow> \<langle>m\<rangle> -t,FL x\<leadsto> \<langle>m\<lbrakk>t \<^sub>t= p\<rbrakk>\<rangle>" |
  prpfo: "tbuffers m t = b\<^sub>1@(FO x)#b\<^sub>2 \<Longrightarrow> set b\<^sub>1 \<inter> ({SF,FL x,FO x} \<union> {W x v|v. True}) = {} \<Longrightarrow> 
            \<langle>m\<rangle> -t,FO x\<leadsto> \<langle>m\<lbrakk>t \<^sub>t= b\<^sub>1@b\<^sub>2\<rbrakk>\<lbrakk>x \<^sub>@= PFO t\<rbrakk>\<rangle>" |
  prpsf: "tbuffers m t = SF#b \<Longrightarrow> \<forall>y. PFO t \<notin> set (buffers m y) \<Longrightarrow> \<langle>m\<rangle> -t,SF\<leadsto> \<langle>m\<lbrakk>t \<^sub>t= b\<rbrakk>\<rangle>"

function prpall where
  "prpall t m = (case tbuffers m t of [] \<Rightarrow> m
                                    | (W x v)#p \<Rightarrow> prpall t (m\<lbrakk>t \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>@= PW v\<rbrakk>)
                                    | (FL x)#p \<Rightarrow> prpall t (m\<lbrakk>x \<^sub>b= []\<rbrakk>\<lbrakk>x \<^sub>p= get\<^sub>s m x\<rbrakk>\<lbrakk>t \<^sub>t= p\<rbrakk>)
                                    | (FO x)#p \<Rightarrow> prpall t (m\<lbrakk>t \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>@= PFO t\<rbrakk>)
                                    | SF#p \<Rightarrow> prpall t (m\<lparr> persistent := get\<^sub>f t m\<rparr>\<lbrakk>t \<^sub>t= p\<rbrakk>))"
  by pat_completeness auto
  termination by (relation "measure (\<lambda>(m,t). length (tbuffers t m))") auto

declare prpall.simps[simp del]

lemma prpwI:
  assumes "tbuffers m t = (W x v)#p"
  assumes "m' = m\<lbrakk>t \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>@= PW v\<rbrakk>"
  shows "\<langle>m\<rangle> -t,W x v\<leadsto> \<langle>m'\<rangle>"
  using prp.prpw assms by metis

lemma prpflI:
  assumes "tbuffers m t = (FL x)#p" "buffers m x = []"
  assumes "m' = m\<lbrakk>t \<^sub>t= p\<rbrakk>"
  shows "\<langle>m\<rangle> -t,FL x\<leadsto> \<langle>m'\<rangle>"
  using prp.prpfl assms by metis

lemma prpfoI:
  assumes "tbuffers m t =  b\<^sub>1@(FO x)#b\<^sub>2" "set b\<^sub>1 \<inter> ({SF,FL x,FO x} \<union> {W x v|v. True}) = {}"
  assumes "m' = m\<lbrakk>t \<^sub>t= b\<^sub>1@b\<^sub>2\<rbrakk>\<lbrakk>x \<^sub>@= PFO t\<rbrakk>"
  shows "\<langle>m\<rangle> -t,FO x\<leadsto> \<langle>m'\<rangle>"
  using prp.prpfo[OF assms(1,2)] assms(3) by auto

lemma prpsfI:
  assumes "tbuffers m t = SF#b" "\<forall>y. PFO t \<notin> set (buffers m y)"
  assumes "m' = m\<lbrakk>t \<^sub>t= b\<rbrakk>"
  shows "\<langle>m\<rangle> -t,SF\<leadsto> \<langle>m'\<rangle>"
  using prp.prpsf assms by metis

inductive env :: "('a,'t,'b) state \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  ("\<langle>_\<rangle> -e\<rightarrow> \<langle>_\<rangle>")
  where
  pwr:   "buffers m x = (PW v)#p \<Longrightarrow> \<langle>m\<rangle> -e\<rightarrow> \<langle>m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>\<rangle>" |
  pfo:   "buffers m x = (PFO t)#p \<Longrightarrow> \<langle>m\<rangle> -e\<rightarrow> \<langle>m\<lbrakk>x \<^sub>b= p\<rbrakk>\<rangle>"

lemma pwrI [intro]:
  assumes "buffers m x = (PW v)#p"
  assumes "m' = m\<lbrakk>x \<^sub>p= v\<rbrakk>\<lbrakk>x \<^sub>b= p\<rbrakk>"
  shows "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  using env.pwr assms by metis

lemma pfoI [intro]:
  assumes "buffers m x = (PFO t)#p"
  assumes "m' = m\<lbrakk>x \<^sub>b= p\<rbrakk>"
  shows "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  using env.pfo assms by metis

subsection \<open>Persistent Properties\<close>

lemma env_get [simp]:
  assumes "env m m'"
  shows "get t m x = get t m' x"
  using assms 
  by cases (auto simp: get_def fun_eq_iff split: option.splits pevent.splits event.splits)

lemma env_get\<^sub>s [simp]:
  assumes "env m m'"
  shows "get\<^sub>s m x = get\<^sub>s m' x"
  using assms 
  by cases (auto simp: get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits event.splits)

lemma envt_get [simp]:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "get t m x = get t m' x"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_get by metis
qed

lemma envt_get\<^sub>s [simp]:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "get\<^sub>s m = get\<^sub>s m'"
  using assms
proof (induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case using env_get\<^sub>s by metis
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

lemma env_tbuffer [simp]:
  assumes "env m m'"
  shows "tbuffers m = tbuffers m'"
  using assms by cases auto

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

lemma prp_self_tbuffer:
  assumes "prp m t a m'"
  shows "set (tbuffers m' t) \<subseteq> set (tbuffers m t)"
  using assms by cases auto

lemma prp_get\<^sub>s_nevent [simp]:
  assumes "prp m t a m'" "tbuffers m t = []"
  shows "get\<^sub>s m x = get\<^sub>s m' x"
  using assms by cases auto

lemma [simp]:
  assumes "tbuffers m t = []"
  shows "prp m t a m' = False"
  apply auto
  using assms
  apply (cases "prp m t a m'")
   apply (cases rule: prp.cases, blast; clarsimp)
  by auto

section \<open>Predicate Language\<close>

text \<open>Predicate abstraction to simplify specification, consisting of: 
      (volatile memory, persistent memory, memory after an mfence)\<close>
type_synonym ('a,'b) pred = "(('a,'b option) m \<times> ('a,'b) m \<times> ('a,'b) m \<times> ('a,'b) m) set"
type_synonym ('a,'b) prel = "(('a,'b) m \<times> ('a,'b) m \<times> ('a,'b) m) rel"


subsection \<open>sat\<close>

definition buf :: "'t \<Rightarrow> ('a,'t,'b) state \<Rightarrow> 'a \<Rightarrow> 'b option"
  where "buf t m a \<equiv> 
    (case lastf (isWX a) (tbuffers m t) of Some (W _ v) \<Rightarrow> Some v | _ \<Rightarrow> None)"

definition sat :: "'t \<Rightarrow> ('a,'b) pred \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  where "sat t Q m \<equiv> \<forall>m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> (buf t m', persistent m', get\<^sub>f t m', get\<^sub>s m') \<in> Q"

lemma sat_env_stable:
  assumes "sat t Q m" "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle>"
  shows "sat t Q m'"
proof (clarsimp simp: sat_def)
  fix n assume a: "env\<^sup>*\<^sup>* m' n"
  hence "env\<^sup>*\<^sup>* m n" using assms by (metis (no_types, lifting) converse_rtranclp_into_rtranclp) 
  moreover have "get\<^sub>s m = get\<^sub>s m'" using assms by auto
  ultimately show "(buf t n, persistent n, get\<^sub>f t n, get\<^sub>s n) \<in> Q" using assms by (auto simp: sat_def)
qed

subsection \<open>wp\<close>

fun wp :: "('a,'b) event \<Rightarrow> ('a,'b) pred \<Rightarrow> ('a,'b) pred"
  where
    "wp (W x v) Q = {(m,p,f,s). (m(x:= Some v),p,f,s(x:=v)) \<in> Q \<and> (m(x:=Some v),p(x:=v),f(x:=v),s(x:=v)) \<in> Q}" |
    "wp (R x v) Q = {(m,p,f,s). (m x = Some v \<or> s x = v) \<longrightarrow> (m,p,f,s) \<in> Q}" |
    "wp (FL x) Q = {(m,p,f,s). (m,p(x := s x),f(x := s x),s) \<in> Q}" |
    "wp MF Q = {(m,p,f,s). (m,f,f,s) \<in> Q}" |
    "wp SF Q = {(m,p,f,s). (m,f,f,s) \<in> Q}" |
    "wp (FO x) Q = {(m,p,f,s). (m,p,f(x := s x),s) \<in> Q}"

lemma [simp]:
  "tbuffers m t = [] \<Longrightarrow> get t m = get\<^sub>s m"
  by (auto simp: fun_eq_iff get_def get\<^sub>s_def)

lemma [elim!]:
  assumes "[E] = b\<^sub>1 @ A # b\<^sub>2"
  obtains "b\<^sub>1 = []" "b\<^sub>2 = []" "A = E"
  using assms by (cases b\<^sub>1; cases b\<^sub>2; auto)
lemma [simp]:
  "(\<lambda>b a. if a = t then c else b a) \<circ> (\<lambda>b. b(t := q)) = (\<lambda>b a. if a = t then c else b a)"
  by (auto simp: fun_eq_iff)

lemma [simp]:
  "tbuffers_update (\<lambda>b a. if a = t then tbuffers m\<^sub>3 t else b a) m\<^sub>3 = m\<^sub>3"
  by (auto simp: fun_eq_iff)

lemma [simp]:
  assumes "tbuffers m t = a"
  shows "m\<lbrakk>t \<^sub>t= a\<rbrakk> = m"
  using assms 
  by force

lemma env_tbuffer_orth:
  assumes "env m\<^sub>1 m\<^sub>2"
  shows "env (m\<^sub>1\<lbrakk>s \<^sub>t= p\<rbrakk>) (m\<^sub>2\<lbrakk>s \<^sub>t= p\<rbrakk>)"
  using assms by cases auto

lemma envt_tbuffer_orth:
  assumes "env\<^sup>*\<^sup>* m\<^sub>1 m\<^sub>2"
  shows "env\<^sup>*\<^sup>* (m\<^sub>1\<lbrakk>s \<^sub>t= p\<rbrakk>) (m\<^sub>2\<lbrakk>s \<^sub>t= p\<rbrakk>)"
  using assms 
  apply (rule rtrancl_summ)
  apply (metis env_tbuffer_orth r_into_rtranclp)
  by auto

lemma envt_tupdE:
  assumes "env\<^sup>*\<^sup>* (m\<^sub>3\<lbrakk>t \<^sub>t= q\<rbrakk>) n"
  obtains "env\<^sup>*\<^sup>* m\<^sub>3 (n\<lbrakk>t \<^sub>t= tbuffers m\<^sub>3 t\<rbrakk>)"
  using envt_tbuffer_orth[OF assms, where s=t and p="tbuffers m\<^sub>3 t"] by simp

lemma [simp]:
  "get\<^sub>s (n\<lbrakk>t \<^sub>t= a\<rbrakk>) = get\<^sub>s n"
  "get\<^sub>s (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = get\<^sub>s m"
  by (auto simp: get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits)  

lemma [simp]:
  "get\<^sub>f t (n\<lbrakk>t \<^sub>t= tbuffers m\<^sub>3 t\<rbrakk>) = get\<^sub>f t n"
  by (auto simp: get\<^sub>f_def fun_eq_iff split: option.splits pevent.splits)  

lemma [simp]:
  "get t (m\<lbrakk>t \<^sub>q= W x v\<rbrakk>) = (get t m)(x := v)"
  "get t (m\<lbrakk>t \<^sub>q= FL x\<rbrakk>) = (get t m)"
  "get t (m\<lbrakk>t \<^sub>q= FO x\<rbrakk>) = (get t m)"
  "get t (m\<lbrakk>t \<^sub>q= SF\<rbrakk>) = (get t m)"
  by (auto simp: get_def fun_eq_iff split: option.splits pevent.splits event.splits)

lemma env_:
  assumes "env m\<^sub>1 m\<^sub>2"
  shows "env (m\<^sub>1\<lbrakk>s \<^sub>q= E\<rbrakk>) (m\<^sub>2\<lbrakk>s \<^sub>q= E\<rbrakk>)"
  using assms by cases auto

lemma env_append:
  assumes "env m\<^sub>1 m\<^sub>2"
  shows "env (m\<^sub>1\<lbrakk>s \<^sub>q= E\<rbrakk>) (m\<^sub>2\<lbrakk>s \<^sub>q= E\<rbrakk>)"
  using assms by cases auto

lemma envt_append:
  assumes "env\<^sup>*\<^sup>* m\<^sub>1 m\<^sub>2"
  shows "env\<^sup>*\<^sup>* (m\<^sub>1\<lbrakk>s \<^sub>q= E\<rbrakk>) (m\<^sub>2\<lbrakk>s \<^sub>q= E\<rbrakk>)"
  using assms
  apply (rule rtrancl_summ)
  using env_append apply (metis r_into_rtranclp) 
  by auto

lemma prp_append:
  assumes "prp m\<^sub>1 t a m\<^sub>2"
  shows "prp (m\<^sub>1\<lbrakk>s \<^sub>q= E\<rbrakk>) t a (m\<^sub>2\<lbrakk>s \<^sub>q= E\<rbrakk>)"
  using assms 
proof cases
  case (prpw x v p)
  then show ?thesis by (cases "s = t") (auto intro!: prpwI simp: fun_upd_twist)
next
  case (prpfl x p)
  then show ?thesis by (cases "s = t") (auto intro!: prpflI simp: fun_upd_twist)
next
  case (prpfo b\<^sub>1 x b\<^sub>2)
  then show ?thesis by (cases "s = t") (auto intro!: prpfoI simp: fun_upd_twist)
next
  case (prpsf b)
  then show ?thesis by (cases "s = t") (auto intro!: prpsfI simp: fun_upd_twist)
qed

lemma [simp]:
  "get\<^sub>s (n\<lbrakk>x \<^sub>b= []\<rbrakk>) = (get\<^sub>s n)(x := persistent n x)"
  by (auto simp: fun_eq_iff get\<^sub>s_def split: option.splits pevent.splits)

lemma [simp]:
  "get\<^sub>f t (n\<lbrakk>x \<^sub>b= []\<rbrakk>) = (get\<^sub>f t n)(x := persistent n x)"
  by (auto simp: fun_eq_iff get\<^sub>f_def split: option.splits pevent.splits)

lemma [simp]:
  "get\<^sub>f t (n\<lbrakk>t \<^sub>t= a\<rbrakk>) = get\<^sub>f t n"
  by (auto simp: fun_eq_iff get\<^sub>f_def split: option.splits pevent.splits)

subsection \<open>Concurrency\<close>

definition wpr
  where "wpr r Q \<equiv> {(m,p,f,b). \<forall>b' p' f'. ((b,p,f),(b',p',f')) \<in> r \<longrightarrow>  (m,p',f',b') \<in> Q}"

fun guar
  where
    "guar (W x v) r = {(m,p,f,s). \<forall>f. ((s,p,f),(s(x := v),p,f)) \<in> r \<and> ((s,p,f),(s(x := v),p(x := v),f(x := v))) \<in> r}" |
    "guar _ r = UNIV"

lemma [simp]:
  "s \<noteq> t \<Longrightarrow> get\<^sub>f s (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = get\<^sub>f s m"
  by (auto simp: get\<^sub>f_def fun_eq_iff split: option.splits)

lemma get\<^sub>s_app_simps' [simp]:
  "get\<^sub>s (m\<lbrakk>x \<^sub>b= p @ [PW v]\<rbrakk>) = (get\<^sub>s m)(x := v)"
  by (auto simp: get_def get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits)


lemma get\<^sub>s_app_simps'' [simp]:
  "get\<^sub>s (m\<lbrakk>x \<^sub>t= p\<rbrakk>) = (get\<^sub>s m)"
  by (auto simp: get_def get\<^sub>s_def fun_eq_iff split: option.splits pevent.splits)

lemma [simp]:
  "s \<noteq> t \<Longrightarrow> get s (m'a\<lbrakk>t \<^sub>t= p\<rbrakk>) = get s (m'a)"
  unfolding get_def fun_eq_iff
  by (clarsimp split: option.splits pevent.splits event.splits)


lemma [simp]:
  "buf s (m\<lbrakk>x \<^sub>p= v\<rbrakk>) = buf s m"
  "buf s (m\<lbrakk>x \<^sub>@= a\<rbrakk>) = buf s m"
  "s \<noteq> t \<Longrightarrow> buf s (m'a\<lbrakk>t \<^sub>t= p\<rbrakk>) = buf s (m'a)"
  unfolding buf_def fun_eq_iff
  by (clarsimp split: option.splits pevent.splits event.splits)+

lemma [simp]:
  "get s (m\<lbrakk>x \<^sub>@= PFO t\<rbrakk>) = get s m"
  unfolding get_def fun_eq_iff
  by (clarsimp split: option.splits pevent.splits event.splits)

lemma wpr_sound:
  assumes "\<langle>m\<rangle> -t,a\<leadsto> \<langle>m'\<rangle>" "sat t (guar a r) m" "s \<noteq> t"
  assumes "sat s (wpr (r) Q) m" "trans (r)"
  shows "sat s (wpr (r) Q) m'"
  using assms
proof (cases)
  case (prpw x v p)
  show ?thesis using assms
    unfolding sat_def prpw wpr_def
    apply (intro allI impI)
    apply (elim envt_buffer_appE envt_tupdE)


    prefer 3
      apply (auto)[1]
     prefer 2
    apply auto
     apply (subgoal_tac "((get\<^sub>s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), persistent (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), (get\<^sub>f s m\<^sub>3)), (get\<^sub>s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>))(x := v), (persistent (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>))(x := v), (get\<^sub>f s m\<^sub>3)(x := v)) \<in> r")
    prefer 2
      apply blast
     apply simp
     apply (subgoal_tac "((get\<^sub>s m\<^sub>3, persistent m\<^sub>3, get\<^sub>f s m\<^sub>3), b', p', f') \<in> r")
    prefer 2
      apply (meson transE)
     apply (subgoal_tac "((get\<^sub>s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), persistent (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), get\<^sub>f s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>)), b', p', f') \<in> r")
    prefer 2
      apply simp
    apply (subgoal_tac "(buf s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), p', f', b') \<in> Q")
    prefer 2
      apply blast
     apply simp
    
     
     apply (subgoal_tac "((get\<^sub>s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), persistent (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), (get\<^sub>f s m\<^sub>3)), (get\<^sub>s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>))(x := v), (persistent (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>)), (get\<^sub>f s m\<^sub>3)) \<in> r")
    prefer 2
    apply blast
    apply simp
     apply (subgoal_tac "((get\<^sub>s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), persistent (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), get\<^sub>f s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>)), b', p', f') \<in> r")
    prefer 2
      apply simp
      apply (meson transE)
    apply (subgoal_tac "(buf s (m\<^sub>3\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>), p', f', b') \<in> Q")
    prefer 2
      apply blast
    apply simp 
    done
next
  case (prpfl x p)
  then show ?thesis using assms by (auto elim!: envt_tupdE simp: sat_def)
next
  case (prpfo b\<^sub>1 x b\<^sub>2)
  show ?thesis using assms
    unfolding sat_def prpfo 
    apply (intro allI impI)
    apply (elim envt_buffer_appE envt_tupdE)
    unfolding get\<^sub>s_app_simps
    by (auto)
next
  case (prpsf b)
  then show ?thesis using assms by (auto elim!: envt_tupdE simp: sat_def)
qed

subsection \<open>wpl\<close>

fun wpl :: " ('a,'b) prel \<Rightarrow> ('a,'b) prel \<Rightarrow> ('a,'b) event list \<Rightarrow> ('a,'b) pred \<Rightarrow> ('a,'b) pred"
  where
    "wpl r g [] A = wpr r A" |
    "wpl r g (x#xs) A = wpr r (wp x (wpl r g xs A) \<inter> guar x g)"

definition compat
  where "compat r g \<equiv> \<forall>i j. i \<noteq> j \<longrightarrow> g i \<subseteq> r j"

inductive trace :: "('a,'t,'b) state \<Rightarrow> ('t \<times> ('a,'b) event) list \<Rightarrow> ('a,'t,'b) state \<Rightarrow> bool"
  where
  nil:  "trace a [] a" |
  step: "\<langle>m\<rangle> -thr,a\<rightarrow> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m ((thr,a)#t) m''" |
  env:  "\<langle>m\<rangle> -e\<rightarrow> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m t m''" |
  prp:  "\<langle>m\<rangle> -thr,a\<leadsto> \<langle>m'\<rangle> \<Longrightarrow> trace m' t m'' \<Longrightarrow> trace m t m''"

fun id_filter
  where 
    "id_filter t [] = []" |
    "id_filter t ((s,e)#p) = (if t = s then e#(id_filter t p) else id_filter t p)"

lemma [simp]:
  "(\<lambda>b. b(s := tbuffers m s)) \<circ> (\<lambda>b. b(s := tbuffers m s @ [A], t := p)) = (\<lambda>b. b(s := tbuffers m s @ [A], t := p, s := tbuffers m s))"
  by (auto simp: fun_eq_iff)

lemma sat_tbuffer [simp]:
  "t \<noteq> s \<Longrightarrow> sat t Q (m\<lbrakk>s \<^sub>t= p\<rbrakk>) = sat t Q m"
  unfolding sat_def
  apply rule
   apply clarsimp
   apply (drule envt_tbuffer_orth[where s=s and p=p])
   apply (subgoal_tac "(buf t (m'\<lbrakk>s \<^sub>t= p\<rbrakk>), persistent (m'\<lbrakk>s \<^sub>t= p\<rbrakk>), get\<^sub>f t (m'\<lbrakk>s \<^sub>t= p\<rbrakk>), get\<^sub>s (m'\<lbrakk>s \<^sub>t= p\<rbrakk>)) \<in> Q")
  prefer 2
    apply blast
  by (auto intro: envt_tbuffer_orth elim!: envt_tupdE)

lemma wpr_pres:
  assumes "sat s (wpr r Q) m" "refl r"
  shows "sat s Q m"
  using assms unfolding sat_def wpr_def
  apply clarsimp
  by (metis UNIV_I refl_on_def)

lemma [simp]:
  "get\<^sub>s (m\<lbrakk>s \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>b= buffers m x @ [PW v]\<rbrakk>) = (get\<^sub>s m)(x := v)"
  by (auto simp: fun_eq_iff get\<^sub>s_def split: option.splits pevent.splits)

lemma [simp]:
  "get\<^sub>s (m\<lbrakk>s \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>b= buffers m x @ [PFO t]\<rbrakk>) = (get\<^sub>s m)"
  by (auto simp: fun_eq_iff get\<^sub>s_def split: option.splits pevent.splits)

lemma wpl_concat:
  "trans r \<Longrightarrow> refl r \<Longrightarrow> wpl r g (pre@post) Q = wpl r g pre (wpl r g post Q)"
proof (induct pre)
  case Nil
  then show ?case 
    apply auto
     apply (cases post)
      apply auto
      apply (unfold wpr_def)
      apply simp
      apply (meson transE)
     apply simp
      apply (meson transE)
    apply simp
    by (simp add: refl_onD)
next
  case (Cons a pre)
  then show ?case by auto
qed

lemma wpr_mono:
  assumes "P \<subseteq> Q"
  shows "wpr r P \<subseteq> wpr r Q"
  using assms unfolding wpr_def
  by auto

lemma wp_mono:
  assumes "P \<subseteq> Q"
  shows "wp a P \<subseteq> wp a Q"
  using assms by (cases a) auto

lemma wpl_mono:
  assumes "P \<subseteq> Q"
  shows "wpl r g p P \<subseteq> wpl r g p Q"
  using assms
proof (induct p)
  case Nil
  then show ?case by (auto intro!: wpr_mono wp_mono)
next
  case (Cons a p)
  then show ?case using wpr_mono wp_mono
    by (metis Int_mono dual_order.refl wpl.simps(2))
qed

lemma [simp]:
  "x \<in> C \<Longrightarrow> override_on (m(x := f)) m' C = override_on m m' C"
  by (auto simp: override_on_def)

lemma [simp]:
  "x \<in> C \<Longrightarrow> (override_on m m' C)(x := m' x) = override_on m m' C"
  by (auto simp: override_on_def)

lemma [simp]:
  "x \<notin> C \<Longrightarrow> override_on (m(x := f)) m' C = (override_on m m' C)(x := f)"
  by (auto simp: override_on_def)

lemma imp_sound:
  assumes "sat t P m" "P \<subseteq> Q" 
  shows "sat t Q m"
  using assms by (auto simp: sat_def)

lemma simple:
  "(a # b) @ c = a # (b @ c)"
  by auto

lemma wp_MF_sound:
  assumes "\<langle>m\<rangle> -t,MF\<rightarrow> \<langle>m'\<rangle>"
  assumes sat: "sat t (wp MF Q) m"
  shows "sat t Q m'"
  using assms
proof (cases)
  case mf
  hence "\<forall>y m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> PFO t \<notin> set (buffers m' y)" by (meson envt_buffer_subset in_mono)
  thus ?thesis using mf sat by (auto simp: sat_def)
qed

lemma wp_MF:
  assumes "tbuffers m t = []" "\<forall>y. PFO t \<notin> set (buffers m y)"
  shows "sat t (wp MF Q) m = sat t Q m"
proof -
  have "\<forall>y m'. env\<^sup>*\<^sup>* m m' \<longrightarrow> PFO t \<notin> set (buffers m' y)" 
    using assms by (meson envt_buffer_subset in_mono)
  thus ?thesis using assms by (auto simp: sat_def)
qed

lemma merge_r:
  assumes "(a, m') \<in> r\<^sup>* " "(m', m'') \<in> r\<^sup>* "
  shows "(a,m'') \<in> r\<^sup>*"
  using assms 
  by auto

lemma guar_mono:
  assumes "r \<subseteq> g"
  shows "guar a r \<subseteq> guar a g"
  using assms by (cases a; clarsimp) blast+

(*
  all pending operations from a thread satisfy their guarantees, given the wpl structure.
*)

lemma squash[simp]:
  "(m\<lbrakk>s \<^sub>t= p\<rbrakk>\<lbrakk>x \<^sub>@= a\<rbrakk>\<lbrakk>s \<^sub>t= q\<rbrakk>) = (m\<lbrakk>s \<^sub>t= q\<rbrakk>\<lbrakk>x \<^sub>@= a\<rbrakk>)"
  by (rule equality) auto

lemma envt_tbuffer:
  assumes "env\<^sup>*\<^sup>* m m'"
  shows "tbuffers m = tbuffers m'"
  using assms by (rule rtrancl_summ) auto

lemma get_split:
  assumes "get s m x = v"
  obtains "get\<^sub>s m x = v"  "buf s m x = None" | "buf s m x = Some v"
  using assms unfolding get_def buf_def get\<^sub>s_def
  by (auto split: event.splits option.splits)  

(*
definition atom
  where "atom r \<equiv> \<forall>x y m p f m' p' f'. ((m,p,f),(m',p',f')) \<in> r \<longrightarrow> x \<noteq> y \<longrightarrow> m x \<noteq> m' x \<longrightarrow> m y \<noteq> m' y \<longrightarrow> (\<exists>m'' p'' f''. ((m,p,f),(m'',p'',f'')) \<in> r \<and> ((m'',p'',f''),(m',p',f')) \<in> r \<and> ((m x = m'' x \<and> m'' y = m' y) \<or> (m y = m'' y \<and> m'' x = m' x)))"

lemma atom_univ:
  "atom UNIV"
  unfolding atom_def
  apply clarsimp
  apply (subgoal_tac "m x = (m(y := m' y)) x \<and> (m(y := m' y)) y = m' y")
   apply blast
  apply auto
  done

lemma
  assumes "refl r" "trans r" "atom r"
  shows "x \<noteq> y \<Longrightarrow> wpr r (wp (W y w) (wpr r (wp (R x v) Q))) \<subseteq> wpr r (wp (R x v) (wpr r (wp (W y w) Q)))"
  apply (clarsimp simp: wpr_def, intro conjI impI allI)
  apply (meson UNIV_I assms(1) assms(2) refl_onD transD)
    apply (meson UNIV_I assms(1) assms(2) refl_onD transD)
  

lemma
  assumes "refl r" "trans r" "atom r"
  shows "wpr r (wp (FO y) (wpr r (wp (R x v) Q))) \<subseteq> wpr r (wp (R x v) (wpr r (wp (FO y) Q)))"
  apply (clarsimp simp: wpr_def, intro conjI impI allI)
   apply (meson UNIV_I assms(1) assms(2) refl_onD transD)
   *)

lemma write_read_same:
  assumes "refl r" "trans r" 
  shows "wpr r (wp (W x v) (wpr r (wp (R x v) Q)) \<inter> guar (W x v) g) \<subseteq>  wpr r (wp (W x v) Q \<inter> guar (W x v) g)"
  apply (clarsimp simp: wpr_def, intro conjI impI allI)
  apply (meson UNIV_I assms(1) assms(2) refl_onD transD)
    apply (meson UNIV_I assms(1) assms(2) refl_onD transD)
  done

lemma reorder_rd_no_write:
  assumes "lastf (isWX x) l = None"
  shows "wpl r g (l @ [R x v]) Q \<subseteq> wpl (r) (g) (R x v # l) Q"  
  using assms(1)
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  hence a: "\<forall>v. a \<noteq> W x v" by (auto split: if_splits option.splits)
  have "wpl r g (l @ [R x v]) Q \<subseteq> wpl r g (R x v # l) Q" (is "?P \<subseteq> ?Q")
    using Cons by (auto split: if_splits option.splits)
  hence "wpr r (wp a ?P \<inter> guar a g) \<subseteq> wpr r (wp a ?Q \<inter> guar a g)"
    by (meson Int_mono dual_order.refl wp_mono wpr_mono)
  also have "... \<subseteq> wpr r (wp (R x v) (wpr r (wp a (wpl r g l Q) \<inter> guar a g)))"
    using a
    apply (simp del: wp.simps)
    sorry (* reordering! *)
  finally show ?case by simp
qed

lemma reorder_fo:
  shows "wpl r g (l @ [FO x]) Q \<subseteq> wpl (r) (g) (FO x # l) Q"  
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  have "wpl r g (l @ [FO x]) Q \<subseteq> wpl r g (FO x # l) Q" (is "?P \<subseteq> ?Q")
    using Cons by (auto split: if_splits option.splits)
  hence "wpr r (wp a ?P \<inter> guar a g) \<subseteq> wpr r (wp a ?Q \<inter> guar a g)"
    by (meson Int_mono dual_order.refl wp_mono wpr_mono)
  also have "... \<subseteq> wpr r (wp (FO x) (wpr r (wp a (wpl r g l Q) \<inter> guar a g)))"
    apply (simp del: wp.simps)
    sorry (* reordering! *)
  finally show ?case by simp
qed

lemma reorder_rd_write:
  assumes "lastf (isWX x) l = Some (W x v)"
  assumes "trans r" "refl r" 
  shows "wpl r g (l @ [R x v]) Q \<subseteq> wpl r g l Q"
  using assms(1)
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  show ?case using Cons(2)
  proof (simp split: option.splits, goal_cases)
    case 1
    hence a: "a = W x v" "lastf (isWX x) l = None" 
      by (auto split: if_splits)
    hence "wpl r g (l @ [R x v]) Q \<subseteq> wpl (r) (g) (R x v # l) Q" (is "?P \<subseteq> ?Q")
      using reorder_rd_no_write by metis
    hence "wpr r (wp a ?P \<inter> guar a g) \<subseteq> wpr r (wp a ?Q \<inter> guar a g)"
      by (meson Int_mono dual_order.refl wp_mono wpr_mono)
    also have "... \<subseteq> wpr r (wp a (wpl r g l Q) \<inter> guar a g)"
      using write_read_same[OF assms(3,2)] a(1)
      apply (simp del: wp.simps guar.simps)
      by auto
    finally show ?case by simp
  next
    case (2 z)
    hence "wpl r g (l @ [R x v]) Q \<subseteq> wpl r g l Q" 
      using Cons by auto
    then show ?case
      by (meson Int_mono dual_order.refl wp_mono wpr_mono)
  qed
qed

lemma wpr_wpl:
  "trans r \<Longrightarrow> refl r \<Longrightarrow> wpr r (wpl r g l Q) = wpl r g l Q"
  apply (cases l)
   apply (auto simp: wpr_def)
  apply (simp add: refl_onD)
  apply (meson transE)
     apply (simp add: refl_onD)
  apply (simp add: refl_onD)
   apply (meson transE)
   apply (meson transE)
  done

lemma flip:
  assumes "env\<^sup>*\<^sup>* (m\<lbrakk>x \<^sub>@= PFO s\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>) m'"
  shows "env\<^sup>*\<^sup>* (m\<lbrakk>s \<^sub>t= []\<rbrakk>\<lbrakk>x \<^sub>@= PFO s\<rbrakk>) m'"
  using assms
  apply (subgoal_tac "m\<lbrakk>x \<^sub>@= PFO s\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk> = m\<lbrakk>s \<^sub>t= []\<rbrakk>\<lbrakk>x \<^sub>@= PFO s\<rbrakk>")
   apply simp
  apply (rule equality)
     apply auto
  done


lemma wpl_sound:
  assumes "trace m ts m'" "\<forall>t. sat t (wpl (r t) (g t) (tbuffers m t @ id_filter t ts) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>)" 
  assumes compat: "compat r g" 
  assumes refl: "\<forall>t. refl (r t) \<and> trans (r t)"
  shows "\<forall>t. sat t (wpl (r t) (g t) (tbuffers m' t) Q) (m'\<lbrakk>t \<^sub>t= []\<rbrakk>)"
  using assms(1,2)
proof (induct arbitrary: Q)
  case (nil a)
  then show ?case by auto
next
  case (step m s a m' ts m'')
  show ?case 
  proof (rule step(3), intro allI)
    fix t
    have a: "sat t (wpl (r t) (g t) (tbuffers m t @ id_filter t ((s, a) # ts)) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>)" 
      using step(4) by blast
    have t: "trans (r t)" "refl (r t)" using refl by auto

    show "sat t (wpl (r t) (g t) (tbuffers m' t @ id_filter t ts) Q) (m'\<lbrakk>t \<^sub>t= []\<rbrakk>)"
    proof (cases "t = s")
      case True
      show ?thesis using step(1)
      proof (cases)
        case (rd x v)
        show ?thesis using rd(3)
        proof (cases rule: get_split)
          case 1
          let ?Q="wpl (r s) (g s) (id_filter t ts) Q"
          have last: "lastf (isWX x) (tbuffers m s) = None" (is "lastf _ ?l = None")
            using 1 by (auto simp: buf_def split: option.splits event.splits)
                       (drule lastf_some; auto)+
          hence "wpl (r s) (g s) (?l @ [R x v]) ?Q \<subseteq> wpl (r s) (g s) (R x v # ?l) ?Q" (is "_ \<subseteq> ?P")
            by (rule reorder_rd_no_write)

          with a have "sat t ?P (m\<lbrakk>t \<^sub>t= []\<rbrakk>)"
            apply (simp add: wpl_concat[OF t, simplified True] wpr_wpl[OF t, simplified True] True rd del: wp.simps)
            apply (rule imp_sound)
             apply blast+
            done

          then show ?thesis using 1(1) t
            unfolding True rd
            apply simp
            unfolding sat_def wpr_def wpl_concat[OF t, simplified True]
            apply clarsimp
            apply (subgoal_tac "get\<^sub>s m x = get\<^sub>s m' x")
             apply (metis UNIV_I refl_on_def)
            apply (subgoal_tac "get\<^sub>s m x = get\<^sub>s (m\<lbrakk>s \<^sub>t= []\<rbrakk>) x")
             apply (metis envt_get\<^sub>s)
            unfolding get\<^sub>s_def
            by (auto split: option.splits event.splits pevent.splits)
        next
          case 2
          let ?Q="wpl (r s) (g s) (id_filter t ts) Q"
          have last: "lastf (isWX x) (tbuffers m s) = Some (W x v)" (is "lastf _ ?l = _")
            using 2 by (auto simp: buf_def split: option.splits event.splits)
                       (drule lastf_some; auto)+
          hence "wpl (r s) (g s) (?l @ [R x v]) ?Q \<subseteq> wpl (r s) (g s) ?l ?Q" (is "_ \<subseteq> ?P")
            using t[simplified True] by (rule reorder_rd_write)
          with a have "sat t ?P (m\<lbrakk>t \<^sub>t= []\<rbrakk>)"
            apply (simp add: wpl_concat[OF t, simplified True] wpr_wpl[OF t, simplified True] True rd del: wp.simps)
            apply (rule imp_sound)
            by blast+
          then show ?thesis unfolding True rd wpl_concat[OF t, simplified True] .
        qed
      next
        case mf
        then show ?thesis
          using a True 
          apply (simp del: wp.simps)
          apply (drule wpr_pres, insert refl, blast)
          by (simp add: wp_MF del: wp.simps)
      qed (insert a True, auto)
    next
      case False
      show ?thesis using step(1) a False
        apply cases
        apply (subgoal_tac "sat t (wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= W x v\<rbrakk>) t @ id_filter t ts) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>\<lbrakk>s \<^sub>q= W x v\<rbrakk>)")
              prefer 2
        using sat_tbuffer[OF False, where m="m\<lbrakk>t \<^sub>t= []\<rbrakk>" and Q="(wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= W x v\<rbrakk>) t @ id_filter t ts) Q)" and p="tbuffers m s@[W x v]" for x v]
              apply simp
             apply (simp add: fun_upd_twist)
            apply auto[2]
        apply (subgoal_tac "sat t (wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= FL x\<rbrakk>) t @ id_filter t ts) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>\<lbrakk>s \<^sub>q= FL x\<rbrakk>)")
              prefer 2
        using sat_tbuffer[OF False, where m="m\<lbrakk>t \<^sub>t= []\<rbrakk>" and Q="(wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= FL x\<rbrakk>) t @ id_filter t ts) Q)" and p="tbuffers m s@[FL x]" for x v]
        apply simp
             apply (simp add: fun_upd_twist)

        apply (subgoal_tac "sat t (wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= FO x\<rbrakk>) t @ id_filter t ts) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>\<lbrakk>s \<^sub>q= FO x\<rbrakk>)")
              prefer 2
        using sat_tbuffer[OF False, where m="m\<lbrakk>t \<^sub>t= []\<rbrakk>" and Q="(wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= FO x\<rbrakk>) t @ id_filter t ts) Q)" and p="tbuffers m s@[FO x]" for x v]
        apply simp
             apply (simp add: fun_upd_twist)
        apply (subgoal_tac "sat t (wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= SF\<rbrakk>) t @ id_filter t ts) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>\<lbrakk>s \<^sub>q= SF\<rbrakk>)")
              prefer 2
        using sat_tbuffer[OF False, where m="m\<lbrakk>t \<^sub>t= []\<rbrakk>" and Q="(wpl (r t) (g t) (tbuffers (m\<lbrakk>s \<^sub>q= SF\<rbrakk>) t @ id_filter t ts) Q)" and p="tbuffers m s@[SF]" for x v]
        apply simp
        apply (simp add: fun_upd_twist)
        done
    qed
  qed
next
  case (env m m' t m'')
  then show ?case using sat_env_stable 
    by (metis (no_types, lifting) env_tbuffer env_tbuffer_orth fold_congs(3)) 
next
  case (prp m s a m' ts m'')
  have s: "sat s (wpl (r s) (g s) (tbuffers m s @ id_filter s ts) Q) (m\<lbrakk>s \<^sub>t= []\<rbrakk>)" using prp(4) by blast
  with prp(1) have g: "sat s (guar a (g s)) (m\<lbrakk>s \<^sub>t= []\<rbrakk>)" 
    apply cases
       apply clarsimp
       apply (drule wpr_pres, insert refl, blast)
    apply (auto simp: sat_def)
    done

  show ?case
  proof (rule prp(3), intro allI)
    fix t
    have a: "sat t (wpl (r t) (g t) (tbuffers m t @ id_filter t ts) Q) (m\<lbrakk>t \<^sub>t= []\<rbrakk>)" using prp(4) by blast
    have t: "trans (r t)" "refl (r t)" using refl by auto

    show "sat t (wpl (r t) (g t) (tbuffers m' t @ id_filter t ts) Q) (m'\<lbrakk>t \<^sub>t= []\<rbrakk>)"
    proof (cases "t = s")
      case True
      show ?thesis using prp(1)
      proof (cases)
        case (prpw x v p)
        show ?thesis using a unfolding prpw True simple wpl.simps
          apply -
          apply (drule wpr_pres, insert refl, blast)
          unfolding sat_def squash apply (intro allI impI)
          apply (elim envt_buffer_appE)
            apply simp
            prefer 3
            apply simp
           prefer 2
          apply simp
          sorry (* Need to show that Q |- Q[None/x_b] *)
      next
        case (prpfl x p)
        hence "buffers (m\<lbrakk>s \<^sub>t= []\<rbrakk>) x = []" by auto
        hence "\<forall>m'. env\<^sup>*\<^sup>* (m\<lbrakk>s \<^sub>t= []\<rbrakk>) m' \<longrightarrow> buffers m' x = []" 
          using envt_buffer_empty by metis
        then show ?thesis using a True prpfl
          apply (simp)
          apply (drule wpr_pres, insert refl, blast)
          by (auto simp: sat_def)
      next
        case (prpfo b\<^sub>1 x b\<^sub>2)

        let ?Q="wpl (r t) (g t) (b\<^sub>2 @ id_filter t ts) Q"
        have "wpl (r t) (g t) (b\<^sub>1 @ [FO x]) ?Q \<subseteq> wpl (r t) (g t) (FO x # b\<^sub>1) ?Q" (is "_ \<subseteq> ?P")
          by (rule reorder_fo)
        
        with a have "sat t ?P (m\<lbrakk>t \<^sub>t= []\<rbrakk>)"
          apply (simp add: wpl_concat[OF t, simplified True] wpr_wpl[OF t, simplified True] True prpfo del: wp.simps)
          apply (rule imp_sound)
           apply blast+
          done
        then show ?thesis unfolding prpfo True wpl.simps
          apply (simp del: wp.simps)
          apply (drule wpr_pres, insert refl, blast)
          unfolding wpl_concat[OF t, simplified True]
          unfolding sat_def apply (intro allI impI)
          apply (drule flip)
          apply (elim envt_buffer_appE)
            apply auto[2]
          apply simp
          by (metis (no_types, lifting) fun_upd_triv get\<^sub>f_no_pw get\<^sub>s_no_pw list.set_cases list.simps(3))
      next
        case (prpsf p)
        hence "\<forall>y. PFO s \<notin> set (buffers (m\<lbrakk>t \<^sub>t= []\<rbrakk>) y)" by auto
        hence "\<forall>y m'. env\<^sup>*\<^sup>* (m\<lbrakk>t \<^sub>t= []\<rbrakk>) m' \<longrightarrow> PFO s \<notin> set (buffers m' y)" 
          by (meson envt_buffer_subset in_mono)
        then show ?thesis using a True prpsf
          apply (simp)
          apply (drule wpr_pres, insert refl, blast)
          by (auto simp: sat_def)
      qed
    next
      case False
      hence "g s \<subseteq> r t" using assms by (auto simp: compat_def)
      hence "guar a (g s) \<subseteq> guar a (r t)" by (rule guar_mono)
      hence g: "sat s (guar a (r t)) (m\<lbrakk>s \<^sub>t= []\<rbrakk>)" 
        using g imp_sound by metis
      hence g: "sat s (guar a (r t)) (m\<lbrakk>t \<^sub>t= []\<rbrakk>)" 
        unfolding sat_def  apply (cases a; clarsimp)
        apply (elim envt_tupdE)
        apply (drule envt_tbuffer_orth[where s=s and p="[]"])
        apply (subgoal_tac "((get\<^sub>s (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>), persistent (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>), f), (get\<^sub>s (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>))(x11 := x12), persistent (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>), f) \<in> r t \<and> ((get\<^sub>s (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>), persistent (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>), f), (get\<^sub>s (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>))(x11 := x12), (persistent (m'\<lbrakk>t \<^sub>t= tbuffers m t\<rbrakk>\<lbrakk>s \<^sub>t= []\<rbrakk>))(x11 := x12), f(x11 := x12)) \<in> r t")
        prefer 2
        apply blast
        unfolding get\<^sub>s_app_simps''
         apply simp
        done
      have s: "\<langle>m\<lbrakk>t \<^sub>t= []\<rbrakk>\<rangle> -s,a\<leadsto> \<langle>m'\<lbrakk>t \<^sub>t= []\<rbrakk>\<rangle>" 
        using prp(1) False 
        apply (cases; clarsimp)
        apply (rule prpwI)
        apply auto[1]
           apply (rule equality; auto)
        apply (rule prpflI)
        apply auto[2]
           apply (rule equality; auto)
        apply (rule prpfoI)
        apply auto[2]
           apply (rule equality; auto)
        apply (rule prpsfI)
        apply auto[2]
           apply (rule equality; auto)
        done
      have [simp]: "tbuffers m t = tbuffers m' t"
        using prp(1) False by cases auto
      show ?thesis using refl a wpr_sound[OF s g False]
        by (cases "tbuffers m' t @ id_filter t ts") auto
    qed
  qed
qed

end