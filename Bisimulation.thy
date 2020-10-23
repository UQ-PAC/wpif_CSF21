theory Bisimulation
  imports Execution 
begin

(* Need to expand to all traces *)

locale bisimulation = execution eval
  for eval :: "'a \<Rightarrow> 's rel"

context bisimulation
begin

type_synonym 'b state = "('b \<times> 'b) set"
type_synonym 'b step = "('b \<times> 'b) rel"

definition stable :: "'s state \<Rightarrow> 's step \<Rightarrow> bool" where
  "stable \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f \<longrightarrow> (x, y) \<in> g \<longrightarrow> y \<in> f)"

(* Apply a step to a set of states *)
definition trans :: "'s state \<Rightarrow> 's step \<Rightarrow> 's state" ("_+[_]") 
  where "trans P R \<equiv> {t. \<exists>s. s \<in> P \<and> (s, t) \<in> R}"

(* Lift an action to a set of steps *)
definition lift\<^sub>a :: "'a \<Rightarrow> 's step" where
  "lift\<^sub>a \<alpha> \<equiv> {((m\<^sub>1,m\<^sub>2),(m\<^sub>1',m\<^sub>2')). (m\<^sub>1,m\<^sub>1') \<in> eval \<alpha> \<and> (m\<^sub>2,m\<^sub>2') \<in> eval \<alpha>}"

(* Lift a set of states to a set of steps it could perform *)
definition lift\<^sub>P :: "'s state \<Rightarrow> 's step" where
  "lift\<^sub>P P \<equiv> {((m\<^sub>1,m\<^sub>2),(m\<^sub>1',m\<^sub>2')). (m\<^sub>1,m\<^sub>2) \<in> P}"

definition progress :: "'s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool" where
  "progress m\<^sub>1 m\<^sub>2 \<alpha> \<equiv> (\<exists>m\<^sub>1'. (m\<^sub>1, m\<^sub>1') \<in> eval \<alpha>) \<longrightarrow> (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> eval \<alpha>)"

definition bisim_act :: "'s state \<Rightarrow> 'a \<Rightarrow> bool" where
  "bisim_act P \<alpha> \<equiv> \<forall>(m\<^sub>1,m\<^sub>2) \<in> P. progress m\<^sub>1 m\<^sub>2 \<alpha> \<and> progress m\<^sub>2 m\<^sub>1 \<alpha>"

inductive rules :: 
  "'s step \<Rightarrow> 's step \<Rightarrow> 's state \<Rightarrow> 'a Stmt \<Rightarrow> 's state \<Rightarrow> bool"
  ("_,_ \<turnstile>\<^sub>s _ {_} _" [20, 20, 20, 20] 20)
where
  skip [intro]:     "stable P R \<Longrightarrow> R,G \<turnstile>\<^sub>s P { Skip } P" |
  seq [intro]:      "R,G \<turnstile>\<^sub>s P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>s Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>1 ;; c\<^sub>2 } M" |
  choice [intro]:   "R,G \<turnstile>\<^sub>s P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  loop [intro]:     "stable P R \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c } P \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c* } P" |
  act [intro]:      "stable P R \<Longrightarrow> stable Q R \<Longrightarrow> lift\<^sub>P P \<inter> lift\<^sub>a \<alpha> \<subseteq> G \<Longrightarrow> P+[lift\<^sub>a \<alpha>] \<subseteq> Q \<Longrightarrow> bisim_act P \<alpha> \<Longrightarrow>
                      R,G \<turnstile>\<^sub>s P { Basic \<alpha> } Q" |
  rewrite [intro]:  "R,G \<turnstile>\<^sub>s P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                      R',G' \<turnstile>\<^sub>s P' { c } Q'" |
  parallel [intro]: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 ==> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow>
                      R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } Q\<^sub>1 \<inter> Q\<^sub>2"

lemma stableI [intro]:
  assumes "stable P R" "R' \<subseteq> R"
  shows "stable P R'"
  using assms by (auto simp: stable_def)

lemma stable_conj [intro]:
  assumes "stable P R" "stable P' R'"
  shows "stable (P \<inter> P') (R \<inter> R')"
  using assms by (auto simp: stable_def)

lemma lift\<^sub>P_conj [simp]:
  shows "lift\<^sub>P (P \<inter> M) = lift\<^sub>P P \<inter> lift\<^sub>P M"
  by (auto simp: lift\<^sub>P_def)

lemma bisim_act_imp [intro]:
  assumes "bisim_act P \<alpha>" "Q \<subseteq> P"
  shows "bisim_act Q \<alpha>"
  using assms by (auto simp: bisim_act_def)

lemma stable_trans:
  assumes "stable M R"
  shows "M+[R] \<subseteq> M"
  using assms by (auto simp: stable_def trans_def)

lemma trans_conj [intro]:
  assumes "P+[R] \<subseteq> Q" "P'+[R] \<subseteq> Q'"
  shows "(P \<inter> P')+[R] \<subseteq> Q \<inter> Q'"
  using assms by (auto simp: trans_def)

lemma frame_act:
  assumes "stable M G"
  assumes "lift\<^sub>P P \<inter> lift\<^sub>a \<alpha> \<subseteq> G"
  assumes "P+[lift\<^sub>a \<alpha>] \<subseteq> Q"
  shows "(P \<inter> M)+[lift\<^sub>a \<alpha>] \<subseteq> (M \<inter> Q)"
  using assms
  by (auto simp: stable_def lift\<^sub>P_def lift\<^sub>a_def trans_def, blast+)

lemma false:
  shows "R,G \<turnstile>\<^sub>s {} { c } {}" 
proof (induct c arbitrary: R G)
  case Skip
  hence "stable {} R" by (auto simp: stable_def)
  thus ?case by auto
next
  case (Basic x)
  then show ?case 
  proof (intro act)
    show "stable {} R" by (auto simp: stable_def)
    show "stable {} R" by (auto simp: stable_def)
    show "lift\<^sub>P {} \<inter> lift\<^sub>a x \<subseteq> G" by (auto simp: lift\<^sub>P_def)
    show "{}+[lift\<^sub>a x] \<subseteq> {}" by (auto simp: trans_def)
    show "bisim_act {} x" by (auto simp: bisim_act_def)
  qed
next
  case (Seq c1 c2)
  then show ?case by blast
next
  case (Choice c1 c2)
  then show ?case by auto
next
  case (Loop c)
  hence "stable {} R" by (auto simp: stable_def)
  then show ?case using Loop by auto
next
  case (Parallel c1 c2)
  hence "(G \<union> R,R \<inter> G \<turnstile>\<^sub>s {} {c1} {}) \<and> (R,R \<inter> G \<union> G \<inter> G \<turnstile>\<^sub>s {} {c2} {})"
    by (meson)
  then show ?case by auto
qed

subsection \<open>Elimination Rules\<close>

lemma skipE [elim]:
  assumes "R,G \<turnstile>\<^sub>s P {Skip} Q"
  obtains M where "stable M R" "P \<subseteq> M" "M \<subseteq> Q"
  using assms
  by (induct R G P "Skip :: 'a Stmt" Q rule: rules.induct) blast+

lemma seqE [elim]:
  assumes "R,G \<turnstile>\<^sub>s P {c\<^sub>1 ;; c\<^sub>2} Q"
  obtains M where "R,G \<turnstile>\<^sub>s P {c\<^sub>1} M" "R,G \<turnstile>\<^sub>s M {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 ;; c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+

lemma choiceE [elim]:
  assumes "R,G \<turnstile>\<^sub>s P {c\<^sub>1 \<sqinter> c\<^sub>2} Q"
  obtains "R,G \<turnstile>\<^sub>s P {c\<^sub>1} Q" "R,G \<turnstile>\<^sub>s P {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 \<sqinter> c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) auto

lemma loopE [elim]:
  assumes "R,G \<turnstile>\<^sub>s P { c* } Q"
  obtains I where "P \<subseteq> I" "R,G \<turnstile>\<^sub>s I { c } I" "I \<subseteq> Q" "stable I R"
  using assms 
proof (induct R G P "c*" Q arbitrary: c)
  case (loop R G P c)
  then show ?case by blast
next
  case (rewrite R G P Q P' R' G' Q')
  then show ?case by (smt order_refl rules.rewrite stableI subset_trans)
qed

lemma actE [elim]:
  assumes "R,G \<turnstile>\<^sub>s P { Basic \<alpha> } Q"
  obtains P' Q' where "P \<subseteq> P'" "Q' \<subseteq> Q" "stable P' R" "stable Q' R" "lift\<^sub>P P' \<inter> lift\<^sub>a \<alpha> \<subseteq> G" "P'+[lift\<^sub>a \<alpha>] \<subseteq> Q'" "bisim_act P' \<alpha>"
  using assms 
proof (induct R G P "Basic \<alpha>" Q)
  case (act P R Q G)
  then show ?case by blast
next
  case (rewrite R G P Q P' R' G' Q')
  then show ?case by (meson stableI subset_trans)
qed

lemma parallelE [elim]:
  assumes "R,G \<turnstile>\<^sub>s P { c\<^sub>1 || c\<^sub>2 } Q"
  obtains R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where  "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
    "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
  using assms
proof (induct R G P "c\<^sub>1 || c\<^sub>2" Q)
  case (rewrite R G P Q P' R' G' Q')
  show ?case
  proof (rule rewrite(2), goal_cases)
    case (1 R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
    then show ?case using rewrite(3,4,5,6) rewrite(7)[OF 1(1,2)] by blast
  qed
next
  case (parallel R\<^sub>1 G\<^sub>2 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 P\<^sub>2 Q\<^sub>2)
  then show ?case by (smt Int_lower2 inf_mono inf_sup_absorb order_refl sup_commute)
qed

lemma parallelI [intro]:
  assumes "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
    "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
  shows "R,G \<turnstile>\<^sub>s P { c\<^sub>1 || c\<^sub>2 } Q"
  using assms by (meson parallel rules.rewrite)

subsection \<open>Introduction Rules\<close>

lemma frameI [intro]:
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  assumes "stable M R\<^sub>2" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>s P \<inter> M {c} Q \<inter> M"
  using assms
proof (induct arbitrary: M)
  case (skip P R G)
  then show ?case 
    by (smt IntI Int_lower1 Int_lower2 bisimulation.skip stable_def subset_eq) 
next
  case (act P R Q \<alpha> G)
  show ?case
  proof (rule rules.act)
    have "stable M G"
      using act by blast
    thus "(P \<inter> M)+[lift\<^sub>a \<alpha>] \<subseteq> Q \<inter> M"
      using act(3,4) frame_act by auto
  qed (insert act, auto)
next
  case (parallel R\<^sub>1 G\<^sub>2 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  then show ?case 
    by (metis (no_types, lifting) inf_assoc rules.parallel sup.absorb_iff1 sup.bounded_iff sup_inf_distrib2)
qed blast+

lemma rwI [intro]:
  assumes "c \<leadsto> c'"
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  shows "R,G \<turnstile>\<^sub>s P {c'} Q"
  using assms
proof (induct arbitrary: R G P Q)
  case (par1 c\<^sub>1 c\<^sub>1' c\<^sub>2)
  then obtain R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where a: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
      "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
    by auto
  hence "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1' } Q\<^sub>1" using par1 by auto
  then show ?case using a by blast
next
  case (par2 c\<^sub>2 c\<^sub>2' c\<^sub>1)
  then obtain R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where a: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
      "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
    by auto
  hence "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2' } Q\<^sub>2" using par2 by auto
  then show ?case using a by blast
next
  case (parE1 c)
  then obtain R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where a: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { Skip } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c } Q\<^sub>2"
      "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
    by auto
  then obtain M where "stable M R\<^sub>1" "P\<^sub>1 \<subseteq> M" "M \<subseteq> Q\<^sub>1" by auto
  then show ?case using a by blast
next
  case (parE2 c)
  then obtain R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where a: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { Skip } Q\<^sub>2"
      "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
    by auto
  then obtain M where "stable M R\<^sub>2" "P\<^sub>2 \<subseteq> M" "M \<subseteq> Q\<^sub>2" by auto
  then show ?case using a by blast
next
  case (loop c n)
  then obtain I where s: "P \<subseteq> I" "R,G \<turnstile>\<^sub>s I {c} I" "I \<subseteq> Q" "stable I R" by auto
  hence "R,G \<turnstile>\<^sub>s I {unroll n c} I" by (induct n) auto
  then show ?case using s by blast
qed fast+

lemma multi_rwI [intro]:
  assumes "c \<mapsto>[]\<^sup>* c'"
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  shows "R,G \<turnstile>\<^sub>s P {c'} Q"
  using assms by (induct c "[] :: 'a Trace" c') auto

lemma precontext_stable:
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  obtains P' where "P \<subseteq> P'" "stable P' R" "R,G \<turnstile>\<^sub>s P' {c} Q"
  using assms 
proof (induct)
  case (skip P R G)
  then show ?case by blast
next
  case (seq R G P c\<^sub>1 Q c\<^sub>2 M)
  then show ?case by blast
next
  case (choice R G P c\<^sub>1 Q c\<^sub>2)
  show ?case
  proof (rule choice(2), rule choice(4),  goal_cases)
    case (1 P' P'')
    have a: "stable (P' \<inter> P'') R" using 1 by auto
    have b: "P \<subseteq> P' \<inter> P''" using 1 by auto
    then show ?case using 1 choice(5)[OF b a] by blast
  qed
next
  case (loop P R G c)
  then show ?case by auto
next
  case (act P R Q \<alpha> G)
  then show ?case by auto
next
  case (rewrite R G P c Q P' R' G' Q')
  then show ?case by blast
next
  case (parallel R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case
  proof (rule parallel(2), rule parallel(4), goal_cases)
    case (1 P' P'')
    then show ?case using parallel(7)[of "P' \<inter> P''"] parallel(5,6) by blast
  qed
qed 

lemma progI [intro]:
  assumes "c \<mapsto>\<^sub>\<alpha> c'"
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  shows "R,G \<turnstile>\<^sub>s P {Basic \<alpha> ;; c'} Q"
  using assms
proof (induct arbitrary: R G P Q)
  case (act \<alpha>)
  then obtain P' Q' where a: "P \<subseteq> P'" "Q' \<subseteq> Q" "stable P' R" "stable Q' R" 
      "lift\<^sub>P P' \<inter> lift\<^sub>a \<alpha> \<subseteq> G" "P'+[lift\<^sub>a \<alpha>] \<subseteq> Q'" "bisim_act P' \<alpha>"
    by auto
  hence "R,G \<turnstile>\<^sub>s Q' {Skip} Q" by auto
  moreover have "R,G \<turnstile>\<^sub>s P {Basic \<alpha>} Q'" using a by blast
  ultimately show ?case by auto
next
  case (seq c\<^sub>1 \<alpha> c\<^sub>1' c\<^sub>2)
  then obtain M where a: "R,G \<turnstile>\<^sub>s P {c\<^sub>1} M" "R,G \<turnstile>\<^sub>s M {c\<^sub>2} Q"
    by auto
  hence "R,G \<turnstile>\<^sub>s P {Basic \<alpha> ;; c\<^sub>1'} M" using seq by auto
  then show ?case using a(2) by auto
next
  case (par1 c\<^sub>1 \<alpha> c\<^sub>1' c\<^sub>2)
  then obtain R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where a: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
      "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
    by auto
  then obtain M where b: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 {Basic \<alpha>} M" "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s M {c\<^sub>1'} Q\<^sub>1" using par1 by force
  obtain P' where c: "P\<^sub>2 \<subseteq> P'" "stable P' R\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P' {c\<^sub>2} Q\<^sub>2" 
    using a(2) precontext_stable by metis 
  have "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>1 \<inter> P\<^sub>2 {Basic \<alpha>} M \<inter> P'"
    using frameI[OF b(1) c(2) a(7)] c(1) by blast
  moreover have "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>s M \<inter> P' {c\<^sub>1' || c\<^sub>2} Q\<^sub>1 \<inter> Q\<^sub>2" 
    using b(2) c(3) a(7,8) by blast
  ultimately show ?case using a(3,4,5,6) by blast
next
  case (par2 c\<^sub>2 \<alpha> c\<^sub>2' c\<^sub>1)
  then obtain R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where a: "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
      "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
    by auto
  then obtain M where b: "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>2 {Basic \<alpha>} M" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>s M {c\<^sub>2'} Q\<^sub>2" using par2 by force
  obtain P' where c: "P\<^sub>1 \<subseteq> P'" "stable P' R\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>s P' {c\<^sub>1} Q\<^sub>1" 
    using a(1) precontext_stable by metis 
  have "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>s P\<^sub>1 \<inter> P\<^sub>2 {Basic \<alpha>} M \<inter> P'"
    using frameI[OF b(1) c(2) a(8)] c(1) by blast
  moreover have "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>s M \<inter> P' {c\<^sub>1 || c\<^sub>2'} Q\<^sub>1 \<inter> Q\<^sub>2" 
    using b(2) c(3) a(7,8) by blast
  ultimately show ?case using a(3,4,5,6) by blast
qed

lemma multi_progI [intro]:
  assumes "c \<mapsto>[\<alpha>]\<^sup>* c'"
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  shows "R,G \<turnstile>\<^sub>s P {Basic \<alpha> ;; c'} Q"
  using assms
proof (induct c "[\<alpha>]" c' arbitrary: R G P Q)
  case (rewrite c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case by blast
next
  case (prepend c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case by (meson multi_rwI seqE progI seq)
qed

fun trace_prog
  where "trace_prog [] = Skip" | "trace_prog (\<alpha>#t) = Basic \<alpha> ;; trace_prog t"

lemma trace_progI:
  assumes "c \<mapsto>t\<^sup>* c'"
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  shows "R,G \<turnstile>\<^sub>s P {trace_prog t ;; c'} Q"
  using assms
proof (induct c t c' arbitrary: R G P Q)
  case (lift c)
  then obtain M where "R,G \<turnstile>\<^sub>s M { c  } Q" "P \<subseteq> M" "stable M R"
    by (meson precontext_stable)
  then show ?case by (smt rewrite seq skip trace_prog.simps(1) subset_refl)
next
  case (rewrite c\<^sub>1 c\<^sub>2 t c\<^sub>3)
  then show ?case by blast
next
  case (prepend c\<^sub>1 \<alpha> c\<^sub>2 t c\<^sub>3)
  hence "R,G \<turnstile>\<^sub>s P {Basic \<alpha> ;; c\<^sub>2} Q" using multi_progI by auto
  then obtain M where c: "R,G \<turnstile>\<^sub>s P {Basic \<alpha>} M" "R,G \<turnstile>\<^sub>s M {c\<^sub>2} Q" by auto
  hence "R,G \<turnstile>\<^sub>s M {trace_prog t ;; c\<^sub>3} Q" using prepend by auto
  then show ?case using c(1) by (smt trace_prog.simps(2) local.seqE rules.seq)
qed

lemma bisim_act:
  assumes "(m\<^sub>1,m\<^sub>1') \<in> eval \<alpha>"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> P"
  assumes "P+[lift\<^sub>a \<alpha>] \<subseteq> Q"
  assumes "bisim_act P \<alpha>"
  obtains m\<^sub>2' where "(m\<^sub>2, m\<^sub>2') \<in> eval \<alpha>" "(m\<^sub>1',m\<^sub>2') \<in> Q"
proof -
  have "progress m\<^sub>1 m\<^sub>2 \<alpha> \<and> progress m\<^sub>2 m\<^sub>1 \<alpha>"
    using assms(2,4) by (auto simp: bisim_act_def)
  then obtain m\<^sub>2' where "(m\<^sub>2, m\<^sub>2') \<in> eval \<alpha>"
    using assms(1) by (auto simp: progress_def)
  moreover have "(m\<^sub>1',m\<^sub>2') \<in> Q"
    using calculation assms(1,2,3) by (auto simp: lift\<^sub>a_def trans_def)
  ultimately show ?thesis using that by blast
qed

lemma info_type_progE:
  assumes "c \<mapsto>[\<alpha>]\<^sup>* c'"
  assumes "R,G \<turnstile>\<^sub>s P {c} Q"
  obtains M where "lift\<^sub>P P \<inter> lift\<^sub>a \<alpha> \<subseteq> G" "P+[lift\<^sub>a \<alpha>] \<subseteq> M" "bisim_act P \<alpha>" "R,G \<turnstile>\<^sub>s M {c'} Q"
proof -
  have "R,G \<turnstile>\<^sub>s P {Basic \<alpha> ;; c'} Q" using assms multi_progI by auto
  then obtain M where c: "R,G \<turnstile>\<^sub>s P {Basic \<alpha>} M" "R,G \<turnstile>\<^sub>s M {c'} Q" by auto
  then obtain P' M' where b: "P \<subseteq> P'" "M' \<subseteq> M" "stable P' R" "stable M' R" "lift\<^sub>P P' \<inter> lift\<^sub>a \<alpha> \<subseteq> G" 
    "P'+[lift\<^sub>a \<alpha>] \<subseteq> M'" "bisim_act P' \<alpha>"
    by auto
  have "lift\<^sub>P P \<inter> lift\<^sub>a \<alpha> \<subseteq> G" using b unfolding lift\<^sub>P_def lift\<^sub>a_def by auto
  moreover have "P+[lift\<^sub>a \<alpha>] \<subseteq> M" using b unfolding lift\<^sub>P_def lift\<^sub>a_def trans_def by blast
  moreover have "bisim_act P \<alpha>" using b by auto
  ultimately show ?thesis using that c by auto
qed

lemma bisim:
  assumes "\<langle>c,m\<^sub>1\<rangle> \<rightarrow>t\<^sup>* \<langle>c\<^sub>1,m\<^sub>1'\<rangle>"
  assumes "R,G \<turnstile>\<^sub>s P { c } Q"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> P"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> \<L>"
  assumes "stable \<L> G"
  obtains m\<^sub>2' c\<^sub>2 where "\<langle>c,m\<^sub>2\<rangle> \<rightarrow>t\<^sup>* \<langle>c\<^sub>2,m\<^sub>2'\<rangle>" "(m\<^sub>1',m\<^sub>2') \<in> \<L>"
  using assms(1) unfolding ev_def
proof 
  assume "trace_mem m\<^sub>1 t m\<^sub>1'" "c \<mapsto>t\<^sup>* c\<^sub>1" 
  hence "\<exists>m\<^sub>2' c\<^sub>2. \<langle>c,m\<^sub>2\<rangle> \<rightarrow>t\<^sup>* \<langle>c\<^sub>2,m\<^sub>2'\<rangle> \<and> (m\<^sub>1',m\<^sub>2') \<in> \<L>" 
    using assms(2,3,4)
  proof (induct m\<^sub>1 t m\<^sub>1' arbitrary: P m\<^sub>2 c rule: trace_mem.induct)
    case (1 m)
    then show ?case by (meson ev_def trace_mem.intros(1))
  next
    case (2 m'' m \<alpha> t m')
    then obtain c' where f1: "c \<mapsto>[\<alpha>]\<^sup>* c'" "c' \<mapsto>t\<^sup>* c\<^sub>1" by auto
    obtain M where f2: "lift\<^sub>P P \<inter> lift\<^sub>a \<alpha> \<subseteq> G" "P+[lift\<^sub>a \<alpha>] \<subseteq> M" "bisim_act P \<alpha>" "R,G \<turnstile>\<^sub>s M {c'} Q"
      using info_type_progE[OF f1(1) 2(5)] by metis
    obtain m\<^sub>2' where f3: "(m\<^sub>2, m\<^sub>2') \<in> eval \<alpha>" "(m, m\<^sub>2') \<in> M"
      using f2 bisim_act[OF 2(1,6)] by blast
    have "((m'', m\<^sub>2), (m, m\<^sub>2')) \<in> G" using "2.hyps"(1) "2.prems"(3) f2(1) f3(1)
      unfolding lift\<^sub>P_def lift\<^sub>a_def by auto
    hence "(m,m\<^sub>2') \<in> \<L>" using 2(7) assms(5) by (meson stable_def)
    hence "\<exists>m\<^sub>2'' c\<^sub>2. \<langle>c',m\<^sub>2'\<rangle> \<rightarrow>t\<^sup>* \<langle>c\<^sub>2,m\<^sub>2''\<rangle> \<and> (m',m\<^sub>2'') \<in> \<L>" 
      using 2(3)[OF f1(2) f2(4) f3(2)] by auto
    then show ?case using f3(1) 2(4) by (meson ev_def trace_mem.intros(2))
  qed
  thus ?thesis using that by auto
qed

end

end
