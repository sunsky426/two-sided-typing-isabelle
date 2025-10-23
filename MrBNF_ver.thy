theory MrBNF_ver
  imports Binders.MRBNF_Recursor "Case_Studies.FixedCountableVars"
begin

datatype "type" = 
    Nat
  | Prod "type" "type"
  | To "type" "type"
  | OnlyTo "type" "type"
  | Ok

typedef 'a :: infinite dpair = "{(x::'a,y). x \<noteq> y}"
  unfolding mem_Collect_eq split_beta
  by (metis (full_types) arb_element finite.intros(1) finite_insert fst_conv insertI1 snd_conv)

setup_lifting type_definition_dpair

lift_definition dfst :: "'a :: infinite dpair \<Rightarrow> 'a" is fst .
lift_definition dsnd :: "'a :: infinite dpair \<Rightarrow> 'a" is snd .
lift_definition dmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a :: infinite dpair \<Rightarrow> 'a :: infinite dpair" is
  "\<lambda>f (x, y). if bij f then (f x, f y) else (x, y)"
  by (auto split: if_splits simp: bij_implies_inject)
lift_definition dset :: "'a :: infinite dpair \<Rightarrow> 'a set" is "\<lambda>(a,b). {a, b}" .

mrbnf "'a :: var dpair"
  map: dmap
  sets: bound: dset
  bd: natLeq
  subgoal
    by (rule ext, transfer) auto
  subgoal
    by (rule ext, transfer) auto
  subgoal
    by (transfer) auto
  subgoal
    by (rule ext, transfer) auto
  subgoal
    by (rule infinite_regular_card_order_natLeq)
  subgoal
    by transfer (auto simp flip: finite_iff_ordLess_natLeq)
  subgoal
    by blast
  subgoal
    unfolding UNIV_I[THEN eqTrueI] simp_thms
    by transfer auto
  done

binder_datatype 'var "term" = 
  Zero
  | Succ "'var term"
  | Pred "'var term"
  | If "'var term" "'var term" "'var term"
  | Var 'var
  | App "'var term" "'var term"
  | Fix f::'var x::'var M::"'var term" binds f x in M
  | Pair "'var term" "'var term"
  | Let "(xy::'var) dpair" M::"'var term" N::"'var term" binds xy in N

definition usubst ("_[_ <- _]" [1000, 49, 49] 1000) where
  "usubst t u x = tvsubst_term (Var(x := u)) t"

lemma SSupp_term_fun_upd: "SSupp_term (Var(x :: 'var :: var := u)) \<subseteq> {x}"
  by (auto simp: SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def Var_def)

lemma IImsupp_term_fun_upd: "IImsupp_term (Var(x :: 'var :: var := u)) \<subseteq> {x} \<union> FVars_term u"
  by (auto simp: IImsupp_term_def SSupp_term_def tvVVr_tvsubst_term_def tv\<eta>_term_tvsubst_term_def Var_def)

lemma SSupp_term_fun_upd_bound[simp]:
  "|SSupp_term (Var(x :: 'var :: var := u))| <o |UNIV :: 'var set|"
  by (meson SSupp_term_fun_upd card_of_mono1 emp_bound infinite_UNIV insert_bound
      ordLeq_ordLess_trans)

lemma usubst_simps[simp]:
  "usubst Zero u y = Zero"
  "usubst (Succ t) u y = Succ (usubst t u y)"
  "usubst (Pred t) u y = Pred (usubst t u y)"
  "usubst (If t1 t2 t3) u y = If (usubst t1 u y) (usubst t2 u y) (usubst t3 u y)"
  "usubst (Var x) u y = (if x = y then u else Var x)"
  "usubst (App t1 t2) u y = App (usubst t1 u y) (usubst t2 u y)"
  "f \<noteq> y \<Longrightarrow> f \<notin> FVars_term u \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> FVars_term u \<Longrightarrow>
   usubst (Fix f x t) u y = Fix f x (usubst t u y)"
  "usubst (Pair t1 t2) u y = Pair (usubst t1 u y) (usubst t2 u y)"
  "y \<notin> dset xy \<Longrightarrow> dset xy \<inter> FVars_term u = {} \<Longrightarrow> dset xy \<inter> FVars_term t1 = {} \<Longrightarrow>
  usubst (term.Let xy t1 t2) u y = term.Let xy (usubst t1 u y) (usubst t2 u y)"
  unfolding usubst_def using IImsupp_term_fun_upd
  by (subst term.subst; fastforce)+

inductive num :: "'var::var term \<Rightarrow> bool" where
  "num Zero"
| "num n \<Longrightarrow> num (Succ n)"

inductive val :: "'var::var term \<Rightarrow> bool" where
  "val (Var x)"
| "num n \<Longrightarrow> val n"
| "val V \<Longrightarrow> val W \<Longrightarrow> val (Pair V W)"
| "val (Fix f x M)"

inductive stuckExp :: "'var::var term \<Rightarrow> bool" where
  "\<lbrakk> val V ; \<not> num V \<rbrakk> \<Longrightarrow> stuckExp (Pred V)"
| "\<lbrakk> val V ; \<not> num V \<rbrakk> \<Longrightarrow> stuckExp (Succ V)"
| "\<lbrakk> val V ; \<not> num V \<rbrakk> \<Longrightarrow> stuckExp (If V _ _)"
| "\<lbrakk> val V ; V \<noteq> Fix _ _ _ \<rbrakk> \<Longrightarrow> stuckExp (App V M)"
| "\<lbrakk> val V ; V \<noteq> Pair _ _ \<rbrakk> \<Longrightarrow> stuckExp (Let x V M)"

inductive stuck :: "'var::var term \<Rightarrow> bool" where
  "stuckExp M \<Longrightarrow> stuck M"
| "stuck N \<Longrightarrow> stuck (App (Fix f x M) N)"
| "stuck M \<Longrightarrow> stuck (App M N)"
| "stuck M \<Longrightarrow> stuck (Succ M)"
| "stuck M \<Longrightarrow> stuck (Pred M)"
| "stuck M \<Longrightarrow> stuck (Pair M N)"
| "val V \<Longrightarrow> stuck N \<Longrightarrow> stuck (Pair V N)"
| "stuck M \<Longrightarrow> stuck (Let x M N)"
| "stuck M \<Longrightarrow> stuck (If M N P)"

inductive beta :: "'var::var term \<Rightarrow> 'var::var term \<Rightarrow> bool"  (infix "\<rightarrow>" 70) where
  OrdApp2: "N \<rightarrow> N' \<Longrightarrow> App (Fix f x M) N \<rightarrow> App (Fix f x M) N'"
| OrdApp1: "M \<rightarrow> M' \<Longrightarrow> App M N \<rightarrow> App M' N"
| OrdSucc: "M \<rightarrow> M' \<Longrightarrow> Succ M \<rightarrow> Succ M'"
| OrdPred: "M \<rightarrow> M' \<Longrightarrow> Pred M \<rightarrow> Pred M'"
| OrdPair1: "M \<rightarrow> M' \<Longrightarrow> Pair M N \<rightarrow> Pair M' N"
| OrdPair2: "val V \<Longrightarrow> N \<rightarrow> N' \<Longrightarrow> Pair V N \<rightarrow> Pair V N'"
| OrdLet: "M \<rightarrow> M' \<Longrightarrow> Let xy M N \<rightarrow> Let xy M' N"
| OrdIf: "M \<rightarrow> M' \<Longrightarrow> If M N P \<rightarrow> If M' N P"
| Ifz : "If Zero N P \<rightarrow> N"
| Ifs : "If (Succ n) N P \<rightarrow> P"
| Let : "Let xy (Pair V W) M \<rightarrow> M[V <- dfst xy][W <- dsnd xy]"
| PredZ: "Pred Zero \<rightarrow> Zero"
| PredS: "Pred (Succ n) \<rightarrow> n"
| FixBeta: "App (Fix f x M) V \<rightarrow> M[V <- x][Fix f x M <- f]"

inductive beta_star :: "'var::var term \<Rightarrow> 'var::var term \<Rightarrow> bool"  (infix "\<rightarrow>*" 70) where
  refl: "M \<rightarrow>* M"
| step: "\<lbrakk> M \<rightarrow> N; N \<rightarrow>* P \<rbrakk> \<Longrightarrow> M \<rightarrow>* P"

coinductive diverge :: "'var::var term \<Rightarrow> bool" ("_ \<Up>" 80) where
  "M \<rightarrow> N \<Longrightarrow> N \<Up> \<Longrightarrow> M \<Up>"

lemma val_stuck_step: "val M \<or> stuck M \<or> (\<exists>N. M \<rightarrow> N)"
proof (induction M)
  case (6 M N)
  then show ?case
    by (auto intro!: num.intros stuckExp.intros beta.intros elim: num.cases intro: val.intros stuck.intros)
next
  case (9 M N P)
  then show ?case
    by (auto intro!: num.intros stuckExp.intros beta.intros elim: num.cases intro: val.intros stuck.intros)
qed (auto intro!: num.intros stuckExp.intros beta.intros elim: num.cases intro: val.intros stuck.intros)
  
binder_inductive (no_auto_equiv) val
  sorry (*TODO: Dmitriy*)

binder_inductive (no_auto_equiv) beta
  sorry (*TODO: Dmitriy*)

lemma num_usubst[simp]: "num M \<Longrightarrow> M[V <- x] = M"
  by (induct M rule: num.induct) auto

lemma val_usubst[simp]: "val M \<Longrightarrow> val V \<Longrightarrow> val (M[V <- x])"
  by (binder_induction M avoiding: V x rule: val.strong_induct)
    (auto intro: val.intros)

lemma fresh_subst[simp]: "x \<notin> FVars_term t \<Longrightarrow> x \<notin> FVars_term s \<Longrightarrow> x \<notin> FVars_term (t[s <- y])"
  sorry (*TODO: Dmitriy*)
(*
  apply (binder_induction t avoiding: s y rule: term.strong_induct)
  apply auto
  oops
*)

lemma subst_idle[simp]: "y \<notin> FVars_term t \<Longrightarrow> t[s <- y] = t"
  sorry (*TODO: Dmitriy*)
(*
  apply (binder_induction t avoiding: s y rule: term.strong_induct)
  apply (auto simp:)
  oops
*)

lemma usubst_usubst: "y1 \<noteq> y2 \<Longrightarrow> y1 \<notin> FVars_term s2 \<Longrightarrow> t[s1 <- y1][s2 <- y2] = t[s2 <- y2][s1[s2 <- y2] <- y1]"
  sorry (*TODO: Dmitriy*)
(*
  apply (binder_induction t avoiding: y1 y2 s1 s2 rule: term.strong_induct)
  apply auto
  oops
*)

lemma dsel_dset[simp]: "dfst xy \<in> dset xy" "dsnd xy \<in> dset xy"
  by (transfer; auto)+

lemma beta_usubst: "M \<rightarrow> N \<Longrightarrow> val V \<Longrightarrow> M[V <- x] \<rightarrow> N[V <- x]"
  apply (binder_induction M N avoiding: M N V x rule: beta.strong_induct)
  apply (auto intro: beta.intros simp: Int_Un_distrib usubst_usubst[of _ x V])
  apply (subst usubst_usubst[of _ x V])
    apply auto
   apply (metis Int_emptyD dsel_dset(2))
  apply (subst usubst_usubst[of _ x V])
    apply auto
   apply (metis Int_emptyD dsel_dset(1))
  apply (auto intro: beta.intros)
  done

type_synonym 'var typing = "'var term \<times> type"
notation Product_Type.Pair (infix ":." 70)

inductive disjunction :: "type \<Rightarrow> type \<Rightarrow> bool" (infix "||" 70) where
  "Nat || Prod _ _"
| "Nat || To _  _"
| "Nat || OnlyTo _  _"
| "Prod _ _ || To _ _"
| "Prod _ _ || OnlyTo _  _"
| "A || B \<Longrightarrow> B || A"

notation Set.insert (infixr ";" 50)

inductive judgement :: "'var::var typing set \<Rightarrow> 'var::var typing set \<Rightarrow> bool" (infix "\<turnstile>" 10) where
  Id : "(Var x :. A) ; \<Gamma> \<turnstile> (Var x :. A) ; \<Delta>"
| ZeroR : "\<Gamma> \<turnstile> (Zero :. Nat) ; \<Delta>"
| SuccR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Succ M :. Nat) ; \<Delta>"
| PredR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Pred M :. Nat) ; \<Delta>"
| FixsR: "(Var f :. To A B) ; (Var x :. A) ; \<Gamma> \<turnstile> (M :. B) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Fix f x M :. To A B) ; \<Delta>"
| FixnR: "(Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma> \<turnstile> (Var x :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Fix f x M :. OnlyTo A B) ; \<Delta>"
| AppR: "(M :. To B A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. B) ; \<Delta> \<Longrightarrow>  \<Gamma>  \<turnstile> (App M N :. A) ; \<Delta>"
| PairR: "\<Gamma> \<turnstile> (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. B) ; \<Delta> \<Longrightarrow>  \<Gamma>  \<turnstile> (Pair M N :. Prod A B) ; \<Delta>"
| LetR: "(M :. Prod B C) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma> \<turnstile> (N :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Let x M N :. A) ; \<Delta>"
| IfzR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (P :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (If M N P :. A) ; \<Delta>"
| Dis: "A || B \<Longrightarrow> \<Gamma> \<turnstile> (M :. B) ; \<Delta> \<Longrightarrow> (M :. A); \<Gamma> \<turnstile> \<Delta>"
| PairL1: "(M :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M N :. Prod A B) ; \<Gamma> \<turnstile> \<Delta>"
| AppL: "(M :. OnlyTo B A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. B) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| SuccL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Succ M :. Nat) ; \<Gamma> \<turnstile> \<Delta>"
| PredL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pred M :. Nat) ; \<Gamma> \<turnstile> \<Delta>"
| IfzL1: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile> \<Delta>"
| IfzL2: "(N :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (P :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL1: "(N :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL2_1: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. A) ; \<Gamma> \<turnstile> (Var (dfst x) :. B1) ; \<Delta> \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL2_2: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. A) ; \<Gamma> \<turnstile> (Var (dsnd x) :. B1) ; \<Delta> \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| OkVarR: "\<Gamma> \<turnstile> (Var x :. Ok) ; \<Delta>"
| OkL: "(M :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile> \<Delta>"
| OkR: "\<Gamma> \<turnstile> (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (M :. Ok) ; \<Delta>"
| OkApL1: "(M :. OnlyTo Ok A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkApL2: "(N :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkSL: "(M :. Nat); \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Succ M :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pred M :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPrL_1: "(M1 :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPrL_2: "(M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta>"

print_attributes
binder_inductive (no_auto_equiv) judgement
  sorry

thm judgement.strong_induct

lemma weakenL: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile> \<Delta>"
  apply (induction \<Gamma> \<Delta> rule:judgement.induct)
  apply (auto intro: judgement.intros simp add: insert_commute[of "M :. A" _])
  done

lemma weakenR: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma>  \<turnstile> (M :. A) ; \<Delta>"
  apply (induction \<Gamma> \<Delta> rule:judgement.induct)
  apply (auto intro: judgement.intros simp add: insert_commute[of "M :. A" _])
  done

definition "Vals0 = {V. val V}"

fun
  type_semantics :: "type \<Rightarrow> 'var :: var term set" ("\<lblot>_\<rblot>" 90) and
  tau_semantics :: "type \<Rightarrow> 'var :: var term set" ("\<T>\<lblot>_\<rblot>" 90) and 
  bottom_semantics :: "type \<Rightarrow> 'var :: var term set" ("\<T>\<^sub>\<bottom>\<lblot>_\<rblot>" 90) where
  "\<lblot>Ok\<rblot> = Vals0"
| "\<lblot>Nat\<rblot> = {V. num V}"
| "\<lblot>Prod A B\<rblot> = case_prod Pair ` (\<lblot>A\<rblot> \<times> \<lblot>B\<rblot>)"
| "\<lblot>To A B\<rblot> = {Fix f x M | f x M. \<forall>V \<in> Vals0. V \<in> \<lblot>A\<rblot> \<longrightarrow> M[V <- x][Fix f x M <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>}"
| "\<lblot>OnlyTo A B\<rblot> = {Fix f x M | f x M. \<forall>V \<in> Vals0. M[V <- x][Fix f x M <- f] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> V \<in> \<lblot>A\<rblot>}"
| "\<T>\<lblot>A\<rblot> = {M. \<exists>V \<in> \<lblot>A\<rblot>. M \<rightarrow>* V \<and> val V}"
| "\<T>\<^sub>\<bottom>\<lblot>A\<rblot> = {M. M \<in> \<T>\<lblot>A\<rblot> \<or> (M \<Up>)}"

type_synonym 'var valuation = "('var \<times> 'var term) list"

fun eval :: "'var::var valuation \<Rightarrow> 'var term \<Rightarrow> 'var term" where
  "eval Nil M = M"
| "eval ((x,t) # ps) M = eval ps (M[t <- x])"

inductive typing_semanticsL :: "'var::var valuation \<Rightarrow> 'var typing \<Rightarrow> bool" where
  "eval \<theta> M \<in> \<T>\<lblot>A\<rblot> \<Longrightarrow> typing_semanticsL \<theta> (M :. A)"

inductive typing_semanticsR :: "'var::var valuation \<Rightarrow> 'var typing \<Rightarrow> bool" where
  "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow> typing_semanticsR \<theta> (M :. A)"

inductive semantic_judgement :: "'var::var typing set \<Rightarrow> 'var typing set \<Rightarrow> bool" (infix "\<Turnstile>" 10) where
  "\<forall>\<theta>. (\<forall>\<tau>\<in>L. typing_semanticsL \<theta> \<tau>) \<longrightarrow> (\<forall>\<tau>\<in>R. typing_semanticsR \<theta> \<tau>) \<Longrightarrow> L \<Turnstile> R"

inductive eval_ctx :: "'var :: var \<Rightarrow> 'var term \<Rightarrow> bool" where
  "eval_ctx hole (Var hole)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars_term M \<Longrightarrow> eval_ctx hole (App (Fix f x M) E)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars_term N \<Longrightarrow> eval_ctx hole (App E N)"
| "eval_ctx hole E \<Longrightarrow> eval_ctx hole (Succ E)"
| "eval_ctx hole E \<Longrightarrow> eval_ctx hole (Pred E)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars_term N \<Longrightarrow>eval_ctx hole (Pair E N)"
| "val V \<Longrightarrow> eval_ctx hole E \<Longrightarrow> hole \<notin> FVars_term V \<Longrightarrow> eval_ctx hole (Pair V E)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars_term N \<Longrightarrow> eval_ctx hole (Let x E N)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars_term N \<Longrightarrow> hole \<notin> FVars_term P \<Longrightarrow> eval_ctx hole (If E N P)"

binder_inductive (no_auto_equiv) eval_ctx
  sorry

definition blocked :: "'var :: var \<Rightarrow> 'var term \<Rightarrow> bool" where 
  "blocked z M = (\<exists> hole E. (eval_ctx hole E) \<and> (M = E[Var z <- hole]))"

lemma eval_subst: "eval_ctx x E \<Longrightarrow> y \<notin> FVars_term E \<Longrightarrow> eval_ctx y E[Var y <- x]"
  apply(binder_induction x E avoiding: y rule:eval_ctx.induct)
  apply(auto simp add:eval_ctx.intros)
  sorry

lemma subst_subst: "eval_ctx x E \<Longrightarrow> y \<notin> FVars_term E \<Longrightarrow> E[Var y <- x][Var z <- y] = E[Var z <- x]"
  sorry

lemma blocked_inductive: 
  "blocked z (Var z)"
  "blocked z N \<Longrightarrow> blocked z (App (Fix f x M) N)"
  "blocked z M \<Longrightarrow> blocked z (App M N)"
  "blocked z M \<Longrightarrow> blocked z (Succ M)"
  "blocked z M \<Longrightarrow> blocked z (Pred M)"
  "blocked z M \<Longrightarrow> blocked z (Pair M N)"
  "val V \<Longrightarrow> blocked z M \<Longrightarrow> blocked z (Pair V M)"
  "blocked z M \<Longrightarrow> blocked z (Let xy M N)"
  "blocked z M \<Longrightarrow> blocked z (If M N P)"
  apply(simp_all add: blocked_def)
  using eval_ctx.intros(1) apply fastforce
  subgoal
proof (erule exE)+
  fix hole E
  assume "eval_ctx hole E \<and> N = E[Var z <- hole]"
  then have "eval_ctx hole E" and "N = E[Var z <- hole]" by auto
  moreover obtain hole' where "hole' \<notin> FVars_term (App M E)"
    using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="App M E"]
    by auto
  moreover obtain E' where "E' = App (Fix f x M) E[Var hole'<-hole]" by simp
  ultimately have "eval_ctx hole' E'" using eval_subst[of hole E hole'] eval_ctx.intros
    by (metis Un_iff term.set(6))
  have "App (Fix f x M) N = E'[Var z <- hole']" 
    using subst_subst \<open>E' = App (Fix f x M) E[Var hole' <- hole]\<close> \<open>N = E[Var z <- hole]\<close>
      \<open>eval_ctx hole E\<close> \<open>hole' \<notin> FVars_term (App M E)\<close> 
    by fastforce
  show "\<exists>hole' E'. eval_ctx hole' E' \<and> App (Fix f x M) N = E'[Var z <- hole']"
    using \<open>eval_ctx hole' E'\<close> \<open>App (Fix f x M) N = E'[Var z <- hole']\<close>
    by auto
qed
  sorry

inductive less_defined :: "'var::var term \<Rightarrow> 'var term \<Rightarrow> bool" (infix "\<greatersim>" 90) where
  "\<exists>N. \<not>(\<exists>N'. N \<rightarrow> N') \<and> ((P \<rightarrow>* N) \<longrightarrow> (Q \<rightarrow>* N)) \<Longrightarrow> P \<greatersim> Q"

thm term.subst

lemma subst_Succ_inversion: 
  assumes "M[t <- x] = Succ N" and "\<not> blocked x M"
  obtains N' where "M = Succ N'" and "N = N'[t <- x]"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros blocked_def Int_Un_distrib split:if_splits)
  using eval_ctx.intros(1) apply fastforce
  done

lemma subst_Pred_inversion: 
  assumes "M[t <- x] = Pred N" and "\<not> blocked x M"
  obtains N' where "M = Pred N'" and "N = N'[t <- x]"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros blocked_def Int_Un_distrib split:if_splits)
  using eval_ctx.intros(1) apply fastforce
  done

lemma subst_App_inversion:
  assumes "M[t <- x] = App R Q" and "\<not> blocked x M"
  obtains R' Q' where "M = App R' Q'" and "R'[t <- x] = R" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros blocked_def Int_Un_distrib split:if_splits)
  using eval_ctx.intros(1) apply fastforce
  done

lemma subst_Pair_inversion:
  assumes "M[t <- x] = Pair Q1 Q2" and "\<not> blocked x M"
  obtains Q1' Q2' where "M = Pair Q1' Q2'" and "Q1'[t <- x] = Q1" and "Q2'[t <- x] = Q2"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  done

lemma subst_If_inversion:
  assumes "M[t <- x] = If Q0 Q1 Q2" and "\<not> blocked x M"
  obtains Q0' Q1' Q2' where "M = If Q0' Q1' Q2'" and "Q0'[t <- x] = Q0" and "Q1'[t <- x] = Q1" and "Q2'[t <- x] = Q2"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  done

lemma b2:
  assumes "eval_ctx x E"
    and "M[N <- z] = E[P <- x]"
    and "x \<noteq> z"
    and "x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N"
    and "\<not> (blocked z M)"
  shows "\<exists>F P'. M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z]"
  using assms
proof (induction x E arbitrary: M rule:eval_ctx.induct)
  case (1 x)
  have "M[N <- z] = P" by (simp add: "1.prems"(1))
  obtain F P' where "F = Var x" "P' = M" by simp
  show ?case by (metis "1.prems"(2) \<open>M[N <- z] = P\<close> usubst_simps(5))
next
  case (2 x E f a Q)
  (*
  have "x \<notin> FVars_term Q" sorry
  have "M[N <- z] = App (Fix f a Q) E[P <- x]" sorry
  obtain Q' R where "M = App (Fix f x Q') R" sorry
  have "Q'[N <- a] = Q" and "E[N <- z] = E[P <- x]" sorry
  have "\<not> blocked z R" sorry
  obtain E' P' where "R = E'[P' <- x]" and "E'[N <- z] = E" and "P'[N <- z] = P" sorry
  obtain F where "F = App (Fix f x Q') E'" sorry *)
  then show ?case sorry
next
  case (3 x E Q)
  have "M[N <- z] = App (E[P <- x]) Q" using "3.prems" "3.hyps" by simp
  then obtain R Q' where "M = App R Q'" and "R[N <- z] = E[P <- x]" and "Q'[N <- z] = Q"
    using subst_App_inversion 3 by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z R"
    using \<open>M = App R Q'\<close> eval_ctx.intros(3) blocked_def blocked_inductive(3) by blast
  ultimately obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- x]"
    using "3.IH"[where M = R] 3 by force
  moreover have "x \<notin> FVars_term Q'"
    using "3.hyps" \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = App R Q'\<close>
    by simp
  ultimately have "M = (App E' Q')[P' <- x] \<and> App E Q = (App E' Q')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = App R Q'\<close> \<open>Q'[N <- z] = Q\<close> by simp
  then show ?case by blast
next                                                                       
  case (4 x E)
  have "M[N <- z] = Succ(E[P <- x])" by (simp add: "4.prems"(1))
  then obtain Q where "M = Succ Q" and "Q[N <- z] = E[P <- x]" using subst_Succ_inversion 4
    by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using \<open>M = Succ Q\<close> eval_ctx.intros(4) blocked_def by (metis usubst_simps(2))
  ultimately
  obtain F' P' where "P'[N <- z] = P" and "E = F'[N <- z]" and "Q = F'[P' <- x]"
    using "4.IH"[where M = Q] 4(4,5) by auto
  then have "M = (Succ F')[P' <- x] \<and> Succ E = (Succ F')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = Succ Q\<close> by simp
  then show ?case by blast
next
  case (5 x E)
  have "M[N <- z] = Pred(E[P <- x])" by (simp add: "5.prems"(1))
  then obtain Q where "M = Pred Q" and "Q[N <- z] = E[P <- x]" using subst_Pred_inversion 5
    by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using \<open>M = Pred Q\<close> eval_ctx.intros(5) blocked_def by (metis usubst_simps(3))
  ultimately
  obtain F' P' where "P'[N <- z] = P" and "E = F'[N <- z]" and "Q = F'[P' <- x]"
    using "5.IH"[where M = Q] 5(4,5) by auto
  then have "M = (Pred F')[P' <- x] \<and> Pred E = (Pred F')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = Pred Q\<close> by simp
  then show ?case by blast
next
  case (6 x E Q)
  have "M[N <- z] = Pair (E[P <- x]) Q"
    by (simp add: "6.hyps"(2) "6.prems"(1))
  then obtain Q1 Q2 where "M = Pair Q1 Q2" and "E[P <- x] = Q1[N <- z]" and "Q = Q2[N <- z]"
    using subst_Pair_inversion "6.prems"(4) by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q1" 
    using blocked_inductive \<open>M = Pair Q1 Q2\<close> by metis
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q1 = E'[P' <- x]"
    using "6.IH"[where M = Q] 6 by fastforce
   moreover have "x \<notin> FVars_term Q2"
    using "6.hyps" \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = Pair Q1 Q2\<close>
    by simp
  ultimately have "M = (Pair E' Q2)[P' <- x] \<and> Pair E Q = (Pair E' Q2)[N <- z] \<and> P = P'[N <- z]"
    by (simp add: \<open>M = term.Pair Q1 Q2\<close> \<open>Q = Q2[N <- z]\<close>)
  then show ?case by blast
next
  case (7 V x E)
  have "M[N <- z] = Pair V E[P <- x]"
    by(simp add:"7.hyps" "7.prems")
  then obtain V' Q where "M = Pair V' Q" and "V = V'[N <- z]" and "E[P <- x] = Q[N <- z]"
    using subst_Pair_inversion "7.prems" by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using blocked_inductive(7) \<open>M = Pair V' Q\<close> \<open>val V'\<close> sorry
  (* How can we know that V' is value? It's possible for V to be val while V' not val.
     For example, consider V = Succ Zero, V' = Succ x, V = V'[Zero <- x]*)
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q = E'[P' <- x]"
    using "7.IH"[where M = Q] 7 by fastforce
   moreover have "x \<notin> FVars_term V'"
    using "7.hyps" \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = Pair V' Q\<close>
    by simp
  ultimately have "M = (Pair V' E')[P' <- x] \<and> Pair V E = (Pair V' E')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = term.Pair V' Q\<close> \<open>V = V'[N <- z]\<close> \<open>Q = E'[P' <- x]\<close> by simp
  then show ?case by blast
next
  case (8 hole E Q x M)
  show ?case sorry
next
  case (9 x E Q1 Q2)
  have "M[N <- z] = If E[P <- x] Q1 Q2"
    by(simp add:"9.hyps" "9.prems")
  then obtain Q0 Q1' Q2' where "M = If Q0 Q1' Q2'" and "E[P <- x] = Q0[N <- z]" and "Q1 = Q1'[N <- z]" and "Q2 = Q2'[N <- z]"
    using subst_If_inversion "9.prems" by metis
  thm "9.IH"[where M = Q0]
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q0"
    using blocked_inductive(9) \<open>M = If Q0 Q1' Q2'\<close> by auto
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q0 = E'[P' <- x]"
    using "9.IH"[where M = Q0] 9 by fastforce
  moreover have "x \<notin> FVars_term Q1'" and "x \<notin> FVars_term Q2'"
    using "9.hyps" \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = If Q0 Q1' Q2'\<close>
    by auto
  ultimately have "M = (If E' Q1' Q2')[P' <- x] \<and> (If E Q1 Q2) = (If E' Q1' Q2')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = If Q0 Q1' Q2'\<close> \<open>Q1 = Q1'[N <- z]\<close> \<open>Q2 = Q2'[N <- z]\<close> \<open>Q0 = E'[P' <- x]\<close> by simp
  then show ?case by blast
qed

thm beta.cases

lemma b3_1: 
  assumes "eval_ctx x E" and "M[N <- z] = E[P1 <- x]" and "P1 \<rightarrow> P2" and "\<not> blocked z M"
  shows "\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x]"
  using assms
proof (induction x E arbitrary: M rule:eval_ctx.induct)
  case (1 hole)
  show ?case
  using "1.prems"(2)
  proof (cases P1 P2 rule:beta.cases)
    case (OrdApp2 N N' f x M)
    then show ?thesis sorry
  next
    case (OrdApp1 M M' N)
    then show ?thesis sorry
  next
    case (OrdSucc M M')
    then show ?thesis sorry
  next
    case (OrdPred M M')
    then show ?thesis sorry
  next
    case (OrdPair1 M M' N)
    then show ?thesis sorry
  next
    case (OrdPair2 V N N')
    then show ?thesis sorry
  next
    case (OrdLet M M' xy N)
    then show ?thesis sorry
  next
    case (OrdIf M M' N P)
    then show ?thesis sorry
  next
    case (Ifz P)
    then show ?thesis sorry
  next
    case (Ifs n N)
    then show ?thesis sorry
  next
    case (Let xy V W M)
    then show ?thesis sorry
  next
    case PredZ
    then show ?thesis sorry
  next
    case PredS
    then show ?thesis sorry
  next
    case (FixBeta f x M V)
    then show ?thesis sorry
  qed
next
  case (2 hole E M f x)
  then show ?case sorry
next
  case (3 hole E N)
  then show ?case sorry
next
  case (4 hole E)
  then show ?case sorry
next
  case (5 hole E)
  then show ?case sorry
next
  case (6 hole E N)
  then show ?case sorry
next
  case (7 V hole E)
  then show ?case sorry
next
  case (8 hole E N x)
  then show ?case sorry
next
  case (9 hole E N P)
  then show ?case sorry
qed

lemma b3: "M[N <- z] \<rightarrow> P \<Longrightarrow> blocked z M \<or> (\<exists>M'. M \<rightarrow> M' \<and> P = M'[N <- z])"
  sorry

end