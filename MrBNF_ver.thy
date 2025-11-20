theory MrBNF_ver
  imports Binders.MRBNF_Recursor "Case_Studies.FixedCountableVars"
begin

section \<open>Def\<close>

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

lemma SSupp_term_fun_upd: "SSupp Var (Var(x :: 'var :: var := u)) \<subseteq> {x}"
  by (auto simp: SSupp_def)

lemma IImsupp_term_fun_upd: "IImsupp Var FVars_term (Var(x :: 'var :: var := u)) \<subseteq> {x} \<union> FVars_term u"
  by (auto simp: IImsupp_def SSupp_def)

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
  unfolding usubst_def using IImsupp_term_fun_upd SSupp_term_fun_upd
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
| Ifs : "num n \<Longrightarrow> If (Succ n) N P \<rightarrow> P"
| Let : "Let xy (Pair V W) M \<rightarrow> M[V <- dfst xy][W <- dsnd xy]"
| PredZ: "Pred Zero \<rightarrow> Zero"
| PredS: "Pred (Succ n) \<rightarrow> n"
| FixBeta: "App (Fix f x M) V \<rightarrow> M[V <- x][Fix f x M <- f]"

inductive betas :: "'var::var term \<Rightarrow> nat \<Rightarrow> 'var::var term \<Rightarrow> bool"  ("_ \<rightarrow>[_] _" [70, 0, 70] 70) where
  refl: "M \<rightarrow>[0] M"
| step: "\<lbrakk> M \<rightarrow> N; N \<rightarrow>[n] P \<rbrakk> \<Longrightarrow> M \<rightarrow>[Suc n] P"

definition beta_star :: "'var::var term \<Rightarrow> 'var::var term \<Rightarrow> bool" (infix "\<rightarrow>*" 70) where
  "M \<rightarrow>* N = (\<exists>n. M \<rightarrow>[n] N)"

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
  by (binder_induction M avoiding: V x rule: val.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
    (auto intro: val.intros)

lemma term_strong_induct: "\<forall>\<rho>. |K \<rho> :: 'a ::var set| <o |UNIV :: 'a set| \<Longrightarrow>
(\<And>\<rho>. P Zero \<rho>) \<Longrightarrow>
(\<And>x \<rho>. \<forall>\<rho>. P x \<rho> \<Longrightarrow> P (Succ x) \<rho>) \<Longrightarrow>
(\<And>x \<rho>. \<forall>\<rho>. P x \<rho> \<Longrightarrow> P (Pred x) \<rho>) \<Longrightarrow>
(\<And>x1 x2 x3 \<rho>. \<forall>\<rho>. P x1 \<rho> \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> \<forall>\<rho>. P x3 \<rho> \<Longrightarrow> P (term.If x1 x2 x3) \<rho>) \<Longrightarrow>
(\<And>x \<rho>. P (Var x) \<rho>) \<Longrightarrow>
(\<And>x1 x2 \<rho>. \<forall>\<rho>. P x1 \<rho> \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> P (App x1 x2) \<rho>) \<Longrightarrow>
(\<And>x1 x2 x3 \<rho>. {x1, x2} \<inter> K \<rho> = {} \<Longrightarrow> \<forall>\<rho>. P x3 \<rho> \<Longrightarrow> P (Fix x1 x2 x3) \<rho>) \<Longrightarrow>
(\<And>x1 x2 \<rho>. \<forall>\<rho>. P x1 \<rho> \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> P (term.Pair x1 x2) \<rho>) \<Longrightarrow>
(\<And>x1 x2 x3 \<rho>. dset x1 \<inter> K \<rho> = {} \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> \<forall>\<rho>. P x3 \<rho> \<Longrightarrow> P (term.Let x1 x2 x3) \<rho>) \<Longrightarrow> \<forall>\<rho>. P t \<rho>"
  by (rule term.strong_induct) auto

lemma fresh_subst[simp]: "x \<notin> FVars_term t \<Longrightarrow> x \<notin> FVars_term s \<Longrightarrow> x \<notin> FVars_term (t[s <- y])"
  by (binder_induction t avoiding: t s y rule: term_strong_induct)
    (auto simp: Int_Un_distrib)

lemma subst_idle[simp]: "y \<notin> FVars_term t \<Longrightarrow> t[s <- y] = t"
  by (binder_induction t avoiding: t s y rule: term_strong_induct) (auto simp: Int_Un_distrib)

lemma FVars_usubst: "FVars_term M[N <- z] = FVars_term M - {z} \<union> (if z \<in> FVars_term M then FVars_term N else {})"
  unfolding usubst_def
  by (auto simp: term.Vrs_Sb split: if_splits)

lemma usubst_usubst: "y1 \<noteq> y2 \<Longrightarrow> y1 \<notin> FVars_term s2 \<Longrightarrow> t[s1 <- y1][s2 <- y2] = t[s2 <- y2][s1[s2 <- y2] <- y1]"
  apply (binder_induction t avoiding: t y1 y2 s1 s2 rule: term_strong_induct)
          apply (auto simp: Int_Un_distrib FVars_usubst split: if_splits)
  apply (subst (1 2) usubst_simps; auto simp: FVars_usubst split: if_splits)
  done

lemma dsel_dset[simp]: "dfst xy \<in> dset xy" "dsnd xy \<in> dset xy"
  by (transfer; auto)+

lemma beta_usubst: "M \<rightarrow> N \<Longrightarrow> val V \<Longrightarrow> M[V <- x] \<rightarrow> N[V <- x]"
  apply (binder_induction M N avoiding: M N V x rule: beta.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
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

section \<open>Semantics\<close>

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

section \<open>B2\<close>

definition blocked :: "'var :: var \<Rightarrow> 'var term \<Rightarrow> bool" where 
  "blocked z M = (\<exists> hole E. (eval_ctx hole E) \<and> (M = E[Var z <- hole]))"

lemma eval_subst: "eval_ctx x E \<Longrightarrow> y \<notin> FVars_term E \<Longrightarrow> eval_ctx y E[Var y <- x]"
(*
  apply(binder_induction x E avoiding: y rule: eval_ctx.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
  apply(auto simp add:eval_ctx.intros)
*)  sorry

lemma eval_ctxt_FVars_term: "eval_ctx x E \<Longrightarrow> x \<in> FVars_term E"
  by (induct x E rule: eval_ctx.induct) auto

lemma SSupp_term_Var[simp]: "SSupp Var Var = {}"
  unfolding SSupp_def by auto

lemma IImsupp_term_Var[simp]: "IImsupp Var FVars_term Var = {}"
  unfolding IImsupp_def by auto

lemma tvsubst_term_Var: "tvsubst_term Var t = (t :: 'var :: var term)"
  by (rule term.strong_induct[where P = "\<lambda>t p. p = t \<longrightarrow> tvsubst_term Var t = (t :: 'var :: var term)" and K = FVars_term, simplified])
    (auto simp: Int_Un_distrib intro!: ordLess_ordLeq_trans[OF term.set_bd var_class.large'])

lemma IImsupp_term_bound:
  fixes f ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  shows "|IImsupp Var FVars_term f| <o |UNIV::'a set|"
  unfolding IImsupp_def using assms
  by (simp add: UN_bound Un_bound ordLess_ordLeq_trans[OF term.set_bd var_class.large'])

lemma SSupp_term_tvsubst_term:
  fixes f g ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  shows "SSupp Var (tvsubst_term f \<circ> g) \<subseteq> SSupp Var f \<union> SSupp Var g"
  using assms by (auto simp: SSupp_def)

lemmas FVars_tvsubst_term = term.Vrs_Sb

lemma IImsupp_term_tvsubst_term:
  fixes f g ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  shows "IImsupp Var FVars_term (tvsubst_term f \<circ> g) \<subseteq> IImsupp Var FVars_term f \<union> IImsupp Var FVars_term g"
  using assms using SSupp_term_tvsubst_term[of f g]
  apply (auto simp: IImsupp_def FVars_tvsubst_term)
  by (metis (mono_tags, lifting) SSupp_def comp_apply mem_Collect_eq singletonD term.set(5) term.subst(5))

lemma SSupp_term_tvsubst_term_bound:
  fixes f g ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  assumes "|SSupp Var g| <o |UNIV::'a set|"
  shows "|SSupp Var (tvsubst_term f \<circ> g)| <o |UNIV :: 'a set|"
  using SSupp_term_tvsubst_term[of f g] assms
  by (simp add: card_of_subset_bound Un_bound)

lemma tvsubst_term_comp:
  assumes "|SSupp Var f| <o |UNIV :: 'var set|" "|SSupp Var g| <o |UNIV :: 'var set|"
  shows "tvsubst_term f (tvsubst_term g t) = tvsubst_term (tvsubst_term f o g) (t :: 'var :: var term)"
  unfolding term.Sb_comp[OF assms(2,1), symmetric] o_apply ..

lemmas tvsubst_term_cong = term.Sb_cong

lemma subst_subst: "eval_ctx x E \<Longrightarrow> y \<notin> FVars_term E \<Longrightarrow> E[Var y <- x][Var z <- y] = E[Var z <- x]"
  apply (cases "x = z")
  subgoal
    by (auto simp add: usubst_def tvsubst_term_comp intro!: tvsubst_term_cong SSupp_term_tvsubst_term_bound)
  subgoal by (subst usubst_usubst) (auto dest: eval_ctxt_FVars_term)
  done

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

inductive normal :: "'var::var term \<Rightarrow> bool" where
  "\<not>(\<exists>N'. N \<rightarrow> N') \<Longrightarrow> normal N"

inductive less_defined :: "'var::var term \<Rightarrow> 'var term \<Rightarrow> bool" (infix "\<greatersim>" 90) where
  "\<exists>N. normal N \<and> ((P \<rightarrow>* N) \<longrightarrow> (Q \<rightarrow>* N)) \<Longrightarrow> P \<greatersim> Q"

thm term.subst

lemma subst_Zero_inversion:
  assumes "M[t <- x] = Zero" and "\<not> blocked x M"
  shows "M = Zero"
  using assms
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros blocked_def Int_Un_distrib split:if_splits)
  using eval_ctx.intros(1) apply fastforce
  done

lemma subst_Var_inversion:
  assumes "M[t <- x] = Var y" and "\<not> M = Var x"
  shows "M = Var y"
  using assms
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
          apply(auto simp add:eval_ctx.intros blocked_inductive Int_Un_distrib split:if_splits)
  done

lemma subst_Succ_inversion: 
  assumes "M[t <- x] = Succ N" and "\<not> blocked x M"
  obtains N' where "M = Succ N'" and "N = N'[t <- x]"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros blocked_inductive Int_Un_distrib split:if_splits)
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
  sorry
  done

lemma subst_Pair_inversion:
  assumes "M[t <- x] = Pair Q1 Q2" and "\<not> blocked x M"
  obtains Q1' Q2' where "M = Pair Q1' Q2'" and "Q1'[t <- x] = Q1" and "Q2'[t <- x] = Q2"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  sorry
  done

lemma subst_If_inversion:
  assumes "M[t <- x] = If Q0 Q1 Q2" and "\<not> blocked x M"
  obtains Q0' Q1' Q2'
  where "M = If Q0' Q1' Q2'" and "Q0'[t <- x] = Q0" and "Q1'[t <- x] = Q1" and "Q2'[t <- x] = Q2"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  sorry
  done

lemma subst_Fix_inversion:
  assumes "M[t <- x] = Fix f z Q" and "\<not> M = Var x"
  assumes "f \<noteq> x" and "f \<notin> FVars_term t" and "x \<noteq> z" and "z \<notin> FVars_term t"
  obtains Q' where "M = Fix f z Q'" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
          apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  subgoal for f' z' Q' \<sigma> sorry

  thm avoiding_bij
  done

lemma subst_Let_inversion:
  assumes "M[t <- x] = Let xy P Q" and "\<not> blocked x M"
  assumes "x \<notin> dset xy" and "FVars_term t \<inter> dset xy = {}"
  obtains P' Q' where "M = Let xy P' Q'" and "P'[t <- x] = P" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: "App M (App t (Var x))" rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  sorry

lemma subst_num_inversion: "num m \<Longrightarrow> \<not> blocked z n \<Longrightarrow> n[N <- z] = m \<Longrightarrow> n = m"
proof (induction arbitrary: n rule:num.induct)
  case 1
  then show ?case using subst_Zero_inversion by auto
next
  case (2 m')
  obtain n' where "n = Succ n'" and "n'[N <- z] = m'" and "\<not> blocked z n'"
    using subst_Succ_inversion
    by (metis "2.prems"(1,2) blocked_inductive(4))
  then have "n' = m'" using "2.IH"[of n'] by auto 
  then show ?case
    by (simp add: \<open>n = Succ n'\<close>)
qed

lemma subst_val_inversion:
  assumes "val V" and "\<not> blocked z V'" and "V'[N <- z] = V"
  shows "val V'"
  using assms
proof(binder_induction V arbitrary: V' avoiding: "App N (Var z)" rule:val.strong_induct)
  case (1 x V')
  then obtain y where "V' = Var y" using subst_Var_inversion by blast
  then show ?case using val.intros by auto
next
  case (2 n V')
  then show ?case using subst_num_inversion
    by (metis val.simps)
next
  case (3 V1 V2 V')
  obtain V1' V2' where "V' = Pair V1' V2'" and "V1'[N <- z] = V1" and "V2'[N <- z] = V2"
    using \<open>\<not> blocked z V'\<close>  subst_Pair_inversion 3 by blast
  then have "\<not> blocked z V1'"
    using blocked_inductive \<open>\<not> blocked z V'\<close> by metis
  then have "val V1'" using \<open>V1'[N <- z] = V1\<close> "3.IH"(1)[of V1'] by auto
  then have "\<not> blocked z V2'"
    using blocked_inductive \<open>\<not> blocked z V'\<close> \<open>V' = term.Pair V1' V2'\<close> by metis
  then have "val V2'" using \<open>V2'[N <- z] = V2\<close> "3.IH"(2)[of V2'] by auto
  show ?case using \<open>val V1'\<close> \<open>val V2'\<close> \<open>V' = Pair V1' V2'\<close> val.intros by auto
next
  case (4 f x M V')
  then obtain M' where "V' = Fix f x M'" and "M'[N <- z] = M"
    using subst_Fix_inversion[of V' N z f x M] blocked_inductive(1)
    by (metis Un_empty_right Un_insert_right insertCI insert_disjoint(2) term.set(5,6))
  then show ?case using val.intros by auto
qed

lemma FVars_subst: "(FVars_term M \<union> FVars_term N) \<supseteq> FVars_term M[N <- z]"
  unfolding usubst_def
  by (auto simp: FVars_tvsubst_term split:if_splits)

lemma FVars_subst_inversion: "(FVars_term M[N <- z] \<union> {z}) \<supseteq> FVars_term M"
  unfolding usubst_def
  by (auto simp: FVars_tvsubst_term)

thm eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P) \<longrightarrow> M[N <- z] = E[P <- x] \<longrightarrow>
    x \<noteq> z \<longrightarrow>
    x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N \<longrightarrow>
    \<not> blocked z M \<longrightarrow> (\<exists>F P'. M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z])"
    and K = "\<lambda>(z, N, M, E, x, P). {z,x} \<union> FVars_term N \<union> FVars_term M  \<union> FVars_term E \<union> FVars_term P",
    rule_format, rotated -5, of "(z, N, M, E, x, P)" M E x,
    simplified prod.inject simp_thms True_implies_equals]

lemma b2:
  assumes "eval_ctx x E"
    and "M[N <- z] = E[P <- x]"
    and "x \<noteq> z"
    and "x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N"
    and "\<not> (blocked z M)"
  shows "\<exists>F P'. M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z]"
proof (rule eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P) \<longrightarrow> M[N <- z] = E[P <- x] \<longrightarrow>
    x \<noteq> z \<longrightarrow>
    x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N \<longrightarrow>
    \<not> blocked z M \<longrightarrow> (\<exists>F P'. M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z])"
    and K = "\<lambda>(z, N, M, E, x, P). {z,x} \<union> FVars_term N \<union> FVars_term M  \<union> FVars_term E \<union> FVars_term P",
    rule_format, rotated -5, of "(z, N, M, E, x, P)" M E x, OF _ assms(2,3,4,5,1),
    simplified prod.inject simp_thms True_implies_equals prod.case], goal_cases card 1 2 3 4 5 6 7 8 9)
case (card p)
then show ?case
  unfolding split_beta
  by (intro Un_bound infinite_UNIV ordLess_ordLeq_trans[OF term.set_bd var_class.large']) auto
next
  case (1 x p M)
  have "M[N <- z] = P" by (simp add: 1(2))
  obtain F P' where "F = Var x" "P' = M" by simp
  show ?case by (metis 1(3) \<open>M[N <- z] = P\<close> usubst_simps(5))
next
  case (2 hole E Q f a p M)
  have "M[N <- z] = App (Fix f a Q) (E[P <- hole])" 
    using "2" by auto
  then obtain F R where "M = App F R" and "F[N <- z] = Fix f a Q" and "R[N <- z] = E[P <- hole]"
    using subst_App_inversion[of M N z "Fix f a Q" "E[P <- hole]"] "2"(9) by auto
  moreover have "\<not> blocked z F" using "2"(9) blocked_inductive(3) \<open>M = App F R\<close> by auto
  ultimately obtain Q' where "M = App (Fix f a Q') R" and "Q'[N <- z] = Q"
     using subst_Fix_inversion[of F N z f a Q] 2 blocked_inductive(1)[of z] by auto
  then have "\<not> blocked z R"
    using \<open>\<not> blocked z M\<close> blocked_inductive(2) by blast
  then obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- hole]"
    using \<open>R[N <- z] = E[P <- hole]\<close> 2(3)[of "(z, N, R, E, hole, P)" R] 2(8)
    by (metis Un_iff \<open>M = App F R\<close> term.set(6))
  moreover have "hole \<notin> FVars_term Q'"
    using 2 \<open>hole \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = App (Fix f a Q') R\<close>
    by simp
  ultimately have "M = (App (Fix f a Q') E')[P' <- hole] \<and> App (Fix f a Q) E = (App (Fix f a Q') E')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = App (Fix f a Q') R\<close> \<open>Q'[N <- z] = Q\<close> \<open>R[N <- z] = E[P <- hole]\<close>
    by (metis "2"(8) Un_iff \<open>F[N <- z] = Fix f a Q\<close> \<open>M = App F R\<close> subst_idle
        term.inject(5) usubst_simps(6))
  then show ?case by metis
next
  case (3 x E Q p M)
  have "M[N <- z] = App (E[P <- x]) Q" using 3 by simp
  then obtain R Q' where "M = App R Q'" and "R[N <- z] = E[P <- x]" and "Q'[N <- z] = Q"
    using subst_App_inversion 3 by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z R"
    using \<open>M = App R Q'\<close> eval_ctx.intros(3) blocked_def blocked_inductive(3) by blast
  ultimately obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- x]"
    using 3(2)[where M = R] 3 by force
  moreover have "x \<notin> FVars_term Q'"
    using 3 \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = App R Q'\<close>
    by simp
  ultimately have "M = (App E' Q')[P' <- x] \<and> App E Q = (App E' Q')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = App R Q'\<close> \<open>Q'[N <- z] = Q\<close> by simp
  then show ?case by blast
next                                                                       
  case (4 x E p M)
  have "M[N <- z] = Succ(E[P <- x])" by (simp add: 4)
  then obtain Q where "M = Succ Q" and "Q[N <- z] = E[P <- x]" using subst_Succ_inversion 4
    by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using \<open>M = Succ Q\<close> eval_ctx.intros(4) blocked_def by (metis usubst_simps(2))
  ultimately
  obtain F' P' where "P'[N <- z] = P" and "E = F'[N <- z]" and "Q = F'[P' <- x]"
    using 4(2)[where M = Q] 4(1,3-) by auto
  then have "M = (Succ F')[P' <- x] \<and> Succ E = (Succ F')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = Succ Q\<close> by simp
  then show ?case by blast
next
  case (5 x E p M)
  have "M[N <- z] = Pred(E[P <- x])" by (simp add: 5)
  then obtain Q where "M = Pred Q" and "Q[N <- z] = E[P <- x]" using subst_Pred_inversion 5
    by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using \<open>M = Pred Q\<close> eval_ctx.intros(5) blocked_def by (metis usubst_simps(3))
  ultimately
  obtain F' P' where "P'[N <- z] = P" and "E = F'[N <- z]" and "Q = F'[P' <- x]"
    using 5(2)[where M = Q] 5(1,3-) by auto
  then have "M = (Pred F')[P' <- x] \<and> Pred E = (Pred F')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = Pred Q\<close> by simp
  then show ?case by blast
next
  case (6 x E Q p M)
  have "M[N <- z] = Pair (E[P <- x]) Q"
    by (simp add: 6)
  then obtain Q1 Q2 where "M = Pair Q1 Q2" and "E[P <- x] = Q1[N <- z]" and "Q = Q2[N <- z]"
    using subst_Pair_inversion 6 by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q1" 
    using blocked_inductive \<open>M = Pair Q1 Q2\<close> by metis
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q1 = E'[P' <- x]"
    using 6(2)[where M = Q] 6 by fastforce
   moreover have "x \<notin> FVars_term Q2"
    using 6 \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = Pair Q1 Q2\<close>
    by simp
  ultimately have "M = (Pair E' Q2)[P' <- x] \<and> Pair E Q = (Pair E' Q2)[N <- z] \<and> P = P'[N <- z]"
    by (simp add: \<open>M = term.Pair Q1 Q2\<close> \<open>Q = Q2[N <- z]\<close>)
  then show ?case by blast
next
  case (7 V x E p M)
  have "M[N <- z] = Pair V E[P <- x]"
    by(simp add: 7)
  then obtain V' Q where "M = Pair V' Q" and "V = V'[N <- z]" and "E[P <- x] = Q[N <- z]"
    using subst_Pair_inversion 7 by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using blocked_inductive(7) \<open>M = Pair V' Q\<close> subst_val_inversion
    using "7"(1) blocked_inductive(6) calculation(2) by blast
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q = E'[P' <- x]"
    using 7(3)[where M = Q] 7 by fastforce
   moreover have "x \<notin> FVars_term V'"
    using 7 \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = Pair V' Q\<close>
    by simp
  ultimately have "M = (Pair V' E')[P' <- x] \<and> Pair V E = (Pair V' E')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = term.Pair V' Q\<close> \<open>V = V'[N <- z]\<close> \<open>Q = E'[P' <- x]\<close> by simp
  then show ?case by blast
next
  case (8 hole E Q x p M)
  have "M[N <- z] = Let x E[P <- hole] Q"
    using "8" usubst_simps(9)[of hole x P E Q]
    by fastforce
  then obtain R Q' where "M = Let x R Q'" and "Q'[N <- z] = Q" and "R[N <- z] = E[P <- hole]"
    using subst_Let_inversion[of M N z x "E[P <- hole]" Q] "8"(9) "8"(1) by blast
  moreover have "\<not> blocked z R" using "8"(9) blocked_inductive \<open>M = Let x R Q'\<close> by metis
  ultimately obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- hole]"
    using 8(3)[of "(z, N, R, E, hole, P)" R] 8(8)
    by (metis Un_iff term.set(9))
  moreover have "hole \<notin> FVars_term Q'"
    using 8 \<open>hole \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = Let x R Q'\<close>
    by simp
  moreover have "dset x \<inter> FVars_term E' = {}" and "dset x \<inter> FVars_term P' = {}"
    using FVars_subst_inversion[of E' N z] FVars_subst_inversion[of P' N z] 8(1) \<open>E = E'[N <- z]\<close> \<open>P = P'[N <- z]\<close>
    by auto
  ultimately have "M = (Let x E' Q')[P' <- hole]" 
    using usubst_simps(9)[of hole x P' E' Q'] 8(1) \<open>M = Let x R Q'\<close> by auto
  moreover have "Let x E Q = (Let x E' Q')[N <- z]"
    using usubst_simps(9)[of z x N E' Q'] \<open>dset x \<inter> FVars_term E' = {}\<close> 8(1)
    using \<open>E = E'[N <- z]\<close> \<open>Q'[N <- z] = Q\<close>
    by fastforce
  ultimately have "M = (Let x E' Q')[P' <- hole] \<and> Let x E Q = (Let x E' Q')[N <- z] \<and> P = P'[N <- z]"
    using \<open>P = P'[N <- z]\<close> by blast
  then show ?case by auto
next
  case (9 x E Q1 Q2 p M)
  have "M[N <- z] = If E[P <- x] Q1 Q2"
    by(simp add: 9)
  then obtain Q0 Q1' Q2' where "M = If Q0 Q1' Q2'" and "E[P <- x] = Q0[N <- z]" and "Q1 = Q1'[N <- z]" and "Q2 = Q2'[N <- z]"
    using subst_If_inversion 9 by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q0"
    using blocked_inductive(9) \<open>M = If Q0 Q1' Q2'\<close> by auto
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q0 = E'[P' <- x]"
    using 9(2)[where M = Q0] 9 by fastforce
  moreover have "x \<notin> FVars_term Q1'" and "x \<notin> FVars_term Q2'"
    using 9 \<open>x \<notin> FVars_term M \<union> FVars_term P \<union> FVars_term N\<close> \<open>M = If Q0 Q1' Q2'\<close>
    by auto
  ultimately have "M = (If E' Q1' Q2')[P' <- x] \<and> (If E Q1 Q2) = (If E' Q1' Q2')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = If Q0 Q1' Q2'\<close> \<open>Q1 = Q1'[N <- z]\<close> \<open>Q2 = Q2'[N <- z]\<close> \<open>Q0 = E'[P' <- x]\<close> by simp
  then show ?case by blast
qed

section \<open>B3\<close>

thm eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P1, P2) \<longrightarrow> M[N <- z] = E[P1 <- x] \<longrightarrow>
    P1 \<rightarrow> P2 \<longrightarrow> \<not> blocked z M \<longrightarrow> (\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x])"
    and K = "\<lambda>(z, N, M, E, x, P1, P2). {z,x} \<union> FVars_term N \<union> FVars_term M  \<union> FVars_term E \<union> FVars_term P1 \<union> FVars_term P2",
    rule_format, rotated -4, of "(z, N, M, E, x, P1, P2)" M E x,
    simplified prod.inject simp_thms True_implies_equals]

lemma b3_1: 
  assumes "eval_ctx x E" and "M[N <- z] = E[P1 <- x]" and "P1 \<rightarrow> P2" and "\<not> blocked z M"
  shows "\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x]"
proof (rule eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P1, P2) \<longrightarrow> M[N <- z] = E[P1 <- x] \<longrightarrow>
    P1 \<rightarrow> P2 \<longrightarrow> \<not> blocked z M \<longrightarrow> (\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x])"
    and K = "\<lambda>(z, N, M, E, x, P1, P2). {z,x} \<union> FVars_term N \<union> FVars_term M \<union> FVars_term E \<union> FVars_term P1 \<union> FVars_term P2",
    rule_format, rotated -4, of "(z, N, M, E, x, P1, P2)" M E x, OF _ assms(2,3,4,1),
    simplified prod.inject simp_thms True_implies_equals], 
    goal_cases card 1 2 3 4 5 6 7 8 9)
  case (card p)
then show ?case sorry
next
  case (1 hole p' M)
  have "p' = (z, N, M, Var hole, hole, P1, P2) \<Longrightarrow>
       M[N <- z] = (Var hole)[P1 <- hole] \<Longrightarrow>
       \<not> blocked z M \<Longrightarrow>
       \<exists>M'. M \<rightarrow> M' \<and>  M'[N <- z] = (Var hole)[P2 <- hole]"
    using 1(3)
proof (binder_induction P1 P2 avoiding: z N rule:beta.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
    case (2 N N' f x Q)
    then show ?case sorry
  next
    case (3 Q Q' N)
    then show ?case sorry
  next
    case (4 Q Q')
    then show ?case sorry
  next
    case (5 Q Q')
    then show ?case sorry
  next
    case (6 Q Q' N)
    then show ?case sorry
  next
    case (7 V N N')
    then show ?case sorry
  next
    case (8 Q Q' xy N)
    then show ?case sorry
  next
    case (9 Q Q' N P)
    then show ?case sorry
  next
    case (10 P2 Q)
    then have "M[N <- z] = If Zero P2 Q" by simp
    then obtain Q0 Q1 Q2
      where "M = If Q0 Q1 Q2" and "Q0[N <- z] = Zero" and "Q1[N <- z] = P2" and "Q2[N <- z] = Q"  and "\<not> blocked z Q0"
      using  \<open>\<not> blocked z M\<close> subst_If_inversion[of M N z Zero P2 Q] blocked_inductive by metis
    then have "Q0 = Zero"
      using subst_Zero_inversion by blast
    then show ?case
      using \<open>M = term.If Q0 Q1 Q2\<close> \<open>Q1[N <- z] = P2\<close> beta.Ifz by auto
  next
    case (11 Q Q1 P2)
    then have "M[N <- z] = term.If (Succ Q) Q1 P2" by simp
    then obtain Q0' Q1' Q2'
      where "M = If Q0' Q1' Q2'" and "Q0'[N <- z] = (Succ Q)" and "Q1'[N <- z] = Q1" and "Q2'[N <- z] = P2"  and "\<not> blocked z Q0'"
      using  \<open>\<not> blocked z M\<close> subst_If_inversion[of M N z "Succ Q" Q1 P2] blocked_inductive by metis
    then have "Q0' = Succ Q"
       using 11(1) num.intros(2) subst_num_inversion by blast
     then show ?case
      using \<open>M = term.If Q0' Q1' Q2'\<close> \<open>Q2'[N <- z] = P2\<close> beta.Ifs 11(1) by auto
  next
    case (12 xy V W Q)
    then have "M[N <- z] = Let xy (Pair V W) Q" by simp
    then obtain P' Q' where "M = Let xy P' Q'" and "P'[N <- z] = Pair V W" and "Q'[N <- z] = Q"
      using subst_Let_inversion[of M N z xy "Pair V W" Q] \<open>\<not> blocked z M\<close> 12(1) 12(2)
      by auto
    moreover have "\<not> blocked z P'" using blocked_inductive(8)[of z P'] \<open>M = Let xy P' Q'\<close> 1(4) by auto
    ultimately obtain V' W' where "P' = Pair V' W'" and "V'[N <- z] = V" and "W' [N <- z] = W"
      using subst_Pair_inversion by blast
    have "(Q'[V' <- dfst xy][W' <- dsnd xy])[N <- z] = Q[V <- dfst xy][W <- dsnd xy]"
      using usubst_usubst[of "dsnd xy" z N "Q'[V' <- dfst xy]" W'] usubst_usubst[of "dfst xy" z N Q' V']
      using 12(1) 12(2) \<open>Q'[N <- z] = Q\<close> \<open>V'[N <- z] = V\<close> \<open>W'[N <- z] = W\<close>
      by (metis Int_emptyD  dsel_dset(1,2))
    then show ?case
      by (metis \<open>M = term.Let xy P' Q'\<close> \<open>P' = term.Pair V' W'\<close> beta.Let
          usubst_simps(5))
  next
    case 13
    then have "M[N <- z] = Pred Zero" by simp
    then obtain Q where "M = Pred Q" and "\<not> blocked z Q" and "Q[N <- z] = Zero" using subst_Pred_inversion
      by (metis "1"(4) blocked_inductive(5))
    then have "Q = Zero" using \<open>Q[N <- z] = Zero\<close> \<open>\<not> blocked z Q\<close> subst_Zero_inversion by auto
    have "(Zero)[N <- z] = Zero" by simp
    then show ?case
      using \<open>M = Pred Q\<close> \<open>Q = Zero\<close> assms(3) PredZ by auto
  next
    case (14 P2)
    then have "M[N <- z] = Pred (Succ P2)" by simp
    then obtain Q where "M = Pred Q" and "\<not> blocked z Q" and "Q[N <- z] = Succ P2" using subst_Pred_inversion
      by (metis "1"(4) blocked_inductive(5))
    then obtain Q' where "Q = Succ Q'" and "Q'[N <- z] = P2"
      using subst_Succ_inversion by blast
    then show ?case
      using \<open>M = Pred Q\<close> PredS by auto
  next
    case (15 f x Q V)
    then have "M[N <- z] = App (Fix f x Q) V" by simp
    then obtain Q' V' where "M = App (Fix f x Q') V'" and "Q'[N <- z] = Q" and "V'[N <- z] = V"
      using  \<open>\<not> blocked z M\<close> subst_Fix_inversion subst_App_inversion blocked_inductive(3) sorry
    moreover have "(Fix f x Q')[N <- z] = Fix f x Q"
      using 15(1) 15(2) \<open>Q'[N <- z] = Q\<close> by auto 
    ultimately have "Q'[V' <- x][Fix f x Q' <- f][N <- z] = Q[V <- x][Fix f x Q <- f]"
      using usubst_usubst[of f z N "Q'[V' <- x]" "Fix f x Q'"] usubst_usubst[of x z N "Q'" "V'"]
      using 15(1) 15(2)
      by (metis insert_disjoint(2) insert_iff)
    then show ?case
      by (metis \<open>M = App (Fix f x Q') V'\<close> beta.FixBeta usubst_simps(5))
  qed
  then show ?case using 1 by auto
next
  case (2 hole E Q f x p M)
  then have "M[N <- z] = App (Fix f x Q) E[P1 <- hole]"
   using subst_idle usubst_simps(6) by auto
  then obtain F R where "M = App F R" and "R[N <- z] = E[P1 <- hole]" and "F[N <- z] = Fix f x Q"
    using \<open>\<not> blocked z M\<close> subst_App_inversion by blast
  then have "\<not> blocked z F" using blocked_inductive \<open>\<not> blocked z M\<close> by blast
  then obtain Q' where "F = Fix f x Q'" and "Q'[N <- z] = Q"
    using \<open>F[N <- z] = Fix f x Q\<close> 2(1) subst_Fix_inversion[of F N z f x Q] blocked_inductive(1)[of z] by auto
  then have "\<not> blocked z R" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = App F R\<close> by blast
  then obtain R' where "R \<rightarrow> R'" and "R'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> "2"(3)[of _  R] \<open>R[N <- z] = E[P1 <- hole]\<close> by auto
  have "(App (Fix f x Q') R')[N <- z] = (App (Fix f x Q) E)[P2 <- hole]"
    using "2"(1, 4) \<open>Q'[N <- z] = Q\<close> \<open>R'[N <- z] = E[P2 <- hole]\<close> by auto
  then show ?case
    using OrdApp2 \<open>F = Fix f x Q'\<close> \<open>M = App F R\<close> \<open>R \<rightarrow> R'\<close> by blast
next
  case (3 hole E Q p M)
  then have "M[N <- z] = App E[P1 <- hole] Q"
   using subst_idle usubst_simps(6) by auto
  then obtain R Q' where "M = App R Q'" and "R[N <- z] = E[P1 <- hole]" and "Q'[N <- z] = Q"
    using \<open>\<not> blocked z M\<close> subst_App_inversion by blast
  then have "\<not> blocked z R" using blocked_inductive \<open>\<not> blocked z M\<close> by blast
  then obtain R' where "R \<rightarrow> R'" and "R'[N <- z] = E[P2 <- hole]" 
    using \<open>P1 \<rightarrow> P2\<close> "3"(2)[where M = R] \<open>R[N <- z] = E[P1 <- hole]\<close> by auto
  have "(App R' Q')[N <- z] = (App E Q)[P2 <- hole]"
    using "3"(3) \<open>Q'[N <- z] = Q\<close> \<open>R'[N <- z] = E[P2 <- hole]\<close> by simp
  then show ?case
    using OrdApp1 \<open>M = App R Q'\<close> \<open>R \<rightarrow> R'\<close> by blast
next
  case (4 hole E p M)
  obtain Q where "M = Succ Q" and "Q[N <- z] = E[P1 <- hole]"
    using \<open>M[N <- z] = (Succ E)[P1 <- hole]\<close> \<open>\<not> blocked z M\<close> subst_Succ_inversion by force
  moreover have "\<not> blocked z Q" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Succ Q\<close> by blast
  ultimately obtain Q' where "Q \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> "4"(2)[where M = Q] by auto
  have "(Succ Q')[N <- z] = (Succ E)[P2 <- hole]"
    by (simp add: \<open>Q'[N <- z] = E[P2 <- hole]\<close>)
  then show ?case
    using OrdSucc \<open>M = Succ Q\<close> \<open>Q \<rightarrow> Q'\<close> by blast
next
  case (5 hole E p M)
  obtain Q where "M = Pred Q" and "Q[N <- z] = E[P1 <- hole]"
    using \<open>M[N <- z] = (Pred E)[P1 <- hole]\<close> \<open>\<not> blocked z M\<close> subst_Pred_inversion by force
  moreover have "\<not> blocked z Q" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Pred Q\<close> by blast
  ultimately obtain Q' where "Q \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]" 
    using \<open>P1 \<rightarrow> P2\<close> "5"(2)[of _ Q] by auto
  have "(Pred Q')[N <- z] = (Pred E)[P2 <- hole]"
    by (simp add: \<open>Q'[N <- z] = E[P2 <- hole]\<close>)
  then show ?case
    using OrdPred \<open>M = Pred Q\<close> \<open>Q \<rightarrow> Q'\<close> by blast
next
  case (6 hole E Q2 p M)
  have "M[N <- z] = (Pair E[P1 <- hole] Q2)"
    by (simp add: "6"(3, 5))
  then obtain Q1' Q2' where "M = Pair Q1' Q2'" and "Q1'[N <- z] = E[P1 <- hole]" and "Q2'[N <- z] = Q2"
    using \<open>\<not> blocked z M\<close> subst_Pair_inversion by blast
  moreover have "\<not> blocked z Q1'" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Pair Q1' Q2'\<close> by metis
  ultimately obtain Q' where "Q1' \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]" 
    using \<open>P1 \<rightarrow> P2\<close> "6"(2)[of _ Q1'] by blast
  have "(Pair Q' Q2')[N <- z] = (Pair E Q2)[P2 <- hole]"
    by (simp add: "6"(3) \<open>Q'[N <- z] = E[P2 <- hole]\<close> \<open>Q2'[N <- z] = Q2\<close>)
  then show ?case
    using OrdPair1 \<open>M = term.Pair Q1' Q2'\<close> \<open>Q1' \<rightarrow> Q'\<close> by blast
next
  case (7 V hole E p M)
  have "M[N <- z] = (Pair V E[P1 <- hole])"
    using "7" by simp
  then obtain V' Q where "M = Pair V' Q" and "V'[N <- z] = V" and "Q[N <- z] = E[P1 <- hole]"
    using \<open>\<not> blocked z M\<close> subst_Pair_inversion[of M N z V "E[P1 <- hole]"] by auto
  then have "val V'" using 7(1) \<open>\<not> blocked z M\<close> blocked_inductive subst_val_inversion
    by metis
  then have "\<not> blocked z Q" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Pair V' Q\<close> by metis
  then obtain Q' where "Q \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> \<open>Q[N <- z] = E[P1 <- hole]\<close> "7"(3)[of _ Q] by blast
  have "(Pair V' Q')[N <- z] = (Pair V E)[P2 <- hole]"
    using \<open>Q'[N <- z] = E[P2 <- hole]\<close> \<open>V'[N <- z] = V\<close> by (simp add: "7"(4))
  then show ?case
    using OrdPair2 \<open>M = term.Pair V' Q\<close> \<open>Q \<rightarrow> Q'\<close> \<open>val V'\<close> by blast
next
  case (8 hole E Q xy p M)
  have "M[N <- z] = Let xy E[P1 <- hole] Q"
   using usubst_simps(9)[of hole xy P1 E Q] subst_idle 8 by fastforce
  then obtain R Q' where "M = Let xy R Q'" and "R[N <- z] = E[P1 <- hole]" and "Q'[N <- z] = Q"
    using \<open>\<not> blocked z M\<close> subst_Let_inversion 8(1) by blast
  then have "\<not> blocked z R" using blocked_inductive(8) \<open>\<not> blocked z M\<close> by blast
  then obtain R' where "R \<rightarrow> R'" and "R'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> "8"(3)[of _  R] \<open>R[N <- z] = E[P1 <- hole]\<close> by auto
  thm FVars_subst
  have "dset xy \<inter> FVars_term E[P2 <- hole] = {}"
    using 8(1) FVars_subst[of E P2 hole] by auto
  then have "dset xy \<inter> FVars_term R' = {}"
    using FVars_subst_inversion[of R' N z] FVars_subst_inversion[of Q' N z]
    using 8(1) \<open>R'[N <- z] = E[P2 <- hole]\<close> \<open>Q'[N <- z] = Q\<close>
    by auto
  then have "(Let xy R' Q')[N <- z] = (Let xy E Q)[P2 <- hole]"
    using usubst_simps(9)[of z xy N R' Q']  usubst_simps(9)[of hole xy P2 E Q] 
    using "8"(1, 4) \<open>Q'[N <- z] = Q\<close> \<open>R'[N <- z] = E[P2 <- hole]\<close>
    by fastforce
  then show ?case
    using OrdLet \<open>M = term.Let xy R Q'\<close> \<open>R \<rightarrow> R'\<close> by blast
next
  case (9 hole E Q1 Q2 p M)
  have "M[N <- z] = (If E[P1 <- hole] Q1 Q2)"
    by (simp add: 9)
  then obtain Q0' Q1' Q2' 
    where "M = If Q0' Q1' Q2'" and "Q0'[N <- z] = E[P1 <- hole]" and "Q1'[N <- z] = Q1" and "Q2'[N <- z] = Q2"
    using \<open>\<not> blocked z M\<close> subst_If_inversion[of M N z "E[P1 <- hole]" Q1 Q2] by auto
  then have "\<not> blocked z Q0'" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = If Q0' Q1' Q2'\<close> by metis
  then obtain Q where "Q0' \<rightarrow> Q" and "Q[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> \<open>Q0'[N <- z] = E[P1 <- hole]\<close> 9(2)[of _ Q0'] by blast
  have "(If Q Q1' Q2')[N <- z] = (If E Q1 Q2)[P2 <- hole]"
    using \<open>Q[N <- z] = E[P2 <- hole]\<close> \<open>Q1'[N <- z] = Q1\<close> \<open>Q2'[N <- z] = Q2\<close> by (simp add: 9)
  then show ?case
    using OrdIf \<open>M = term.If Q0' Q1' Q2'\<close> \<open>Q0' \<rightarrow> Q\<close> by blast
qed

thm b3_1

lemma b3: "M[N <- z] \<rightarrow> P \<Longrightarrow> blocked z M \<or> (\<exists>M'. M \<rightarrow> M' \<and> P = M'[N <- z])"
proof -
  assume "M[N <- z] \<rightarrow> P"
  obtain E :: "'a term" and x :: 'a where "eval_ctx x E" and "E = Var x"
    by (simp add: eval_ctx.intros(1))
  then have "\<not> blocked z M \<Longrightarrow> (\<exists>M'. M \<rightarrow> M' \<and> P = M'[N <- z])" 
    using b3_1[of x E M N z "M[N <- z]" P] \<open>M[N <- z] \<rightarrow> P\<close> by auto
  then show ?thesis by blast
qed

section \<open>B4\<close>

thm diverge.cases

lemma div_ctx: 
  assumes "diverge Q" and "eval_ctx x E" 
  shows "diverge E[Q <- x]"
(*
  using assms(2)
proof(induction x E rule: eval_ctx.induct)
  case (2 hole E M f x)
  obtain E' where "E[Q <- hole] \<rightarrow> E'" and "diverge E'"
    using 2 diverge.cases[of "E[Q <- hole]"] by auto
  have "App (Fix f x M)[Q <- hole] E[Q <- hole] \<Up>"
  show ?case
    using 2 usubst_simps
*) sorry

context fixes x :: "'a :: var" begin
private definition Uctor :: "('a, 'a, 'a MrBNF_ver.term \<times> (unit \<Rightarrow> nat), 'a MrBNF_ver.term \<times> (unit \<Rightarrow> nat)) term_pre \<Rightarrow> unit \<Rightarrow> nat" where
  "Uctor \<equiv> \<lambda>pre _. case Rep_term_pre pre of
      Inl (Inl (Inl _)) \<Rightarrow> 0
    | Inl (Inl (Inr (_, c))) \<Rightarrow> c ()
    | Inl (Inr (Inl (_, c))) \<Rightarrow> c ()
    | Inl (Inr (Inr ((_, c1), (_, c2), (_, c3)))) \<Rightarrow> c1 () + c2 () + c3 ()
    | Inr (Inl (Inl y)) \<Rightarrow> (if x = y then 1 else 0)
    | Inr (Inl (Inr ((_, c1), (_, c2)))) \<Rightarrow> c1 () + c2 ()
    | Inr (Inr (Inl (_, _, _, c))) \<Rightarrow> c ()
    | Inr (Inr (Inr (Inl ((_, c1), (_, c2))))) \<Rightarrow> c1 () + c2 ()
    | Inr (Inr (Inr (Inr (_, (_, c1), (_, c2))))) \<Rightarrow> c1 () + c2 ()"
interpretation count: REC_term where
  Pmap = "\<lambda>_. id" and
  PFVars = "\<lambda>_. {}" and
  validP = "\<lambda>_::unit. True" and
  avoiding_set = "{x}" and
  Umap = "\<lambda>_ _. id" and
  UFVars = "\<lambda>_ _. {}" and
  validU = "\<lambda>_ :: nat. True" and
  Uctor = Uctor
  by standard
    (auto simp: Uctor_def map_term_pre_def Abs_term_pre_inverse[OF UNIV_I] in_imsupp
      dest: not_in_imsupp_same split: sum.splits)

definition "count_term t = count.REC_term t ()"

lemmas count_term_ctor = count.REC_ctor[simplified,
  folded count_term_def, unfolded Uctor_def map_term_pre_def o_apply Abs_term_pre_inverse[OF UNIV_I]
  case_sum_map_sum case_prod_map_prod prod.case, folded Uctor_def count_term_def]

lemmas count_term_swap = count.REC_swap[simplified, folded count_term_def]

end

lemma count_term_simps[simp]:
  "count_term x Zero = 0"
  "count_term x (Pred M) = count_term x M"
  "count_term x (Succ M) = count_term x M"
  "count_term x (If M N P) = count_term x M + count_term x N + count_term x P"
  "count_term x (Var y) = (if x = y then 1 else 0)"
  "count_term x (App M N) = count_term x M + count_term x N"
  "x \<noteq> f \<Longrightarrow> x \<noteq> a \<Longrightarrow> count_term x (Fix f a M) = count_term x M"
  "count_term x (Pair M N) = count_term x M + count_term x N"
  "x \<notin> dset xy \<Longrightarrow> dset xy \<inter> FVars_term M = {} \<Longrightarrow> count_term x (Let xy M N) = count_term x M + count_term x N"
  unfolding Zero_def Pred_def Succ_def If_def Var_def Fix_def App_def Pair_def Let_def
  by (subst count_term_ctor; auto simp:
    set1_term_pre_def set2_term_pre_def set3_term_pre_def set4_term_pre_def
    noclash_term_def sum.set_map Abs_term_pre_inverse[OF UNIV_I])+

lemma my_induct[case_names lex]:
  assumes "\<And>n N. (\<And>m M. m < n \<Longrightarrow> P m x M) \<Longrightarrow> (\<And>M. count_term x M < count_term x N \<Longrightarrow> P n x M) \<Longrightarrow> P n x N"
  shows "P (n :: nat) x (N :: 'a :: var term)"
  apply (induct "(n, N)" arbitrary: n N rule: wf_induct[OF wf_mlex[OF wf_measure], of fst "count_term x o snd"])
  apply (auto simp add: mlex_iff intro: assms)
  done

lemma b4:
  assumes "M[N <- x] \<rightarrow>[k] P" and "normal P" and "N \<greatersim> Q"
  shows "diverge M[Q <- x] \<or> (\<exists>m M'. P = M'[N <- x] \<and> M[Q <- x] \<rightarrow>[m] M'[Q <- x])"
  using assms
proof (induct k x M rule: my_induct)
  case (lex k M)
  show ?case
    using lex(3)
  proof (cases rule:betas.cases)
    case refl
    then have "P = M[N <- x]" and "M[Q <- x] \<rightarrow>[k] M[Q <- x]"
       using betas.intros by auto
    then show ?thesis by auto
  next
    case (step P' k')
    then show ?thesis
    proof (cases "blocked x M")
      case True
      then obtain hole E where "eval_ctx hole E" and "M = E[Var x <- hole]" 
          using blocked_def[of x M] by auto
      then have "M[Q <- x] = E[Q <- x][Q <- hole]"
          using usubst_usubst[of hole x Q E "Var x"] sorry (* need hole freshness *)
      then show ?thesis
      proof (cases "diverge Q")
        case True
        then have "diverge M[Q <- x]" 
          using div_ctx[of Q hole "E[Q <- x]"] \<open>M[Q <- x] = E[Q <- x][Q <- hole]\<close>
        then show ?thesis by simp
      next
        case False
        obtain N' where "normal N'" and "N \<rightarrow>* N'" and "Q \<rightarrow>* N'" sorry
        then have "M[N <- x] \<rightarrow>* E[N <- x][N' <- hole]" and "M[Q <- x] \<rightarrow>* E[Q <- x][N' <- x]" sorry
        then obtain m where "E[N <- x][N' <- hole] \<rightarrow>[m] P" and "m \<le> k" 
          and "count_term x E[Q <- x][N' <- hole] = count_term x M - 1" sorry
        have "E[Q <- x][N' <- hole] \<Up> \<or> (\<exists>m M'. P = M'[N <- x] \<and> E[Q <- x][N' <- hole] \<rightarrow>[m] M'[Q <- x])"
          using lex(2)[of "E[N' <- hole]"] sorry
        then show ?thesis sorry
      qed
    next
      case False
      then obtain M'' where "M \<rightarrow> M''" and "P' = M''[N <- x]"
        using step(2) b3[of M N x P'] by auto
      then have "M''[N <- x] \<rightarrow>[k'] P"
        using step(3) by simp
      then have "diverge M''[Q <- x] \<or> (\<exists>m M'. P = M'[N <- x] \<and> M''[Q <- x] \<rightarrow>[m] M'[Q <- x])"
        using step(1) lex.prems lex(1)[of k' M''] by simp
      moreover have "M[Q <- x] \<rightarrow> M''[Q <- x]"
        using \<open>M \<rightarrow> M''\<close> beta_usubst sorry
      ultimately show ?thesis
        using diverge.intros[of "M[Q <- x]" "M''[Q <- x]"] 
        using betas.step[of "M[Q <- x]" "M''[Q <- x]" _ _]
        by blast
    qed
  qed
qed

inductive b5_prop :: "'var::var term \<Rightarrow> bool" where
  "(V \<noteq> Fix _ _ _ \<Longrightarrow> W = V) \<Longrightarrow> b5_prop W" (* no correct, should be if V has Fix _ _ _ as subterm. Is there is subterm predicate defined?*)
| "(V = Pair V1 V2 \<Longrightarrow> W = Pair W1[P <- z] W2[P <- z] \<and> W1[N <- z] = V1 \<and> W2[N <- z] = V2) \<Longrightarrow> b5_prop W"
| "(V = Fix f x P \<Longrightarrow> W = Fix f x Q[P <- z] \<and> Q[N <- z] = P) \<Longrightarrow> b5_prop W"

lemma b5:
  assumes "M[N <- z] = V" and "val V" and "N \<greatersim> P"
  shows "diverge M[P <- z] \<or> (M[P <- z] \<rightarrow>* W \<and> b5_prop W)"
  sorry

lemma b6:
  assumes "stuck M[N <- z]" and "N \<greatersim> P"
  shows "diverge M[P <- z] \<or> stuck M[P <- z]"
  sorry

term FVars_term
end