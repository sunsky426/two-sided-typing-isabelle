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

binder_datatype 'var "ctx" =
  Hole
  | CtxSucc "'var ctx"
  | CtxPred "'var ctx"
  | CtxIf1 "'var ctx" "'var term" "'var term"
  | CtxIf2 "'var term" "'var ctx" "'var term"
  | CtxIf3 "'var term" "'var term" "'var ctx"
  | CtxAppL "'var ctx" "'var term"
  | CtxAppR "'var term" "'var ctx"
  | CtxFix f::'var x::'var M::"'var ctx" binds f x in M
  | CtxPairL "'var ctx" "'var term"
  | CtxPairR "'var term" "'var ctx"
  | CtxLet1 "(xy::'var) dpair" M::"'var ctx" N::"'var term" binds xy in N
  | CtxLet2 "(xy::'var) dpair" M::"'var term" N::"'var ctx" binds xy in N

function plug :: "'var::var ctx \<Rightarrow> 'var term \<Rightarrow> 'var term" ("_[[_]]")  where
  "plug Hole X = X"
| "plug (CtxSucc ctx) X = Succ (plug ctx X)"
| "plug (CtxPred ctx) X = Pred (plug ctx X)"
| "plug (CtxIf1 ctx M N) X = If (plug ctx X) M N"
| "plug (CtxIf2 M ctx N) X = If M (plug ctx X) N"
| "plug (CtxIf3 M N ctx) X = If M N (plug ctx X)"
| "plug (CtxAppL ctx N) X = App (plug ctx X) N"
| "plug (CtxAppR M ctx) X = App M (plug ctx X)"
| "plug (CtxFix f x ctx) X = Fix f x (plug ctx X)"
| "plug (CtxPairL ctx N) X = Pair (plug ctx X) N"
| "plug (CtxPairR M ctx) X = Pair M (plug ctx X)"
| "plug (CtxLet1 x ctx N) X = Let x (plug ctx X) N"
| "plug (CtxLet2 x M ctx) X = Let x M (plug ctx X)"
  sorry

definition usubst ("_[_ <- _]" [1000, 49, 49] 1000) where
  "usubst t u x = tvsubst_term (Var(x := u)) t"

function ctx_subst :: "'var::var ctx \<Rightarrow> 'var term \<Rightarrow> 'var \<Rightarrow> 'var ctx" ("_[[_<-_]]" [1000, 49, 49] 1000) where
  "ctx_subst Hole t z = Hole"
| "ctx_subst (CtxSucc ctx) t z = CtxSucc (ctx_subst ctx t z)"
| "ctx_subst (CtxPred ctx) t z = CtxPred (ctx_subst ctx t z)"
| "ctx_subst (CtxIf1 ctx M N) t z = CtxIf1 (ctx_subst ctx t z) M[t <- z] N[t <- z]"
| "ctx_subst (CtxIf2 M ctx N) t z = CtxIf2 M[t <- z] (ctx_subst ctx t z) N[t <- z]"
| "ctx_subst (CtxIf3 M N ctx) t z = CtxIf3 M[t <- z] N[t <- z] (ctx_subst ctx t z)"
| "ctx_subst (CtxAppL ctx N) t z = CtxAppL (ctx_subst ctx t z) N[t <- z]"
| "ctx_subst (CtxAppR M ctx) t z = CtxAppR M[t <- z] (ctx_subst ctx t z)"
| "ctx_subst (CtxFix f x ctx) t z = CtxFix f x (ctx_subst ctx t z)"
| "ctx_subst (CtxPairL ctx N) t z = CtxPairL (ctx_subst ctx t z) N"
| "ctx_subst (CtxPairR M ctx) t z = CtxPairR M[t <- z] (ctx_subst ctx t z)"
| "ctx_subst (CtxLet1 x ctx N) t z = CtxLet1 x (ctx_subst ctx t z) N[t <- z]"
| "ctx_subst (CtxLet2 x M ctx) t z = CtxLet2 x M[t <- z] (ctx_subst ctx t z)"
  sorry

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
  "dset xy \<inter> {y} = {} \<Longrightarrow> dset xy \<inter> FVars_term u = {} \<Longrightarrow> dset xy \<inter> FVars_term t1 = {} \<Longrightarrow>
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

inductive eval_ctx :: "'var::var ctx \<Rightarrow> bool" where
  "eval_ctx (CtxAppR (Fix f x M) Hole)"
| "eval_ctx (CtxAppL Hole N)"
| "eval_ctx (CtxSucc Hole)"
| "eval_ctx (CtxPred Hole)"
| "eval_ctx (CtxPairL Hole N)"
| "val V \<Longrightarrow> eval_ctx (CtxPairR V Hole)"
| "eval_ctx (CtxLet1 x Hole N)"
| "eval_ctx (CtxIf1 Hole N P)"

inductive stuckExp :: "'var::var term \<Rightarrow> bool" where
  "\<lbrakk> val V ; \<not> num V \<rbrakk> \<Longrightarrow> stuckExp (Pred V)"
| "\<lbrakk> val V ; \<not> num V \<rbrakk> \<Longrightarrow> stuckExp (Succ V)"
| "\<lbrakk> val V ; \<not> num V \<rbrakk> \<Longrightarrow> stuckExp (If V _ _)"
| "\<lbrakk> val V ; V \<noteq> Fix _ _ _ \<rbrakk> \<Longrightarrow> stuckExp (App V M)"
| "\<lbrakk> val V ; V \<noteq> Pair _ _ \<rbrakk> \<Longrightarrow> stuckExp (Let x V M)"

inductive stuck :: "'var::var term \<Rightarrow> bool" where
  "stuckExp M \<Longrightarrow> stuck M"
| "eval_ctx E \<Longrightarrow> stuck M \<Longrightarrow> stuck (plug E M)"

inductive beta :: "'var::var term \<Rightarrow> 'var::var term \<Rightarrow> bool"  (infix "\<rightarrow>" 70) where
  "eval_ctx E \<Longrightarrow> M \<rightarrow> M' \<Longrightarrow> E[[M]] \<rightarrow> E[[M']]"
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

lemma "val M \<or> stuck M \<or> (\<exists>N. M \<rightarrow> N)"
  apply(induction M)
  apply(simp_all add:num.intros val.intros)
  apply(erule disjE) (*I wanted to apply to all subgoals here*)
  sorry

lemma "(\<exists>N. M \<rightarrow>* N \<and> val N) \<or> (\<exists>N. M \<rightarrow>* N \<and> stuck N) \<or> (M \<Up>)"
  sorry

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

inductive blocked :: "'var :: var \<Rightarrow> 'var term \<Rightarrow> bool" where
  "blocked z (App (Fix f x M) (Var z))"
| "blocked z N \<Longrightarrow> blocked z (App (Fix f x M) N)"
| "blocked z (App (Var z) N)"
| "blocked z M ==> blocked z (App M N)"
| "blocked z (Succ (Var z))"
| "blocked z M \<Longrightarrow> blocked z (Succ M)"
| "blocked z (Pred (Var z))"
| "blocked z M \<Longrightarrow> blocked z (Pred M)"
| "blocked z (Pair (Var z) N)"
| "blocked z M ==> blocked z (Pair M N)"
| "val V ==> blocked z (Pair V (Var z))"
| "val V ==> blocked z M ==> blocked z (Pair V M)"
| "blocked z (Let x (Var z) N)"
| "blocked z M \<Longrightarrow> blocked z (Let x M N)"
| "blocked z (If (Var z) N P)"
| "blocked z M \<Longrightarrow> blocked z (If M N P)"

lemma B1: "\<lbrakk> M[N <- z] = plug E P; \<not> blocked z M \<rbrakk> \<Longrightarrow> \<exists>F P'. (M = plug F P' \<and> E = F[[N<-z]] \<and> P = P'[N<-z])"
proof(induction E)
  case 1
  have "Hole[[P]] = P" by simp
  then have "M[N <- z] = P" by auto
  obtain "F = Hole" "P' = M"
  then show ?case sorry
next
  case (2 E)
  then show ?case sorry
next
  case (3 E)
  then show ?case sorry
next
  case (4 E x2 x3)
  then show ?case sorry
next
  case (5 x1 E x3)
  then show ?case sorry
next
  case (6 x1 x2 E)
  then show ?case sorry
next
  case (7 E x2)
  then show ?case sorry
next
  case (8 x1 E)
  then show ?case sorry
next
  case (9 x1 x2 E)
  then show ?case sorry
next
  case (10 E x2)
  then show ?case sorry
next
  case (11 x1 E)
  then show ?case sorry
next
  case (12 x1 E x3)
  then show ?case sorry
next
  case (13 x1 x2 E)
  then show ?case sorry
qed
end