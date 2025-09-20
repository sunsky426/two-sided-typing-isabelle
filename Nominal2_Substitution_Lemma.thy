theory Nominal2_Substitution_Lemma
imports Nominal2.Nominal2
begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

atom_decl var

nominal_datatype "term" = Var var | App "term" "term" | Lam x::"var" t::"term" binds x in t

nominal_function subst :: "term \<Rightarrow> term \<Rightarrow> var \<Rightarrow> term" ("_[_ '/ _]" [1000, 49, 49] 1000) where
  "(Var x)[s / y] = (if x = y then s else Var x)"
| "(App t u)[s / y] = App (t[s / y]) (u[s / y])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[s / y] = Lam x (t[s / y])"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def subst_graph_aux_def)
  subgoal by (erule subst_graph.induct) (auto simp: fresh_star_def fresh_at_base)
                      apply clarify
  subgoal for P t s y
    by (rule term.strong_exhaust[of t P "(s, y)"]) (auto simp: fresh_star_def fresh_Pair)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for x' y' s' t' x t
    apply (erule Abs_lst1_fcb2'[where c = "(s', y')"])
       apply (simp_all add: eqvt_at_def fresh_star_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    apply (metis fresh_star_def fresh_star_supp_conv supp_perm_eq_test)
    apply (metis fresh_star_def fresh_star_supp_conv supp_perm_eq_test)
    done
  done

nominal_termination (eqvt)
  by lexicographic_order

thm subst.eqvt

lemma fresh_subst[simp]: "atom x \<sharp> t \<Longrightarrow> atom x \<sharp> s \<Longrightarrow> atom (x :: var) \<sharp> t[s / y]"
  by (nominal_induct t avoiding: s y rule: term.strong_induct) auto

lemma subst_idle[simp]: "atom y \<sharp> t \<Longrightarrow> t[s / y] = t"
  by (nominal_induct t avoiding: s y rule: term.strong_induct)
    (auto simp: fresh_at_base)

thm term.strong_induct[no_vars]

lemma subst_subst: "y1 \<noteq> y2 \<Longrightarrow> atom y1 \<sharp> s2 \<Longrightarrow> t[s1 / y1][s2 / y2] = t[s2 / y2][s1[s2 / y2] / y1]"
  by (nominal_induct t avoiding: y1 y2 s1 s2 rule: term.strong_induct) auto

inductive beta :: "term \<Rightarrow> term \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50) where
    beta[simp]: "atom x \<sharp> t \<Longrightarrow> App (Lam x s) t \<rightarrow>\<^sub>\<beta> s[t/x]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> App s u \<rightarrow>\<^sub>\<beta> App t u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> App u s \<rightarrow>\<^sub>\<beta> App u t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Lam x s \<rightarrow>\<^sub>\<beta> Lam x t"

lemma fresh_subst': "atom x \<sharp> s \<Longrightarrow> atom x \<sharp> t[s / x]"
  by (nominal_induct t avoiding: s x rule: term.strong_induct) auto

equivariance beta
nominal_inductive beta avoids beta: x | abs: x by (auto simp: fresh_star_def fresh_subst')

theorem subst_preserves_beta[simp]: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r[t/i] \<rightarrow>\<^sub>\<beta> s[t/i]"
  by (nominal_induct avoiding: t i rule: beta.strong_induct) (simp_all add: subst_subst)

lemma "App (Lam x s) t \<rightarrow>\<^sub>\<beta> s[t/x]"
proof -
  obtain y :: var where y: "atom y \<sharp> (x, s, t)" by (rule obtain_fresh)
  then have "Lam x s = Lam y (s[Var y/x])"
    by (nominal_induct s avoiding: t x y rule: term.strong_induct)
      (auto simp: fresh_Pair fresh_at_base)
  also from y have "App (Lam y (s[Var y/x])) t \<rightarrow>\<^sub>\<beta> s[Var y/x][t/y]"
    by (intro beta) simp
  also from y have "s[Var y/x][t/y] = s[t/x]"
    by (nominal_induct s avoiding: t x y rule: term.strong_induct)
      (auto simp: fresh_Pair fresh_at_base)
  finally show ?thesis .
qed

end