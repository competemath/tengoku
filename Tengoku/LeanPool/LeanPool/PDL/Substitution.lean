/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Tengoku.LeanPool.LeanPool.PDL.Discon

/-!
# Substitution and Helper Lemmas

The lemmas here are mostly from Sections 2.1 and 2.2.
-/

@[expose] public section

namespace PDL

/-! ## Single-step replacing -/

mutual
  /-- Replace atomic proposition `x` by `ψ` in a formula. -/
  @[simp]
  def replInF (x : Nat) (ψ : Formula) : Formula → Formula
    | ⊥ => ⊥
    | ·c => if c == x then ψ else ·c
    | ~φ => ~ replInF x ψ φ
    | φ1⋀φ2 => (replInF x ψ) φ1 ⋀ (replInF x ψ) φ2
    | ⌈α⌉ φ => ⌈replInP x ψ α⌉ (replInF x ψ φ)
  /-- Replace atomic proposition `x` by `ψ` in a program. -/
  @[simp]
  def replInP (x : Nat) (ψ : Formula) : Program → Program
    | ·c => ·c
    | α;'β  => (replInP x ψ α) ;' (replInP x ψ β)
    | α⋓β  => (replInP x ψ α) ⋓ (replInP x ψ β)
    | ∗α  => ∗(replInP x ψ α)
    | ?'φ  => ?' (replInF x ψ φ)
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

/--
@isnad1 id=eq.0h3v.s4.1b57aaf5fb8a from=translated src=- shape=62abca2e vocab=6e759d8a
-/
theorem repl_in_con : replInF x ψ (con l) = con (l.map (replInF x ψ)) := by
  cases l
  · simp [Top.top, Bot.bot]
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp only [con, replInF, List.map_cons, Formula.and.injEq, true_and]
      apply repl_in_con

/--
@isnad1 id=eq.0h4v.s4.199fb9b1b5cf from=translated src=- shape=e5dda6fb vocab=3879fe84
-/
theorem repl_in_or : replInF x ψ (φ1 ⋁ φ2) = replInF x ψ φ1 ⋁ replInF x ψ φ2 := by
  simp

/--
@isnad1 id=eq.0h3v.s4.d234fa7b14f5 from=translated src=- shape=62abca2e vocab=afd2ad2c
-/
theorem repl_in_dis : replInF x ψ (dis l) = dis (l.map (replInF x ψ)) := by
  cases l
  · simp
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp only [dis, Formula.or, replInF, List.map_cons, Formula.neg.injEq, Formula.and.injEq,
        true_and]
      apply repl_in_dis

mutual
/--
@isnad1 id=eq.1h3v.s5.b5ff2daed64c from=translated src=- shape=40bdcbe9 vocab=8dba9f67
-/
theorem repl_in_F_non_occ_eq {x φ ρ} :
    (Sum.inl x) ∉ φ.voc → replInF x ρ φ = φ := by
  intro x_notin_phi
  cases φ
  case bottom => simp [Bot.bot]
  case atom_prop c =>
    simp only [replInF, beq_iff_eq, ite_eq_right_iff]
    intro c_is_x; simp only [Formula.voc, Finset.mem_singleton, Sum.inl.injEq] at *; subst_eqs;
      tauto
  case neg φ0 =>
    simp only [Formula.voc, replInF, Formula.neg.injEq] at *
    apply repl_in_F_non_occ_eq; tauto
  case and φ1 φ2 =>
    simp only [Formula.voc, Finset.mem_union, not_or, replInF, Formula.and.injEq] at *
    constructor <;> (apply repl_in_F_non_occ_eq ; tauto)
  case box α φ0 =>
    simp only [Formula.voc, Finset.mem_union, not_or, replInF, Formula.box.injEq] at *
    constructor
    · apply repl_in_P_non_occ_eq; tauto
    · apply repl_in_F_non_occ_eq; tauto

/--
@isnad1 id=eq.1h3v.s5.c0a1dfe5fff7 from=translated src=- shape=e9ba8f2f vocab=06fe10c6
-/
theorem repl_in_P_non_occ_eq {x α ρ} :
    (Sum.inl x) ∉ α.voc → replInP x ρ α = α := by
  intro x_notin_alpha
  cases α
  all_goals simp only [Program.voc, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    replInP, Finset.mem_union, not_or, Program.sequence.injEq, Program.union.injEq,
    Program.star.injEq, Program.test.injEq] at *
  case sequence β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case union β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case star β =>
    apply repl_in_P_non_occ_eq; tauto
  case test φ =>
    apply repl_in_F_non_occ_eq; tauto
end

end PDL

namespace PDL

/--
@isnad1 id=eq.1h3v.s5.7d50827736ad from=translated src=- shape=f8a901de vocab=59271100
-/
theorem repl_in_boxes_non_occ_eq_neg (δ : List Program) :
    (Sum.inl x) ∉ Vocab.fromList (δ.map Program.voc) → replInF x ψ (⌈⌈δ⌉⌉~·x) = ⌈⌈δ⌉⌉~ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, List.foldr_cons, replInF, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp_all [Vocab.fromList]
    · apply IH
      clear IH
      simp_all [Vocab.fromList]

/--
@isnad1 id=eq.1h3v.s5.7cfd622b8ada from=translated src=- shape=6bab14bb vocab=39015e01
-/
theorem repl_in_boxes_non_occ_eq_pos (δ : List Program) :
    (Sum.inl x) ∉ Vocab.fromList (δ.map Program.voc) → replInF x ψ (⌈⌈δ⌉⌉·x) = ⌈⌈δ⌉⌉ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, List.foldr_cons, replInF, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp_all [Vocab.fromList]
    · apply IH
      clear IH
      simp_all [Vocab.fromList]

/--
@isnad1 id=eq.1h3v.s5.5e0d73d881e6 from=translated src=- shape=d77b79f3 vocab=13f66c1f
-/
theorem repl_in_list_non_occ_eq (F : List Formula) :
     (Sum.inl x) ∉ Vocab.fromList (F.map Formula.voc) → F.map (replInF x ρ) = F := by
  intro nonOcc
  induction F
  · simp
  case cons φ F IH =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply repl_in_F_non_occ_eq
      simp only [Vocab.fromList, Finset.mem_sup, List.mem_toFinset, List.mem_map, id_eq,
        exists_exists_and_eq_and, not_exists, not_and, List.map_cons, List.toFinset_cons,
        Finset.sup_insert, Finset.sup_eq_union', Finset.mem_union, not_or] at *
      exact nonOcc.left
    · apply IH
      clear IH
      simp_all [Vocab.fromList]

end PDL

namespace PDL

/-- Overwrite the valuation of `x` with the current value of `ψ` in a model. -/
def replInModel (x : Nat) (ψ : Formula) : KripkeModel W → KripkeModel W
| M@⟨V,R⟩ => ⟨fun w c => if c == x then (M,w) ⊨ ψ else V w c,R⟩

mutual
/--
@isnad1 id=iff.0h6v.s5.98f7106c3819 from=translated src=- shape=e41d9d32 vocab=60f1013b
-/
theorem repl_in_model_sat_iff x ψ φ {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ replInF x ψ φ ↔ (replInModel x ψ M, w) ⊨ φ := by
  cases φ
  case bottom =>
    simp [evaluatePoint, vDash.SemImplies]
  case atom_prop c =>
    simp [evaluatePoint, vDash.SemImplies, evaluate, replInModel]
    aesop
  case neg φ =>
    have IH := repl_in_model_sat_iff x ψ φ M w
    simp [evaluatePoint, vDash.SemImplies] at *
    tauto
  case and φ1 φ2 =>
    have IH1 := repl_in_model_sat_iff x ψ φ1 M w
    have IH2 := repl_in_model_sat_iff x ψ φ2 M w
    simp only [vDash.SemImplies, evaluatePoint, replInF, evaluate] at *
    rw [IH1, IH2]
  case box α φ =>
    have IHα := repl_in_model_rel_iff x ψ α M w
    simp only [vDash.SemImplies, evaluatePoint, replInF, evaluate] at *
    constructor
    all_goals
      intro hyp v rel
      have IHφ := repl_in_model_sat_iff x ψ φ M v
      specialize IHα v
      specialize hyp v
      tauto

/--
@isnad1 id=iff.0h7v.s5.835b9f7b51d4 from=translated src=- shape=2498c1be vocab=097d7675
-/
theorem repl_in_model_rel_iff x ψ α {W} (M : KripkeModel W) (w v : W) :
    relate M (replInP x ψ α) w v ↔ relate (replInModel x ψ M) α w v := by
  cases α
  case atom_prog a =>
    simp [replInModel]
  case sequence α β =>
    have IHα := repl_in_model_rel_iff x ψ α M
    have IHβ := repl_in_model_rel_iff x ψ β M
    simp_all only [replInP, relate]
  case union α β =>
    have IHα := repl_in_model_rel_iff x ψ α M
    have IHβ := repl_in_model_rel_iff x ψ β M
    simp_all only [replInP, relate]
  case star α =>
    have IHα := repl_in_model_rel_iff x ψ α M
    simp_all only [replInP, relate]
    constructor
    all_goals
      apply Relation.ReflTransGen.mono
      intro w v
      rw [IHα w v]
  case test φ =>
    have IHφ := repl_in_model_sat_iff x ψ φ M v
    simp only [replInP, relate, and_congr_right_iff] at *
    intro w_is_v
    subst w_is_v
    exact IHφ
end

end PDL

namespace PDL

/--
@isnad1 id=semequiv.1h4v.s4.a4b7a8f96d97 from=translated src=- shape=ebdcef65 vocab=db64c196
-/
theorem repl_in_F_equiv x ψ :
    (φ1 ≡ φ2) → (replInF x ψ φ1) ≡ (replInF x ψ φ2) := by
  intro hyp W M w
  have claim1 := repl_in_model_sat_iff x ψ φ1 M w
  have claim2 := repl_in_model_sat_iff x ψ φ2 M w
  simp only [evaluatePoint, vDash.SemImplies] at *
  rw [claim1]
  rw [claim2]
  have := @equiv_iff φ1 φ2 hyp W (replInModel x ψ M) w
  simp only [evaluatePoint, vDash.SemImplies] at *
  exact this

/--
@isnad1 id=eq.0h6v.s6.1ad0ef7659da from=translated src=- shape=465994bd vocab=d12437e8
-/
theorem repl_in_disMap x ρ (L : List α) (p : α → Prop) (f : α → Formula) [DecidablePred p] :
    replInF x ρ (dis (L.map (fun Fδ => if p Fδ then Formula.bottom else f Fδ))) =
    dis (L.map (fun Fδ => if p Fδ then Formula.bottom else replInF x ρ (f Fδ))) := by
  rw [repl_in_dis, listEq_to_disEq]
  simp only [List.map_map]
  aesop

/-! ## Cancellation of replacements -/

mutual
/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the same formula.
@isnad1 id=eq.1h3v.s5.24bbed13959e from=translated src=- shape=5baf74f5 vocab=ca88d948
-/
@[simp]
lemma repl_in_F_cancel_via_non_occ φ p q : Sum.inl q ∉ φ.voc →
    replInF q (·p) (replInF p (·q) φ) = φ := by
  intro q_not_in_ψ
  cases φ <;> simp_all only [Formula.voc, Finset.notMem_empty, not_false_eq_true, replInF,
    Bot.bot, Finset.mem_singleton, Sum.inl.injEq, beq_iff_eq, Formula.neg.injEq, Finset.mem_union,
    not_or, Formula.and.injEq, Formula.box.injEq]
  case atom_prop q =>
    by_cases q = p <;> aesop
  case neg φ =>
    have := repl_in_F_cancel_via_non_occ φ p q
    aesop
  case and φ1 φ2 =>
    have := repl_in_F_cancel_via_non_occ φ1 p q
    have := repl_in_F_cancel_via_non_occ φ2 p q
    aesop
  case box α φ =>
    have := repl_in_F_cancel_via_non_occ φ p q
    have := repl_in_P_cancel_via_non_occ α p q
    aesop
/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the same program.
@isnad1 id=eq.1h3v.s5.8fab34fc2edd from=translated src=- shape=5baf74f5 vocab=c98bc179
-/
lemma repl_in_P_cancel_via_non_occ α p q : Sum.inl q ∉ α.voc →
    replInP q (·p) (replInP p (·q) α) = α := by
  intro q_not_in_α
  cases α <;> simp_all only [Program.voc, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    replInP, Finset.mem_union, not_or, Program.sequence.injEq, Program.union.injEq,
    Program.star.injEq, Program.test.injEq]
  case sequence α1 α2 =>
    have := repl_in_P_cancel_via_non_occ α1 p q
    have := repl_in_P_cancel_via_non_occ α2 p q
    aesop
  case union α1 α2 =>
    have := repl_in_P_cancel_via_non_occ α1 p q
    have := repl_in_P_cancel_via_non_occ α2 p q
    aesop
  case test τ =>
    have := repl_in_F_cancel_via_non_occ τ p q
    aesop
  case star α =>
    have := repl_in_P_cancel_via_non_occ α p q
    aesop
end

end PDL

namespace PDL

/-! ## Replacement of atoms in tautologies -/

/-! ## Simultaneous Substitutions -/

/-- A substitution assigning a formula to each atomic proposition. -/
abbrev Substitution := Nat → Formula

mutual
  /-- Apply substitution `σ` to formula `φ`. -/
  @[simp]
  def substInF (σ : Substitution) : (φ : Formula) → Formula
    | ⊥ => ⊥
    | ·c => σ c
    | ~φ => ~(substInF σ φ)
    | φ1⋀φ2 => (substInF σ) φ1 ⋀ (substInF σ) φ2
    | ⌈α⌉ φ => ⌈substInP σ α⌉ (substInF σ φ)
  /-- Apply substitution `σ` to program `α`. -/
  @[simp]
  def substInP (σ : Substitution) : (α : Program) → Program
    | ·c => ·c
    | α;'β  => (substInP σ α) ;' (substInP σ β)
    | α⋓β  => (substInP σ α) ⋓ (substInP σ β)
    | ∗α  => ∗(substInP σ α)
    | ?'φ  => ?' (substInF σ φ)
end

end PDL

namespace PDL

/-- Overwrite the valuation in `M` with the substitution `σ`. -/
def substInModel (σ : Substitution) : (M : KripkeModel W) → KripkeModel W
| M@⟨_, R⟩ => ⟨fun w c => (M,w) ⊨ σ c, R⟩

end PDL

namespace PDL

/-! ## Semantic Equivalents

The following does *not* hold in general, because `frm` might be sneaky:
`theorem wrong_equiv_repl φ1 φ2 (h : φ1 ≡ φ2) (frm : Formula → Formula) : frm φ1 ≡ frm φ2 := by ...`
-/

end PDL
