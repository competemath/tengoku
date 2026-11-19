import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Permutation-native cycle-index polynomials, and the algebraic gluing lemma
relating `sumCongr` to disjoint unions of cycle type, needed for
Theorem `thm:strong`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial

/-- The cycle-indicator monomial of a permutation: `X_1^(fixed points) * ∏ X_ℓ` over its
(non-trivial) cycle lengths `ℓ`, matching the manuscript's `[X^λ]` convention where `λ`
includes fixed points as length-`1` cycles.-/
noncomputable def ci {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    MvPolynomial ℕ ℤ :=
  X 1 ^ (Fintype.card α - g.cycleType.sum) * (g.cycleType.map X).prod

/-- The permutation-native cycle-index polynomial on `n` labels.-/
noncomputable def Cperm (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ g : Equiv.Perm (Fin n), ci g

/--
@isnad1 id=eq.0h3v.s5.0416a98c53b5 from=translated src=- shape=6db72262 vocab=895b745b
-/
lemma ci_conj {α : Type*} [Fintype α] [DecidableEq α] (h g : Equiv.Perm α) :
    ci (h * g * h⁻¹) = ci g := by
  simp [ci, Equiv.Perm.cycleType_conj]

/-- `sumCongr σ 1` has the same cycle type as `σ`, via `extendDomain`.
@isnad1 id=eq.0h3v.s6.7784ff6b2590 from=translated src=- shape=a56b6709 vocab=806a030a
-/
lemma cycleType_sumCongr_one_right {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (σ : Equiv.Perm m) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm n)).cycleType = σ.cycleType := by
  set f : m ≃ Subtype (· ∈ Set.range (Sum.inl : m → m ⊕ n)) :=
    Equiv.ofInjective Sum.inl Sum.inl_injective with hf
  have hext : σ.extendDomain f = Equiv.Perm.sumCongr σ (1 : Equiv.Perm n) := by
    ext x
    cases x with
    | inl a =>
      have himg : (f a : m ⊕ n) = Sum.inl a := rfl
      rw [← himg, Equiv.Perm.extendDomain_apply_image]
      rfl
    | inr b =>
      have hnp : (Sum.inr b : m ⊕ n) ∉ Set.range (Sum.inl : m → m ⊕ n) := by
        rintro ⟨a, ha⟩; cases ha
      rw [Equiv.Perm.extendDomain_apply_not_subtype σ f hnp]
      simp
  rw [← hext, Equiv.Perm.cycleType_extendDomain]

/-- `sumCongr 1 τ` has the same cycle type as `τ`, via `extendDomain`.
@isnad1 id=eq.0h3v.s6.be947eb63c21 from=translated src=- shape=14008578 vocab=806a030a
-/
lemma cycleType_sumCongr_one_left {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (τ : Equiv.Perm n) :
    (Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ).cycleType = τ.cycleType := by
  set f : n ≃ Subtype (· ∈ Set.range (Sum.inr : n → m ⊕ n)) :=
    Equiv.ofInjective Sum.inr Sum.inr_injective with hf
  have hext : τ.extendDomain f = Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ := by
    ext x
    cases x with
    | inr b =>
      have himg : (f b : m ⊕ n) = Sum.inr b := rfl
      rw [← himg, Equiv.Perm.extendDomain_apply_image]
      rfl
    | inl a =>
      have hnp : (Sum.inl a : m ⊕ n) ∉ Set.range (Sum.inr : n → m ⊕ n) := by
        rintro ⟨b, hb⟩; cases hb
      rw [Equiv.Perm.extendDomain_apply_not_subtype τ f hnp]
      simp
  rw [← hext, Equiv.Perm.cycleType_extendDomain]

/-- The two factors `sumCongr σ 1` and `sumCongr 1 τ` are disjoint permutations.
@isnad1 id=disjoint.0h4v.s5.e727a086ed98 from=translated src=- shape=77e92a86 vocab=d91c28ae
-/
lemma disjoint_sumCongr_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    Equiv.Perm.Disjoint (Equiv.Perm.sumCongr σ (1 : Equiv.Perm n))
      (Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ) := by
  intro x
  cases x with
  | inl a => right; simp
  | inr b => left; simp

/-- **Cycle-type gluing**: `cycleType (sumCongr σ τ) = cycleType σ + cycleType τ`.
@isnad1 id=eq.0h4v.s6.d1dd6fdf230d from=translated src=- shape=3d1af121 vocab=be22a544
-/
theorem cycleType_sumCongr {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    (Equiv.Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  have hmul : Equiv.Perm.sumCongr σ τ =
      Equiv.Perm.sumCongr σ (1 : Equiv.Perm n) * Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ := by
    ext x
    cases x with
    | inl a => simp
    | inr b => simp
  rw [hmul, (disjoint_sumCongr_one σ τ).cycleType_mul, cycleType_sumCongr_one_right,
    cycleType_sumCongr_one_left]

/-- The permutation-native cycle-index polynomial on a `2n`-label domain, modeled as
`Fin n ⊕ Fin n`.-/
noncomputable def CpermSum (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ g : Equiv.Perm (Fin n ⊕ Fin n), ci g

/-- The subgroup `H = Perm A × Perm B` embedded in `Perm (Fin n ⊕ Fin n)`, as a `Finset`.-/
noncomputable def HSet (n : ℕ) : Finset (Equiv.Perm (Fin n ⊕ Fin n)) :=
  Finset.univ.filter (· ∈ (Equiv.Perm.sumCongrHom (Fin n) (Fin n)).range)

end CongruenceTheory
