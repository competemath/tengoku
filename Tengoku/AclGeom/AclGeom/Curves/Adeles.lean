/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Genus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Adeles of a function field

The places-indexed adele space: families `α P` of field elements that
are integral at all but finitely many places, filtered by the divisor
bounds `A(D)` (`adeleSpace`). The Riemann–Roch space is the pullback of
`A(D)` along the diagonal, and the one-point decomposition
`A(D + P) = A(D) ⊔ span {monomial}` is the local counting device of the
duality theory (Stichtenoth 1.5): unlike its `L(D)`-counterpart the
spanning monomial always exists, concentrated at the single place `P`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

variable (k F) in
/-- The **adele space** of the function field: families of field
elements integral at all but finitely many places.-/
noncomputable def adeleSubmodule : Submodule k ((P : Place k F) → F) where
  carrier := {α | {P : Place k F | α P ≠ 0 ∧ P.ord (α P) < 0}.Finite}
  zero_mem' := by
    refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
    exact absurd rfl hP.1
  add_mem' := by
    intro α β hα hβ
    refine Set.Finite.subset (hα.union hβ) fun P hP ↦ ?_
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at hP
    obtain ⟨hne, hlt⟩ := hP
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases eq_or_ne (α P) 0 with h0 | h0
    · rw [h0, zero_add] at hne hlt
      exact absurd (h2 hne) (by omega)
    rcases eq_or_ne (β P) 0 with h0' | h0'
    · rw [h0', add_zero] at hne hlt
      exact absurd (h1 h0) (by omega)
    have h3 := P.min_ord_le_ord_add h0 h0' hne
    have h4 := h1 h0
    have h5 := h2 h0'
    rcases min_cases (P.ord (α P)) (P.ord (β P)) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
      rw [hm] at h3 <;> omega
  smul_mem' := by
    intro c α hα
    rcases eq_or_ne c 0 with rfl | hc0
    · refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
      simp only [Set.mem_ofPred_eq, Pi.smul_apply, zero_smul] at hP
      exact absurd rfl hP.1
    · refine Set.Finite.subset hα fun P hP ↦ ?_
      simp only [Set.mem_ofPred_eq, Pi.smul_apply] at hP ⊢
      obtain ⟨hne, hlt⟩ := hP
      have h0 : α P ≠ 0 := fun h ↦ hne (by rw [h, smul_zero])
      refine ⟨h0, ?_⟩
      have h1 : P.ord (c • α P) = P.ord (α P) := by
        rw [Algebra.smul_def,
          P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) h0,
          P.ord_algebraMap hc0, zero_add]
      rw [h1] at hlt
      exact hlt

/-- The divisor-bounded adele space `A(D)`: families whose order at
each place `P` is at least `-D P`.-/
noncomputable def adeleSpace (D : Divisor k F) :
    Submodule k ((P : Place k F) → F) where
  carrier := {α | ∀ P : Place k F, α P = 0 ∨ -(D P) ≤ P.ord (α P)}
  zero_mem' := fun _ ↦ Or.inl rfl
  add_mem' := by
    intro α β hα hβ P
    rcases eq_or_ne (α P) 0 with h0 | h0
    · have h : (α + β) P = β P := by rw [Pi.add_apply, h0, zero_add]
      rw [h]
      exact hβ P
    rcases eq_or_ne (β P) 0 with h0' | h0'
    · have h : (α + β) P = α P := by rw [Pi.add_apply, h0', add_zero]
      rw [h]
      exact hα P
    rcases eq_or_ne ((α + β) P) 0 with h0'' | h0''
    · exact Or.inl h0''
    have h1 := (hα P).resolve_left h0
    have h2 := (hβ P).resolve_left h0'
    refine Or.inr ?_
    rw [Pi.add_apply] at h0'' ⊢
    exact le_trans (le_min h1 h2) (P.min_ord_le_ord_add h0 h0' h0'')
  smul_mem' := by
    intro c α hα P
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (by rw [Pi.smul_apply, zero_smul])
    rcases eq_or_ne (α P) 0 with h0 | h0
    · exact Or.inl (by rw [Pi.smul_apply, h0, smul_zero])
    have h1 := (hα P).resolve_left h0
    refine Or.inr ?_
    rw [Pi.smul_apply, Algebra.smul_def,
      P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) h0,
      P.ord_algebraMap hc0, zero_add]
    exact h1

/-- Monotonicity of the bounded adele spaces.
@isnad1 id=le.1h4v.s8.a74f0f4a9876 from=translated src=- shape=eabeed95 vocab=9d1007fe
-/
theorem adeleSpace_mono {D E : Divisor k F} (h : D ≤ E) :
    adeleSpace D ≤ adeleSpace (E : Divisor k F) := by
  intro α hα P
  rcases hα P with h0 | h0
  · exact Or.inl h0
  · have := h P
    exact Or.inr (by omega)

/-- Bounded adeles are adeles: the exceptional places lie in the
support of the divisor.
@isnad1 id=le.0h3v.s8.ada4123dd66a from=translated src=- shape=e06c6518 vocab=7b62b5c1
-/
theorem adeleSpace_le_adeleSubmodule (D : Divisor k F) :
    adeleSpace D ≤ adeleSubmodule k F := by
  intro α hα
  refine Set.Finite.subset D.hasFiniteSupport fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq] at hP
  obtain ⟨hne, hlt⟩ := hP
  have h1 := (hα P).resolve_left hne
  rw [Function.mem_support]
  omega

variable (k F) in
/-- The diagonal embedding of the function field into place-indexed
families.-/
noncomputable def adeleDiagonal : F →ₗ[k] ((P : Place k F) → F) :=
  LinearMap.pi fun _ ↦ LinearMap.id

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/--
@isnad1 id=eq.0h4v.s8.7412765d3d7b from=translated src=- shape=44d39984 vocab=a857ee84
-/
@[simp]
theorem adeleDiagonal_apply (f : F) (P : Place k F) :
    adeleDiagonal k F f P = f := rfl

/-- Diagonal families are adeles: the exceptional places are the poles.
@isnad1 id=mem.0h3v.s9.179a38a9089a from=translated src=- shape=497ba3f9 vocab=7952dfbb
-/
theorem adeleDiagonal_mem_adeleSubmodule (f : F) :
    adeleDiagonal k F f ∈ adeleSubmodule k F := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [map_zero]
    exact zero_mem _
  refine Set.Finite.subset (finite_setOf_one_lt_valuation hf0)
    fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq, adeleDiagonal_apply] at hP ⊢
  obtain ⟨-, hlt⟩ := hP
  by_contra hle
  push Not at hle
  exact absurd ((P.ord_nonneg_iff hf0).2 hle) (by omega)

section OnePoint

variable (P : Place k F)

open Classical in
/-- The **monomial adele**: the uniformizer power `π_P ^ n`
concentrated at the single place `P`.-/
noncomputable def adeleMonomial (n : ℤ) : (Q : Place k F) → F :=
  fun Q ↦ if Q = P then P.pi ^ n else 0

/--
@isnad1 id=eq.0h4v.s6.a7057c818a92 from=translated src=- shape=d1c81f92 vocab=724ebecf
-/
theorem adeleMonomial_apply_self (n : ℤ) :
    adeleMonomial P n P = P.pi ^ n := ite_eq_left rfl

/--
@isnad1 id=eq.1h5v.s6.3cd970c44876 from=translated src=- shape=faea3a0e vocab=fc6c9fbd
-/
theorem adeleMonomial_apply_ne {Q : Place k F} (hQ : Q ≠ P) (n : ℤ) :
    adeleMonomial P n Q = 0 := ite_eq_right hQ

/--
@isnad1 id=eq.0h4v.s6.fcd42265793b from=translated src=- shape=775d08aa vocab=1517353c
-/
theorem ord_pi_zpow (n : ℤ) : P.ord (P.pi ^ n) = n := by
  rw [P.ord_zpow P.pi_ne_zero, P.ord_pi, mul_one]

/-- The monomial adele lies in `A(D)` as soon as its order clears the
bound at `P`.
@isnad1 id=mem.1h5v.s8.d97f8a25755c from=translated src=- shape=3559f68a vocab=c4b05f63
-/
theorem adeleMonomial_mem_adeleSpace {D : Divisor k F} {n : ℤ}
    (h : -(D P) ≤ n) : adeleMonomial P n ∈ adeleSpace D := by
  intro Q
  rcases eq_or_ne Q P with rfl | hQ
  · refine Or.inr ?_
    rw [adeleMonomial_apply_self, ord_pi_zpow]
    exact h
  · exact Or.inl (adeleMonomial_apply_ne P hQ n)

end OnePoint

section Surjectivity

end Surjectivity

end

end AclGeom
