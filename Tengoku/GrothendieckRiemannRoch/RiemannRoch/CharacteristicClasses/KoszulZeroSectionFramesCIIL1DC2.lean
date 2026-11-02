/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.KoszulChartAlgebraCIIL1DA

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route CIIL1DC2, algebra leaves for the arbitrary-frame zero-section charts

Two self-contained commutative-algebra facts used by the arbitrary-frame analysis of the zero
section of `ℙ(N ⊞ 𝟙)`:

* `isWeaklyRegular_X_sub_C_ofFn`: for arbitrary constants `a : Fin n → R`, the *translated*
  coordinates `Xⱼ - aⱼ` form a weakly regular sequence in `R[X₀,…,X_{n-1}]`.  This is the
  regularity input at points of a chart `D₊(b_k)` where `c_k` is a unit: after the affine change
  of variable `y'ⱼ = yⱼ - cⱼ/c_k` the `σ`-values are (unit multiples of) these translated
  coordinates.  Proved by transporting the parent's `isWeaklyRegular_X_ofFn` along the translation
  automorphism `Xⱼ ↦ Xⱼ - aⱼ`.

* `isWeaklyRegular_cons_of_isUnit`: any list whose head is a unit is weakly regular (the Koszul
  complex of a cosection one of whose values is a unit is contractible).  This is the regularity
  input at points `x ∉ s(X)`, where after shrinking some `σ`-value `eⱼ` is a unit and the chosen
  frame is reordered to put it first.

Both are transport/bookkeeping lemmas on top of `RingTheory.Sequence.IsWeaklyRegular`; neither
introduces a new axiom.
-/

set_option autoImplicit false
noncomputable section
open MvPolynomial RingTheory.Sequence

namespace SchemeKTheory.KoszulChartAlgebra

variable (R : Type*) [CommRing R]

/-- The `R`-algebra automorphism of `R[X₀,…,X_{n-1}]` translating `Xⱼ ↦ Xⱼ - aⱼ`.-/
def shiftAlgEquiv {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom
    (aeval fun j => (X j - C (a j) : MvPolynomial (Fin n) R))
    (aeval fun j => (X j + C (a j) : MvPolynomial (Fin n) R))
    (by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, aeval_X, map_add, aeval_C, MvPolynomial.algebraMap_eq,
        AlgHom.id_apply]
      ring)
    (by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, aeval_X, map_sub, aeval_C, MvPolynomial.algebraMap_eq,
        AlgHom.id_apply]
      ring)

@[simp] theorem shiftAlgEquiv_X {n : ℕ} (a : Fin n → R) (j : Fin n) :
    shiftAlgEquiv R a (X j) = X j - C (a j) := by
  simp [shiftAlgEquiv]

end SchemeKTheory.KoszulChartAlgebra

namespace RiemannRoch.CIIL1DC2

open RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A module quotiented by a unit multiple of the whole module is subsingleton.-/
theorem subsingleton_quotSMulTop_of_isUnit {r : R} (hr : IsUnit r) :
    Subsingleton (QuotSMulTop r M) := by
  have htop : r • (⊤ : Submodule R M) = ⊤ := by
    obtain ⟨u, rfl⟩ := hr
    refine top_le_iff.mp fun x _ => ?_
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨(↑u⁻¹ : R) • x, trivial, by rw [smul_smul]; simp⟩
  exact Submodule.Quotient.subsingleton_iff.mpr htop

/-- A weakly regular sequence over a subsingleton module is automatic.-/
theorem isWeaklyRegular_of_subsingleton [Subsingleton M] (rs : List R) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsWeaklyRegular.nil R M
  | cons r rs ih =>
    refine IsWeaklyRegular.cons (fun a b _ => Subsingleton.elim a b) ?_
    haveI : Subsingleton (QuotSMulTop r M) :=
      Function.Surjective.subsingleton (Submodule.Quotient.mk_surjective _)
    exact ih

/-- Any list whose head is a unit is a weakly regular sequence.-/
theorem isWeaklyRegular_cons_of_isUnit {r : R} (hr : IsUnit r) (rs : List R) :
    IsWeaklyRegular M (r :: rs) := by
  refine IsWeaklyRegular.cons (hr.isSMulRegular (M := M)) ?_
  haveI := subsingleton_quotSMulTop_of_isUnit (M := M) hr
  exact isWeaklyRegular_of_subsingleton rs

end RiemannRoch.CIIL1DC2
