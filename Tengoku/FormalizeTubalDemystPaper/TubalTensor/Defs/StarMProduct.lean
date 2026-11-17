import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Defs.RealPaired

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Defs/StarMProduct.lean
  Definition of the ⋆_M product.

  The ⋆_M product is defined as: a ⋆_M b := M⁻¹(Ma ∘ₕ Mb)
  where ∘ₕ is the Hadamard (entrywise) product.
-/

namespace TubalTensor

open Complex Matrix

variable {n : ℕ}

/-! ## The ⋆_M product (Equation 5 in the paper) -/

/-- The ⋆_M product on complex vectors: M⁻¹(Ma ∘ₕ Mb).
    This is the "lifted" version on ℂⁿ.-/
noncomputable def starMC (td : TubalData n) (a b : Fin n → ℂ) : Fin n → ℂ :=
  td.applyMinv (td.applyM a ∘ₕ td.applyM b)

/-- The ⋆_M product on real vectors: take the real part of M⁻¹(Ma ∘ₕ Mb).
    When M satisfies the realness condition, this equals the complex version.-/
noncomputable def starM (td : TubalData n) (a b : Fin n → ℝ) : Fin n → ℝ :=
  vecRe (starMC td (toComplex a) (toComplex b))

/-! ## Key property: applying M to a real vector respects the real-paired structure -/

/-- If M is real-paired and a is real, then (Ma)_i is real when row i is real.
@isnad1 id=eq.1h4v.s5.7dcd3e6a398f from=translated src=- shape=120d77f5 vocab=a9fb6d7c
-/
theorem applyM_real_row {td : TubalData n} {a : Fin n → ℝ} {i : Fin n}
    (hrow : IsRealRow td.M i) : (td.applyM (toComplex a) i).im = 0 := by
  simp only [TubalData.applyM_apply]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hr : (td.M i j).im = 0 := hrow j
  simp only [toComplex_apply, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, hr, zero_mul, add_zero]

/-- If M is real-paired and a is real, then for conjugate-pair rows i, k:
    (Ma)_k = conj((Ma)_i).
@isnad1 id=eq.1h5v.s6.91f54324c805 from=translated src=- shape=0094af5f vocab=877f5e85
-/
theorem applyM_conj_row {td : TubalData n} {a : Fin n → ℝ} {i k : Fin n}
    (hconj : IsConjRow td.M i k) :
    td.applyM (toComplex a) k = starRingEnd ℂ (td.applyM (toComplex a) i) := by
  simp only [TubalData.applyM_apply, map_sum, map_mul]
  congr 1
  ext j
  rw [hconj j]
  simp [toComplex_apply, Complex.conj_ofReal]

/-- A vector v has the "real-paired structure" w.r.t. M: real entries for real rows,
    conjugate-pair entries for conjugate-pair rows.-/
def HasRealPairedStructure (td : TubalData n) (v : Fin n → ℂ) : Prop :=
  (∀ i, IsRealRow td.M i → (v i).im = 0) ∧
  (∀ i k, k ≠ i → IsConjRow td.M i k → v k = starRingEnd ℂ (v i))

/-- Applying M to a real vector produces a vector with real-paired structure.
@isnad1 id=hasrealp.0h3v.s4.663b51e07f2e from=translated src=- shape=2cab76d7 vocab=8b88ae5c
-/
theorem applyM_toComplex_hasPairedStructure (td : TubalData n) (a : Fin n → ℝ) :
    HasRealPairedStructure td (td.applyM (toComplex a)) :=
  ⟨fun _ h => applyM_real_row h, fun _ _ _ h => applyM_conj_row h⟩

/-- The Hadamard product of two vectors with real-paired structure also has
    real-paired structure.
@isnad1 id=hasrealp.2h4v.s5.14a72f4585cc from=translated src=- shape=586c417f vocab=20f65b68
-/
theorem vecHadamard_hasPairedStructure {td : TubalData n} {u v : Fin n → ℂ}
    (hu : HasRealPairedStructure td u) (hv : HasRealPairedStructure td v) :
    HasRealPairedStructure td (u ∘ₕ v) := by
  constructor
  · intro i hrow
    simp only [vecHadamard_apply]
    have hure : (u i).im = 0 := hu.1 i hrow
    have hvre : (v i).im = 0 := hv.1 i hrow
    simp only [Complex.mul_im, hure, hvre, mul_zero, zero_mul, add_zero]
  · intro i k hki hconj
    simp only [vecHadamard_apply]
    rw [hu.2 i k hki hconj, hv.2 i k hki hconj]
    show starRingEnd ℂ (u i) * starRingEnd ℂ (v i) = starRingEnd ℂ (u i * v i)
    rw [map_mul]

end TubalTensor
