import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Defs.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Defs/RealPaired.lean
  IsRealPaired predicate, TubalData structure.

  The realness condition (Lemma 2 in the paper) states that ⋆_M preserves ℝⁿ
  if and only if every row of M is either entirely real, or is the entrywise
  complex conjugate of exactly one other row.
-/

namespace TubalTensor

open Complex Matrix

/-- A row of a complex matrix is real: all entries have zero imaginary part.-/
def IsRealRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Prop :=
  ∀ j : Fin n, (M i j).im = 0

/-- Row `k` is the complex conjugate of row `i`.-/
def IsConjRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) : Prop :=
  ∀ j : Fin n, M k j = starRingEnd ℂ (M i j)

/-- The realness condition on M (Definition from Section 3.3 / Lemma 2).
    Every row of M is either entirely real, or has exactly one conjugate partner row.-/
def IsRealPaired {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i : Fin n,
    IsRealRow M i ∨
    (∃ k : Fin n, k ≠ i ∧ IsConjRow M i k ∧
      ∀ l : Fin n, l ≠ i → IsConjRow M i l → l = k)

/-- A real row is its own conjugate.
@isnad1 id=isconjro.1h3v.s4.cffe3395a89c from=translated src=- shape=2769cfea vocab=3a63e08b
-/
theorem isRealRow_self_conj {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {i : Fin n}
    (h : IsRealRow M i) : IsConjRow M i i := by
  intro j
  have him : (M i j).im = 0 := h j
  show M i j = starRingEnd ℂ (M i j)
  rw [starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr him]

/-- If row k is the conjugate of row i, then row i is the conjugate of row k.
@isnad1 id=isconjro.1h4v.s4.5a4a0d4b91f7 from=translated src=- shape=1d476208 vocab=ddce66f9
-/
theorem isConjRow_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {i k : Fin n}
    (h : IsConjRow M i k) : IsConjRow M k i := by
  intro j
  have := h j
  -- M k j = conj(M i j), so M i j = conj(M k j)
  rw [this, starRingEnd_apply, starRingEnd_apply, star_star]

/-- Bundled data for the ⋆_M product: an invertible matrix M satisfying the realness condition.-/
structure TubalData (n : ℕ) where
  /-- The invertible complex matrix M.-/
  M : Matrix (Fin n) (Fin n) ℂ
  /-- M is invertible.-/
  M_inv : Matrix (Fin n) (Fin n) ℂ
  /-- Left inverse property.-/
  hM_left_inv : M_inv * M = 1
  /-- Right inverse property.-/
  hM_right_inv : M * M_inv = 1
  /-- M satisfies the realness condition.-/
  hM_real : IsRealPaired M

namespace TubalData

variable {n : ℕ} (td : TubalData n)

/-- The inverse of M from the tubal data.-/
noncomputable def Minv : Matrix (Fin n) (Fin n) ℂ := td.M_inv

/--
@isnad1 id=eq.0h2v.s6.c50f56e16881 from=translated src=- shape=0ddac857 vocab=b9ca4d79
-/
theorem M_mul_Minv : td.M * td.Minv = 1 := td.hM_right_inv

/--
@isnad1 id=eq.0h2v.s6.eda1c31417d6 from=translated src=- shape=0ddac857 vocab=b9ca4d79
-/
theorem Minv_mul_M : td.Minv * td.M = 1 := td.hM_left_inv

/-- M is invertible (as a Mathlib Invertible instance).-/
@[reducible] noncomputable def M_invertible : Invertible td.M :=
  ⟨td.M_inv, td.hM_left_inv, td.hM_right_inv⟩

/-- Apply M to a complex vector.-/
noncomputable def applyM (v : Fin n → ℂ) : Fin n → ℂ := td.M *ᵥ v

/-- Apply M⁻¹ to a complex vector.-/
noncomputable def applyMinv (v : Fin n → ℂ) : Fin n → ℂ := td.M_inv *ᵥ v

/--
@isnad1 id=eq.0h4v.s5.f666c198dc5a from=translated src=- shape=e0baead8 vocab=d6909921
-/
@[simp]
theorem applyM_apply (v : Fin n → ℂ) (i : Fin n) :
    td.applyM v i = ∑ j, td.M i j * v j := by
  simp [applyM, Matrix.mulVec, dotProduct]

/--
@isnad1 id=eq.0h4v.s5.98650eff5a03 from=translated src=- shape=e0baead8 vocab=6f9fd505
-/
@[simp]
theorem applyMinv_apply (v : Fin n → ℂ) (i : Fin n) :
    td.applyMinv v i = ∑ j, td.M_inv i j * v j := by
  simp [applyMinv, Matrix.mulVec, dotProduct]

/--
@isnad1 id=eq.0h3v.s4.3fa90cb3bea1 from=translated src=- shape=e025fdef vocab=0a810525
-/
theorem applyMinv_applyM (v : Fin n → ℂ) : td.applyMinv (td.applyM v) = v := by
  change td.M_inv *ᵥ (td.M *ᵥ v) = v
  rw [mulVec_mulVec, td.hM_left_inv, one_mulVec]

/--
@isnad1 id=eq.0h3v.s4.439f9f153187 from=translated src=- shape=e025fdef vocab=0a810525
-/
theorem applyM_applyMinv (v : Fin n → ℂ) : td.applyM (td.applyMinv v) = v := by
  change td.M *ᵥ (td.M_inv *ᵥ v) = v
  rw [mulVec_mulVec, td.hM_right_inv, one_mulVec]

/--
@isnad1 id=injectiv.0h2v.s4.972f20da47be from=translated src=- shape=525de613 vocab=a8e3bf06
-/
theorem applyM_injective : Function.Injective td.applyM := by
  intro v w h
  have := congr_arg td.applyMinv h
  rwa [td.applyMinv_applyM, td.applyMinv_applyM] at this

/--
@isnad1 id=injectiv.0h2v.s4.dbef18a0ea24 from=translated src=- shape=525de613 vocab=0ff0e721
-/
theorem applyMinv_injective : Function.Injective td.applyMinv := by
  intro v w h
  have := congr_arg td.applyM h
  rwa [td.applyM_applyMinv, td.applyM_applyMinv] at this

/--
@isnad1 id=eq.0h4v.s6.54af6e1bddcc from=translated src=- shape=0c3f930b vocab=b194e7eb
-/
theorem applyM_add (v w : Fin n → ℂ) :
    td.applyM (v + w) = td.applyM v + td.applyM w :=
  Matrix.mulVec_add _ v w

/--
@isnad1 id=eq.0h4v.s6.27d6e8b40446 from=translated src=- shape=0c3f930b vocab=7777d323
-/
theorem applyMinv_add (v w : Fin n → ℂ) :
    td.applyMinv (v + w) = td.applyMinv v + td.applyMinv w :=
  Matrix.mulVec_add _ v w

end TubalData

end TubalTensor
