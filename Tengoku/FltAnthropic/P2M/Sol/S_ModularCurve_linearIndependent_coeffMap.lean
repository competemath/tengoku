import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Theorems.Thm_LinearIndependent_exists_det_submatrix_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_linearIndependent_coeffMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_linearIndependent_coeffMap

set_option autoImplicit false

open ModularCurve

/--
@isnad1 id=linearin.1h5v.s8.c3a8c77d6695 from=translated src=- shape=66e3a996 vocab=c71aecdb
-/
theorem solution {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    {n : ℕ} {v : Fin n → LaurentSeries k₀} (hv : LinearIndependent k₀ v) :
    LinearIndependent k (fun i => coeffMap σ (v i)) := by
  classical

  let f : Fin n → ℤ → k₀ := fun j => (v j).coeff
  have hf : LinearIndependent k₀ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ j, g j • v j = 0 := by
      apply HahnSeries.coeff_injective
      funext a
      have := congrFun hg a
      simp only [Finset.sum_apply, Pi.smul_apply, f] at this
      rw [HahnSeries.coeff_sum]
      simp only [HahnSeries.coeff_smul] at this ⊢
      exact this
    exact (Fintype.linearIndependent_iff.1 hv) g h0

  obtain ⟨s, -, hdet⟩ := LinearIndependent.exists_det_submatrix_ne_zero f hf

  have hdet' : (Matrix.of fun l j => σ (f j (s l))).det ≠ 0 := by
    have : (Matrix.of fun l j => σ (f j (s l))) = σ.mapMatrix (Matrix.of fun l j => f j (s l)) := by
      ext l j; rfl
    rw [this, ← RingHom.map_det]
    exact (map_ne_zero σ).2 hdet
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmul : (Matrix.of fun l j => σ (f j (s l))).mulVec g = 0 := by
    funext l
    have := congrArg (fun x : LaurentSeries k => x.coeff (s l)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, HahnSeries.coeff_zero] at this
    rw [Pi.zero_apply, ← this]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, f]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet' hmul
  exact fun i => congrFun this i
