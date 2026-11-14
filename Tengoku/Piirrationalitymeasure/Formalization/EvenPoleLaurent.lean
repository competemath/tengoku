import Tengoku.Piirrationalitymeasure.Formalization.EvenPolePolynomial
import Tengoku.Piirrationalitymeasure.Formalization.LaurentIdentification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual normalized Laurent derivatives for every even integer numerator. -/

namespace PiIrrationality.EvenPole

open Polynomial

noncomputable def regularized (F : Polynomial ℤ) (m : ℕ) (t : ℝ) : ℝ :=
  aeval t (numerator F) / (5 - t) ^ m

theorem regularized_contDiffAt (F : Polynomial ℤ) (m k : ℕ) :
    ContDiffAt ℝ k (regularized F m) (-5) := by
  unfold regularized
  exact ((numerator F).contDiff_aeval k).contDiffAt.div (by fun_prop) (by norm_num)

theorem localCoeff_is_rational (F : Polynomial ℤ) (m k : ℕ) :
    ∃ q : ℚ, normalizedDeriv k (regularized F m) (-5) = (q : ℝ) := by
  let K : Subfield ℝ := (algebraMap ℚ ℝ).fieldRange
  have he : regularized F m =
      fun t : ℝ => aeval t (numerator F) * (5 - t) ^ (-(m : ℤ)) := by
    ext t
    simp only [regularized, zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hinv : ContDiffAt ℝ k (fun t : ℝ => (5 - t) ^ (-(m : ℤ))) (-5) := by
    simp only [zpow_neg, zpow_natCast]
    fun_prop (disch := norm_num)
  have hmem : normalizedDeriv k (regularized F m) (-5) ∈ K := by
    rw [he, normalizedDeriv_mul ((numerator F).contDiff_aeval k).contDiffAt hinv]
    apply K.sum_mem
    intro i hi
    apply K.mul_mem
    · have h := normalizedDeriv_rat_aeval i (numerator F) (-5)
      norm_num only [Rat.cast_neg, Rat.cast_ofNat] at h
      rw [h]
      exact RingHom.mem_fieldRange_self _ _
    · obtain ⟨q, hq⟩ := normalizedDeriv_inv_linear_is_rational m (k - i)
      rw [hq]
      exact RingHom.mem_fieldRange_self _ _
  obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp hmem
  exact ⟨q, hq.symm⟩

noncomputable def localCoeff (F : Polynomial ℤ) (m k : ℕ) : ℚ :=
  Classical.choose (localCoeff_is_rational F m k)

theorem localCoeff_cast (F : Polynomial ℤ) (m k : ℕ) :
    (localCoeff F m k : ℝ) = normalizedDeriv k (regularized F m) (-5) :=
  (Classical.choose_spec (localCoeff_is_rational F m k)).symm

noncomputable def laurentCoeff (F : Polynomial ℤ) (m : ℕ) (j : ℤ) : ℚ :=
  if j < (m : ℤ) then localCoeff F m ((m : ℤ) - 1 - j).toNat else 0

theorem laurentCoeff_cast (F : Polynomial ℤ) {m : ℕ} (_hm : 0 < m) {j : ℤ}
    (hj : j < (m : ℤ)) :
    (laurentCoeff F m j : ℝ) =
      normalizedDeriv ((m : ℤ) - 1 - j).toNat (regularized F m) (-5) := by
  rw [laurentCoeff, ite_eq_left hj, localCoeff_cast]

end PiIrrationality.EvenPole
