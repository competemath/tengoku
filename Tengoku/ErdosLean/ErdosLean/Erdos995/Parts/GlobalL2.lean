import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Atoms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 995, part L6 (GlobalL2): `g = ∑ F_k` is finite a.e. and lies in `L²`

Adapted from `ErdosLean/Erdos996/Parts/Asm/PartialSumL2.lean` (`‖∑_{k<K} F_k‖₂² = ∑ λ_k ≤ 1`)
and the first half of `ErdosLean/Erdos996/Parts/Asm/GlobalL2.lean` (up to `memLp_gFun`) with `A`
deleted.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

private lemma measurable_atom' (k q : ℕ) : Measurable (atom k q) :=
  (Erdos996.Asm.measurable_spike _).comp (continuous_nsmul _).measurable

/--
@isnad1 id=measurab.0h1v.s5.67f22aaea6f6 from=translated src=- shape=f6104e8a vocab=51916328
-/
lemma measurable_blk (k : ℕ) : Measurable (blk k) := by
  have e : blk k = fun x => Real.sqrt (lam k / blockLen k) *
      ∑ q ∈ Finset.Icc 1 (blockLen k), atom k q x := funext (blk_eq_sum_atom k)
  rw [e]
  exact (Finset.measurable_sum _ fun q _ => measurable_atom' k q).const_mul _

/--
@isnad1 id=integrab.0h1v.s5.cc76c39e79a8 from=translated src=- shape=cced9a14 vocab=bab47de3
-/
lemma integrable_blk (k : ℕ) : Integrable (blk k) μ𝕋 := by
  refine Integrable.of_bound (measurable_blk k).aestronglyMeasurable
    (Real.sqrt (lam k / blockLen k) * ∑ q ∈ Finset.Icc 1 (blockLen k), (2 : ℝ) ^ depth k)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, blk_eq_sum_atom, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun q _ => Erdos996.Asm.abs_spike_le _ _)

private lemma fourierCoeff_blk_zero (k : ℕ) : fourierCoeff (fun x => (blk k x : ℂ)) 0 = 0 := by
  rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero k q), mul_zero]

private lemma integral_blk (k : ℕ) : ∫ x, blk k x ∂μ𝕋 = 0 := by
  have h := fourierCoeff_blk_zero k
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/--
@isnad1 id=measurab.0h0v.s4.2a1ad41dcbd3 from=translated src=- shape=ec6472ca vocab=3c72ca19
-/
lemma measurable_gPos : Measurable gPos := by
  unfold gPos
  exact Measurable.ennreal_tsum fun k => ((measurable_blk k).add_const _).ennreal_ofReal

private lemma lintegral_gPos :
    ∫⁻ x, gPos x ∂μ𝕋 = ∑' k, ENNReal.ofReal (floorC k) := by
  unfold gPos
  rw [lintegral_tsum fun k => ((measurable_blk k).add_const _).ennreal_ofReal.aemeasurable]
  congr 1
  ext k
  have hi : Integrable (fun x => blk k x + floorC k) μ𝕋 :=
    (integrable_blk k).add (integrable_const _)
  have hnn : (0 : 𝕋 → ℝ) ≤ᵐ[μ𝕋] fun x => blk k x + floorC k :=
    ae_of_all _ fun x => by
      have := blk_floor k x
      simp only [Pi.zero_apply]
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_add (integrable_blk k) (integrable_const _), integral_blk, integral_const]
  simp

/--
@isnad1 id=ne.0h0v.s5.5b6a10018a08 from=translated src=- shape=ff366b27 vocab=95fd3915
-/
lemma lintegral_gPos_ne_top : ∫⁻ x, gPos x ∂μ𝕋 ≠ ∞ := by
  rw [lintegral_gPos, ← ENNReal.ofReal_tsum_of_nonneg floorC_nonneg summable_floorC]
  exact ENNReal.ofReal_ne_top

/--
@isnad1 id=eventual.0h0v.s6.07cf9d43b528 from=translated src=- shape=65467b23 vocab=a9c9bf03
-/
lemma ae_gPos_ne_top : ∀ᵐ x ∂μ𝕋, gPos x ≠ ∞ :=
  (ae_lt_top' measurable_gPos.aemeasurable lintegral_gPos_ne_top).mono fun _ hx => hx.ne

/--
@isnad1 id=and.1h1v.s6.d9092aeafc93 from=translated src=- shape=e127a83b vocab=5d83d04e
-/
lemma gPos_toReal_eq (x : 𝕋) (hx : gPos x ≠ ∞) :
    Summable (fun k => blk k x + floorC k) ∧ (gPos x).toReal = ∑' k, (blk k x + floorC k) := by
  have hnn : ∀ k, 0 ≤ blk k x + floorC k := fun k => by linarith [blk_floor k x]
  have e : ∀ k, (ENNReal.ofReal (blk k x + floorC k)).toReal = blk k x + floorC k :=
    fun k => ENNReal.toReal_ofReal (hnn k)
  constructor
  · have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (blk k x + floorC k)) hx
    simp only [e] at this
    exact this
  · unfold gPos
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    simp only [e]

private lemma hasSum_blk (x : 𝕋) (hx : gPos x ≠ ∞) :
    HasSum (fun k => blk k x) (gFun x) := by
  obtain ⟨hs, htr⟩ := gPos_toReal_eq x hx
  have h := hs.hasSum.sub summable_floorC.hasSum
  simp only [add_sub_cancel_right] at h
  unfold gFun
  rw [htr]
  exact h

/--
@isnad1 id=tendsto.1h1v.s5.d92692abfccf from=translated src=- shape=9a5f060a vocab=cac9da93
-/
lemma tendsto_partialSum_gFun (x : 𝕋) (hx : gPos x ≠ ∞) :
    Tendsto (fun K => ∑ k ∈ range K, blk k x) atTop (𝓝 (gFun x)) :=
  (hasSum_blk x hx).tendsto_sum_nat

/-! ### Partial sums in `L²` -/

private lemma memLp_atomC (k q : ℕ) : MemLp (fun x => (atom k q x : ℂ)) 2 μ𝕋 :=
  MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_atom' k q)).aestronglyMeasurable)
    (2 ^ depth k)
    (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Erdos996.Asm.abs_spike_le _ _)

private noncomputable def aLp (k q : ℕ) : Lp ℂ 2 μ𝕋 := (memLp_atomC k q).toLp _

end Con
end Erdos995
