import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder

set_option maxHeartbeats 800000
set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

open Finset BigOperators

namespace AnnulusNF

variable {W : Type*} [CommRing W] (I : Ideal W)

def psum (c : ℕ → W) (π : W) (k N : ℕ) : W := ∑ m ∈ range N, c (k + m) * π ^ m

end AnnulusNF

namespace AnnulusNF

open ModularCurve ModularCurve.UVCrossingModel

variable {W : Type*} [CommRing W]

noncomputable abbrev ij (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

end AnnulusNF

namespace AnnulusG1

open ModularCurve ModularCurve.UVCrossingModel Finset

variable {W : Type*} [CommRing W]

end AnnulusG1

namespace AnnulusNF

open ModularCurve ModularCurve.UVCrossingModel Finset

variable {W : Type*} [CommRing W]

end AnnulusNF

namespace AnnulusStepA

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1

variable {W : Type*} [CommRing W]

end AnnulusStepA

set_option autoImplicit false

namespace AnnulusSlope

noncomputable def gaussOrder (e : ℕ) (α β : ℕ → ℕ∞) (t : ℕ) : ℕ∞ :=
  (⨅ i : ℕ, α i + ((i * t : ℕ) : ℕ∞)) ⊓ (⨅ j : ℕ, β j + (((j + 1) * (e - t) : ℕ) : ℕ∞))

end AnnulusSlope

namespace AnnulusStepA

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1

variable {W : Type*} [CommRing W]

end AnnulusStepA

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

namespace SlopeLawSol
open ModularCurve ModularCurve.UVCrossingModel

open AnnulusNF AnnulusStepA

variable {W : Type u} [CommRing W]

/--
@isnad1 id=eq.0h3v.s7.e7124ba40cee from=translated src=- shape=27129757 vocab=c933f4b8
-/
@[scoped simp] theorem nfCoeff_negSucc (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl
/--
@isnad1 id=eq.0h3v.s7.8e4884a50e49 from=translated src=- shape=caef8e0a vocab=17dc28c5
-/
@[scoped simp] theorem nfCoeff_natCast (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl
omit [CommRing W] in
/--
@isnad1 id=eq.0h1v.s5.317cd36f8ff1 from=translated src=- shape=f4fd4301 vocab=affde172
-/
@[scoped simp] theorem nfExponent_negSucc (j : ℕ) : nfExponent (Int.negSucc j) = Finsupp.single 1 (j + 1) := rfl
omit [CommRing W] in
/--
@isnad1 id=eq.0h1v.s5.444c3287447f from=translated src=- shape=1d30f6b6 vocab=10583364
-/
@[scoped simp] theorem nfExponent_natCast (i : ℕ) : nfExponent (i : ℤ) = Finsupp.single 0 i := rfl

/--
@isnad1 id=eq.0h4v.s9.355f16b05c21 from=translated src=- shape=15a28eac vocab=0019873e
-/
theorem coeff_inU_add_inV (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a + inV b) =
      (if d 1 = 0 then PowerSeries.coeff (d 0) a else 0) + (if d 0 = 0 then PowerSeries.coeff (d 1) b else 0) := by
  rw [map_add, coeff_inU, coeff_inV]

/--
@isnad1 id=eq.1h3v.s8.aaff859067e9 from=translated src=- shape=2db4564d vocab=2c23582e
-/
theorem coeff_nfExponent (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2) = nfCoeff ab n := by
  cases n with
  | ofNat i =>
    rw [Int.ofNat_eq_natCast, nfExponent_natCast, nfCoeff_natCast, coeff_inU_add_inV]
    simp only [Finsupp.single_apply, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, ite_true]
    by_cases hi : i = 0
    · subst hi; simp [hb]
    · simp [hi]
  | negSucc j =>
    rw [nfExponent_negSucc, nfCoeff_negSucc, coeff_inU_add_inV]
    simp [Finsupp.single_apply]

/--
@isnad1 id=eq.2h5v.s7.65f409116680 from=translated src=- shape=1daa7f33 vocab=bee27d1a
-/
theorem repGaussOrder_normalForm_eq_iInf_termOrder
    (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    have := repGaussOrder_le v E t (inU ab.1 + inV ab.2) (nfExponent n)
    rwa [coeff_nfExponent ab hb n] at this
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
    · have hd : d = nfExponent ((0 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h0, h1]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨j, hj⟩ : ∃ j, d 1 = j + 1 := Nat.exists_eq_succ_of_ne_zero h1
      have hd : d = nfExponent (Int.negSucc j) := by
        rw [nfExponent_negSucc]; ext k; fin_cases k <;> simp [h0, hj]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨i, hi⟩ : ∃ i, d 0 = i + 1 := Nat.exists_eq_succ_of_ne_zero h0
      have hd : d = nfExponent ((i + 1 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h1, hi]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · rw [coeff_inU_add_inV, ite_eq_right h1, ite_eq_right h0, add_zero, hv0, top_add]
      exact le_top

section Scaled
variable [IsDomain W] [IsDiscreteValuationRing W]

noncomputable abbrev vq (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) : W → ℕ∞ :=
  fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w

/--
@isnad1 id=eq.1h2v.s5.f64fc8733d7c from=translated src=- shape=3c251591 vocab=c34322e3
-/
theorem vq_zero (q : ℕ) (hq : 1 ≤ q) : vq W q 0 = ⊤ := by
  simp only [vq, AddValuation.map_zero]
  exact WithTop.mul_top (Nat.cast_ne_zero.mpr (by omega))

noncomputable def vqAddVal (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) (hq : 1 ≤ q) :
    AddValuation W ℕ∞ :=
  AddValuation.of (vq W q) (vq_zero q hq) (by simp [vq])
    (fun x y => by
      simp only [vq]
      rw [← mul_min]
      exact mul_le_mul_right (AddValuation.map_add _ x y) _)
    (fun x y => by simp only [vq, AddValuation.map_mul, mul_add])

end Scaled

end SlopeLawSol
open scoped _root_.P2MW.S_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder.SlopeLawSol

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

/--
@isnad1 id=eq.2h5v.s7.65f409116680 from=translated src=- shape=1daa7f33 vocab=bee27d1a
-/
theorem solution
    {W : Type u} [CommRing W] (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n :=
  SlopeLawSol.repGaussOrder_normalForm_eq_iInf_termOrder v hv0 E t ab hb
