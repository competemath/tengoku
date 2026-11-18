import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_dominantIndices_finite_nonempty.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_dominantIndices_finite_nonempty

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

@[scoped simp] theorem nfCoeff_negSucc (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl
@[scoped simp] theorem nfCoeff_natCast (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_negSucc (j : ℕ) : nfExponent (Int.negSucc j) = Finsupp.single 1 (j + 1) := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_natCast (i : ℕ) : nfExponent (i : ℤ) = Finsupp.single 0 i := rfl

theorem coeff_inU_add_inV (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a + inV b) =
      (if d 1 = 0 then PowerSeries.coeff (d 0) a else 0) + (if d 0 = 0 then PowerSeries.coeff (d 1) b else 0) := by
  rw [map_add, coeff_inU, coeff_inV]

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

theorem termOrder_natCast (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    termOrder v E t ab (i : ℤ) = v (PowerSeries.coeff i ab.1) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem termOrder_negSucc (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    termOrder v E t ab (Int.negSucc j) = v (PowerSeries.coeff (j + 1) ab.2) + (((j + 1) * (E - t) : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

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

theorem mem_dominantIndices_iff (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ termOrder v E t ab n = ⨅ m : ℤ, termOrder v E t ab m := by
  rw [dominantIndices, Set.mem_ofPred_eq, repGaussOrder_normalForm_eq_iInf_termOrder v hv0 E t ab hb]

theorem dominantIndices_nonempty (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : (dominantIndices v E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ciInf_mem (fun n : ℤ => termOrder v E t ab n)
  exact ⟨n, (mem_dominantIndices_iff v hv0 E t ab hb n).mpr hn⟩

theorem dominantIndices_bddBelow (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (hte : t < E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddBelow (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨-(g : ℤ) - 1, fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = Int.negSucc j := Int.eq_negSucc_of_lt_zero (by omega)
  have hj : g + 1 ≤ j + 1 := by
    have : (Int.negSucc j : ℤ) = -(j : ℤ) - 1 := by rw [Int.negSucc_eq]; ring
    omega
  have h1 : (((j + 1) * (E - t) : ℕ) : ℕ∞) ≤ termOrder v E t ab (Int.negSucc j) := by
    rw [termOrder_negSucc]; exact le_add_self
  rw [hn, ← hg] at h1
  have : (j + 1) * (E - t) ≤ g := by exact_mod_cast h1
  have het : 1 ≤ E - t := by omega
  nlinarith

theorem dominantIndices_bddAbove (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht0 : 0 < t)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddAbove (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨(g : ℤ), fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = (i : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hi : g + 1 ≤ i := by omega
  have h1 : ((i * t : ℕ) : ℕ∞) ≤ termOrder v E t ab i := by rw [termOrder_natCast]; exact le_add_self
  rw [hn, ← hg] at h1
  have : i * t ≤ g := by exact_mod_cast h1
  nlinarith

theorem iInf_termOrder_lt_top (v : W → ℕ∞) (hv : ∀ c, v c = ⊤ → c = 0) (π : W) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) : (⨅ n : ℤ, termOrder v E t ab n) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hx
  have hall : ∀ n, termOrder v E t ab n = ⊤ := fun n => top_le_iff.mp (htop ▸ iInf_le _ n)
  have hcoef : ∀ n, nfCoeff ab n = 0 := fun n => by
    apply hv
    have := hall n
    rw [termOrder] at this
    exact (WithTop.add_eq_top.mp this).resolve_right (ENat.natCast_ne_top _)
  have ha : ab.1 = 0 := by
    ext i; simpa using hcoef (i : ℤ)
  have hb' : ab.2 = 0 := by
    ext j
    cases j with
    | zero => simpa using hb
    | succ j => simpa using hcoef (Int.negSucc j)
  have h0 : inU ab.1 + inV ab.2 = 0 := by
    ext d; rw [coeff_inU_add_inV, ha, hb']; simp
  rw [h0, map_zero]

section Scaled
variable [IsDomain W] [IsDiscreteValuationRing W]

noncomputable abbrev vq (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) : W → ℕ∞ :=
  fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w

theorem vq_zero (q : ℕ) (hq : 1 ≤ q) : vq W q 0 = ⊤ := by
  simp only [vq, AddValuation.map_zero]
  exact WithTop.mul_top (Nat.cast_ne_zero.mpr (by omega))

theorem vq_eq_top (q : ℕ) (c : W) (h : vq W q c = ⊤) : c = 0 := by
  simp only [vq] at h
  rcases WithTop.mul_eq_top_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact IsDiscreteValuationRing.addVal_eq_top_iff.mp h2
  · exact absurd h1 (ENat.natCast_ne_top q)

noncomputable def vqAddVal (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) (hq : 1 ≤ q) :
    AddValuation W ℕ∞ :=
  AddValuation.of (vq W q) (vq_zero q hq) (by simp [vq])
    (fun x y => by
      simp only [vq]
      rw [← mul_min]
      exact mul_le_mul_right (AddValuation.map_add _ x y) _)
    (fun x y => by simp only [vq, AddValuation.map_mul, mul_add])

theorem dominantIndices_finite_nonempty [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e) :
    (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Finite ∧
      (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Nonempty := by
  change (dominantIndices (vq W q) (q * e) p ab).Finite ∧ (dominantIndices (vq W q) (q * e) p ab).Nonempty
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have hfin := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) p ab hb hx'
  obtain ⟨lb, hlb⟩ := dominantIndices_bddBelow (vq W q) (vq_zero q hq) (q * e) p (by omega) ab hb hfin
  obtain ⟨ub, hub⟩ := dominantIndices_bddAbove (vq W q) (vq_zero q hq) (q * e) p (by omega) ab hb hfin
  exact ⟨(Set.finite_Icc lb ub).subset fun n hn => ⟨hlb hn, hub hn⟩,
    dominantIndices_nonempty _ (vq_zero q hq) _ p ab hb⟩

end Scaled

end SlopeLawSol
open scoped _root_.P2MW.S_ModularCurve_UVCrossingModel_dominantIndices_finite_nonempty.SlopeLawSol

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e) :
    (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Finite ∧ (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Nonempty :=
  SlopeLawSol.dominantIndices_finite_nonempty ϖ hϖ e he q hq x hx ab hb habx p hp1 hpe
