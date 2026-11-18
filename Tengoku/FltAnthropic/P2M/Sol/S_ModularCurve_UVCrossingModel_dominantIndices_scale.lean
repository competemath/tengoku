import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_dominantIndices_scale.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_dominantIndices_scale

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u

namespace DominantScaleSol

open ModularCurve ModularCurve.UVCrossingModel

variable {W : Type u} [CommRing W]

/--
@isnad1 id=eq.1h3v.s6.7879fa29e9c3 from=translated src=- shape=fcfecaba vocab=2f0a12a8
-/
theorem enat_map_iInf_eq_of_monotone {ι : Type*} [Nonempty ι] (g : ℕ∞ → ℕ∞) (hg : Monotone g) (f : ι → ℕ∞) :
    g (⨅ i, f i) = ⨅ i, g (f i) := by
  apply le_antisymm
  · exact le_iInf fun i => hg (iInf_le f i)
  · obtain ⟨i, hi⟩ := ciInf_mem f
    rw [← hi]
    exact iInf_le (fun i => g (f i)) i

/--
@isnad1 id=eq.2h3v.s5.0cf3692a9943 from=translated src=- shape=40fd8a51 vocab=0d04a1e0
-/
theorem enat_natCast_mul_left_cancel (q : ℕ) (hq : 1 ≤ q) {a b : ℕ∞} (h : (q : ℕ∞) * a = (q : ℕ∞) * b) :
    a = b := by
  have hq0 : (q : ℕ∞) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe b =>
      exfalso
      rw [ENat.mul_top hq0, ← Nat.cast_mul] at h
      exact ENat.natCast_ne_top _ h.symm
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top hq0, ← Nat.cast_mul] at h
      exact ENat.natCast_ne_top _ h
    | coe b =>
      rw [← Nat.cast_mul, ← Nat.cast_mul] at h
      have h' : q * a = q * b := by exact_mod_cast h
      exact_mod_cast Nat.eq_of_mul_eq_mul_left (by omega) h'

/--
@isnad1 id=eq.0h4v.s5.b7c220941277 from=translated src=- shape=abd1e7ee vocab=002cc1d6
-/
theorem annulusWeight_scale (q E t : ℕ) (d : Fin 2 →₀ ℕ) :
    annulusWeight (q * E) (q * t) d = q * annulusWeight E t d := by
  simp only [annulusWeight, ← mul_tsub]; ring

/--
@isnad1 id=eq.0h6v.s6.b88cd3d33655 from=translated src=- shape=49a273de vocab=215e410d
-/
theorem repGaussOrder_scale (v : W → ℕ∞) (E t q : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder (fun w => (q : ℕ∞) * v w) (q * E) (q * t) F = (q : ℕ∞) * repGaussOrder v E t F := by
  simp only [repGaussOrder, annulusWeight_scale, Nat.cast_mul, ← mul_add]
  exact (enat_map_iInf_eq_of_monotone (fun x => (q : ℕ∞) * x) (fun a b h => mul_le_mul_right h _) _).symm

/--
@isnad1 id=eq.0h7v.s6.8a3be9faa982 from=translated src=- shape=e01083a5 vocab=97a822a0
-/
theorem termOrder_scale (v : W → ℕ∞) (E t q : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab n = (q : ℕ∞) * termOrder v E t ab n := by
  simp only [termOrder, annulusWeight_scale, Nat.cast_mul, mul_add]

/--
@isnad1 id=eq.1h6v.s6.9b97c2358bd7 from=translated src=- shape=f9830ce7 vocab=5c93494d
-/
theorem dominantIndices_scale (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab := by
  ext n
  simp only [dominantIndices, Set.mem_ofPred_eq, termOrder_scale, repGaussOrder_scale]
  exact ⟨enat_natCast_mul_left_cancel q hq, fun h => by rw [h]⟩

end DominantScaleSol

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

/--
@isnad1 id=eq.1h6v.s6.9b97c2358bd7 from=translated src=- shape=f9830ce7 vocab=5c93494d
-/
theorem solution
    {W : Type u} [CommRing W] (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab :=
  DominantScaleSol.dominantIndices_scale v E t q hq ab
