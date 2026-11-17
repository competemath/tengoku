import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.MasterSeries
import Tengoku.Seed.Analysis.Normed.Group.Tannery
import Tengoku.Seed.Tactic.FunProp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology

def shellHeight (r : ℤ) (p : ℤ × ℤ × ℤ) : ℕ :=
  (-entryMinimum r p.1 p.2.1 p.2.2).toNat

/--
@isnad1 id=eq.0h3v.s6.7425818e7602 from=translated src=- shape=4e0d500a vocab=9c2b9e61
-/
theorem shellHeight_eq (r : ℤ) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellHeight r p = ((cartanIndices r p.1 p.2.1 p.2.2 c).1 / 2).toNat +
      (cartanIndices r p.1 p.2.1 p.2.2 c).2.toNat := by
  have hh := shell_height_eq r p.1 p.2.1 p.2.2 c
  have hn := shell_exponents_nonnegative r p.1 p.2.1 p.2.2 c
  unfold shellHeight
  omega

/--
@isnad1 id=eq.0h8v.s6.48f197632277 from=translated src=- shape=72381dc1 vocab=9d89c8f3
-/
theorem shellMonomial_damping (t d U V T : ℂ) (r : ℤ)
    (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellMonomial t d U V T r p c =
      T ^ shellHeight r p * shellMonomial t d U V 1 r p c := by
  have hn := shell_exponents_nonnegative r p.1 p.2.1 p.2.2 c
  have hn' := Int.toNat_of_nonneg hn.1
  have hb' := Int.toNat_of_nonneg hn.2
  rw [shellHeight_eq r p c]
  unfold shellMonomial
  dsimp
  rw [← hn', ← hb']
  simp only [zpow_natCast, Int.toNat_natCast, one_mul, mul_pow, pow_add]
  ring

/--
@isnad1 id=eq.0h8v.s6.0ebb863fa248 from=translated src=- shape=addbcc92 vocab=d094d9cc
-/
theorem masterTerm_damping (q t d U V T : ℂ) (r : ℤ) (p : LatticeIndex) :
    masterTerm q t d U V T r p =
      T ^ shellHeight r (p.1, p.2.1, p.2.2.1) * masterTerm q t d U V 1 r p := by
  unfold masterTerm
  rw [shellMonomial_damping]
  ring

/--
@isnad1 id=le.2h8v.s6.70cc00053fde from=translated src=- shape=7e423d4b vocab=b67d0ce2
-/
theorem masterTerm_norm_le_undamped (q t d U V : ℂ) (r : ℤ)
    (p : LatticeIndex) {T : ℝ} (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1) :
    ‖masterTerm q t d U V (T : ℂ) r p‖ ≤ ‖masterTerm q t d U V 1 r p‖ := by
  rw [masterTerm_damping, norm_mul, norm_pow]
  have ht : ‖(T : ℂ)‖ = T := by simp [abs_of_nonneg hT₀]
  rw [ht]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hT₀ hT₁)

/--
@isnad1 id=tendsto.0h7v.s6.c2c94353e6d3 from=translated src=- shape=6ed8cf6c vocab=1ddc8914
-/
theorem tendsto_masterTerm (q t d U V : ℂ) (r : ℤ) (p : LatticeIndex) :
    Tendsto (fun T : ℝ => masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (masterTerm q t d U V 1 r p)) := by
  have he : (fun T : ℝ => masterTerm q t d U V (T : ℂ) r p) =
      (fun T : ℝ => (T : ℂ) ^ shellHeight r (p.1, p.2.1, p.2.2.1) *
        masterTerm q t d U V 1 r p) := by
    funext T
    exact masterTerm_damping q t d U V (T : ℂ) r p
  rw [he]
  have hc : ContinuousAt (fun T : ℝ =>
      (T : ℂ) ^ shellHeight r (p.1, p.2.1, p.2.2.1) *
        masterTerm q t d U V 1 r p) 1 := by fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- Dominated convergence on the actual master family. The summability
input is deliberately visible and is discharged by the region assembly.
@isnad1 id=tendsto.1h6v.s7.21199753daa6 from=translated src=- shape=2f06d953 vocab=276f1579
-/
theorem tendsto_master_sum_of_summable (q t d U V : ℂ) (r : ℤ)
    (hs : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V 1 r p‖)) :
    Tendsto (fun T : ℝ => ∑' p : LatticeIndex, masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (∑' p : LatticeIndex, masterTerm q t d U V 1 r p)) := by
  apply tendsto_tsum_of_dominated_convergence hs (tendsto_masterTerm q t d U V r)
  filter_upwards [self_mem_nhdsWithin] with T hT
  intro p
  exact masterTerm_norm_le_undamped q t d U V r p hT.1.le hT.2.le

end FourierJacobi.Analysis
