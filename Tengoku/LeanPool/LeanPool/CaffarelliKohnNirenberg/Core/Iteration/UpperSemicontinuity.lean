/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Iteration.UpperSemicontinuityBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Energy.AELocalEnergy
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku

/-!
# Upper semicontinuity of the time-slice energy

The product-cutoff argument below uses the almost-every-time local energy
inequality and the compactly supported smooth cutoffs from the setting layer.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-- Conditional form of `lem:alpha-usc`.

`F h` is the inner-ball time-slice essential supremum on the enlarged time
interval, `S` is the outer-ball essential supremum before the endpoint, and
`henergy` is the estimate obtained from the a.e.-time local energy inequality
and a product cutoff.  The conclusion is the paper's right-sided limsup
bound.
@isnad1 id=le.4h3v.s7.5e17fc06421b from=translated src=- shape=dd64538b vocab=a3efcf5b
-/
theorem alpha_usc_of_local_energy_inequality
    {F ω : ℝ → ℝ} {S : ℝ}
    (hF_nonneg : ∀ᶠ h in (𝓝[>] (0 : ℝ)), 0 ≤ F h)
    (hF_bounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F)
    (henergy : ∀ᶠ h in (𝓝[>] (0 : ℝ)), F h ≤ S + ω h)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Filter.limsup F (𝓝[>] (0 : ℝ)) ≤ S := by
  have hco : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F :=
    isCoboundedUnder_le_of_eventually_le _ hF_nonneg
  rw [Filter.limsup_le_iff' hco hF_bounded]
  intro y hy
  have hdiff : 0 < y - S := sub_pos.mpr hy
  have hωlt : ∀ᶠ h in (𝓝[>] (0 : ℝ)), ω h < y - S :=
    (tendsto_order.1 hω).2 (y - S) hdiff
  filter_upwards [henergy, hωlt] with h hF hωh
  nlinarith only [hF, hωh]

end CKN
