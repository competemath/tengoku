/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.NumberTheory.Padics.RingHoms
import Tengoku.Seed.Topology.Algebra.Group.Basic
import Tengoku.Seed.Topology.MetricSpace.Ultra.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuity of reduction of p-adic integers

Reduction modulo `p^n` has open kernel and is continuous for the discrete
topology on the quotient. This source has no local-field dependencies.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

/-- The kernel of reduction `Z_p -> ZMod (p^n)` is open.
@isnad1 id=isopen.0h2v.s8.9993b34b7ebb from=translated src=- shape=dc12bd83 vocab=0dc84be9
-/
theorem isOpen_ker_padicIntToZModPow
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsOpen
      ((RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) :
        Ideal ℤ_[p]) : Set ℤ_[p]) := by
  rw [PadicInt.ker_toZModPow]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr : (p : ℝ) ^ (-n : ℤ) ≠ 0 := zpow_ne_zero (-n : ℤ) hp0
  have hball :
      IsOpen (Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ))) :=
    IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p]) hr
  have heq :
      ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ)) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  rw [heq]
  exact hball

/-- Reduction of p-adic integers modulo `p^n` is continuous for the
discrete topology on the target.
@isnad1 id=continuo.0h2v.s9.b1e02d7bdf02 from=translated src=- shape=c72c9bde vocab=ff6437d6
-/
theorem Internal.continuous_padicIntToZModPow
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    @Continuous ℤ_[p] (ZMod (p ^ n))
      (inferInstance : TopologicalSpace ℤ_[p]) ⊥
      (PadicInt.toZModPow n : ℤ_[p] → ZMod (p ^ n)) := by
  let : TopologicalSpace (ZMod (p ^ n)) := ⊥
  let : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
  apply continuous_of_continuousAt_zero
    (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n))
  rw [ContinuousAt, nhds_discrete (ZMod (p ^ n)), map_zero, Filter.tendsto_pure]
  exact (isOpen_ker_padicIntToZModPow p n).mem_nhds
    (RingHom.ker (PadicInt.toZModPow n)).zero_mem

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
