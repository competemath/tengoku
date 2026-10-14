/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionCommonLaw
public import Tengoku.LeanPool.LeanPool.Feige.InsertionK
public import Tengoku.LeanPool.LeanPool.Feige.Lemma43Insertion
import Tengoku.LeanPool.LeanPool.Feige.InsertionEdgeRealization
import Tengoku.LeanPool.LeanPool.Feige.Lemma43ArbitraryBase
import Tengoku.LeanPool.LeanPool.Feige.NNRealExponentialLaw

/-!
# The terminal law in the insertion argument

The common variable on the terminal edge is the sum of the negative old
coordinates, with the distinguished positive exponential removed.
-/

@[expose] public section

open MeasureTheory Set

namespace Feige

noncomputable section

/-- The all-negative signed exponential sum at the terminal chain state. -/
def terminalCommonSignedSum {n : ℕ} (β : Fin (n + 1) → ℝ)
    (e : Fin n → NNReal) : ℝ :=
  -∑ i, β i.castSucc * (e i : ℝ)

/-- The law of the terminal all-negative signed exponential sum. -/
noncomputable def terminalCommonLaw {n : ℕ}
    (β : Fin (n + 1) → ℝ) : Measure ℝ :=
  Measure.map (terminalCommonSignedSum β)
    (Measure.pi fun _ : Fin n ↦ nnexpMeasure)

/--
@isnad1 id=measurab.0h2v.s5.21dd1fcfd88e from=translated src=- shape=8b4fd764 vocab=cb75d736
-/
theorem measurable_terminalCommonSignedSum {n : ℕ}
    (β : Fin (n + 1) → ℝ) :
    Measurable (terminalCommonSignedSum β) := by
  unfold terminalCommonSignedSum
  fun_prop

/--
@isnad1 id=eq.1h2v.s6.bfaf4f781e4f from=translated src=- shape=cf901ac0 vocab=69e3a638
-/
theorem terminalCommonLaw_Ioi_zero {n : ℕ}
    (β : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i) :
    terminalCommonLaw β (Ioi 0) = 0 := by
  rw [terminalCommonLaw,
    Measure.map_apply (measurable_terminalCommonSignedSum β) measurableSet_Ioi]
  have hpre :
      terminalCommonSignedSum β ⁻¹' Ioi 0 = (∅ : Set (Fin n → NNReal)) := by
    ext e
    simp only [mem_preimage, mem_Ioi, Set.mem_empty_iff_false]
    constructor
    · intro he
      exact (not_lt_of_ge (show terminalCommonSignedSum β e ≤ 0 by
        unfold terminalCommonSignedSum
        exact neg_nonpos.mpr <| Finset.sum_nonneg fun i _ ↦
          mul_nonneg (hβ i.castSucc).le (NNReal.coe_nonneg _))) he
    · intro he
      exact he.elim
  rw [hpre]
  exact measure_empty

end

end Feige
