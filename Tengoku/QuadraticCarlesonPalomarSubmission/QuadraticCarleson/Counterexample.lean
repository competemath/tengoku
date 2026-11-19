/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.WavePacket

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The counterexample family for the negative endpoint theorem

This file formalizes the packet scales, intervals, and finite superposition
`χ_N` introduced at the start of the proof of Theorem 1.
-/

open Finset MeasureTheory Set

namespace QuadraticCarleson

/-- The length `2^(-N j)` of the packet centered at the integer `j`.-/
noncomputable def packetScale (N j : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((N * j : ℕ) : ℤ))

/--
@isnad1 id=lt.0h2v.s4.92c2b7b6e87f from=translated src=- shape=5ffe46ab vocab=44707c87
-/
theorem packetScale_pos (N j : ℕ) : 0 < packetScale N j := by
  exact zpow_pos (by norm_num) _

/--
@isnad1 id=le.0h2v.s4.fda77e49928d from=translated src=- shape=628a94f6 vocab=e0a62a85
-/
theorem packetScale_le_one (N j : ℕ) : packetScale N j ≤ 1 := by
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  omega

/--
@isnad1 id=lt.2h2v.s5.a74bee3db8b9 from=translated src=- shape=c96fe337 vocab=44707c87
-/
theorem packetScale_lt_one {N j : ℕ} (hN : 0 < N) (hj : 0 < j) :
    packetScale N j < 1 := by
  apply zpow_lt_one_of_neg₀ (by norm_num)
  have hNj : 0 < N * j := Nat.mul_pos hN hj
  rw [neg_lt_zero]
  exact_mod_cast hNj

/-- The interval `j + 2^(-N j) [-1/2,1/2]` in the family `ℐ_N`.-/
noncomputable def packetInterval (N j : ℕ) : Set ℝ :=
  Icc ((j : ℝ) - packetScale N j / 2) ((j : ℝ) + packetScale N j / 2)

/--
@isnad1 id=le.0h2v.s4.d184d9aaa8e8 from=translated src=- shape=44533b80 vocab=9980ad61
-/
theorem wavePacket_support_subset_packetInterval (N j : ℕ) :
    Function.support (wavePacket (j : ℝ) (packetScale N j)) ⊆ packetInterval N j := by
  intro x hx
  have hx' := wavePacket_support (packetScale_pos N j) hx
  rw [packetInterval]
  constructor <;> linarith [hx'.1, hx'.2, packetScale_pos N j]

/--
@isnad1 id=lt.5h5v.s5.5d3171c7973b from=translated src=- shape=c7affeb2 vocab=f9f46c52
-/
theorem packetInterval_separated {N j k : ℕ} (hN : 0 < N) (hj : 0 < j) (hjk : j < k) :
    ∀ x ∈ packetInterval N j, ∀ y ∈ packetInterval N k, x < y := by
  intro x hx y hy
  have hk : 0 < k := by omega
  have hjScale := packetScale_lt_one hN hj
  have hkScale := packetScale_lt_one hN hk
  have hjkReal : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  rw [packetInterval] at hx hy
  linarith [hx.2, hy.1]

/--
@isnad1 id=disjoint.4h3v.s6.bf804918e123 from=translated src=- shape=793489da vocab=72549529
-/
theorem wavePacket_support_disjoint {N j k : ℕ}
    (hN : 0 < N) (hj : 0 < j) (hk : 0 < k) (hjk : j ≠ k) :
    Disjoint (Function.support (wavePacket (j : ℝ) (packetScale N j)))
      (Function.support (wavePacket (k : ℝ) (packetScale N k))) := by
  rw [Set.disjoint_left]
  intro x hxj hxk
  rcases lt_or_gt_of_ne hjk with hjk' | hkj'
  · exact (lt_irrefl x <| packetInterval_separated hN hj hjk' x
      (wavePacket_support_subset_packetInterval N j hxj) x
      (wavePacket_support_subset_packetInterval N k hxk))
  · exact (lt_irrefl x <| packetInterval_separated hN hk hkj' x
      (wavePacket_support_subset_packetInterval N k hxk) x
      (wavePacket_support_subset_packetInterval N j hxj))

/--
@isnad1 id=eq.5h4v.s6.68a135159583 from=translated src=- shape=900975f5 vocab=5b33689c
-/
theorem wavePacket_eq_zero_of_ne {N j k : ℕ} {x : ℝ}
    (hN : 0 < N) (hj : 0 < j) (hk : 0 < k) (hjk : j ≠ k)
    (hxj : wavePacket (j : ℝ) (packetScale N j) x ≠ 0) :
    wavePacket (k : ℝ) (packetScale N k) x = 0 := by
  by_contra hxk
  exact Set.disjoint_left.mp (wavePacket_support_disjoint hN hj hk hjk) hxj hxk

/-- The unnormalized sum of the packets used to form `χ_N`.-/
noncomputable def packetSum (N : ℕ) : ℝ → ℝ :=
  ∑ j ∈ Icc 1 N, wavePacket (j : ℝ) (packetScale N j)

/--
@isnad1 id=eq.4h3v.s6.6edb74838b5a from=translated src=- shape=13d10123 vocab=1140980b
-/
theorem packetSum_eq_wavePacket {N j : ℕ} {x : ℝ}
    (hN : 0 < N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hxj : wavePacket (j : ℝ) (packetScale N j) x ≠ 0) :
    packetSum N x = wavePacket (j : ℝ) (packetScale N j) x := by
  rw [packetSum, Finset.sum_apply]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    exact wavePacket_eq_zero_of_ne hN (by omega) (Finset.mem_Icc.mp hk).1 hkj.symm hxj
  · intro hjNotMem
    exact False.elim (hjNotMem (Finset.mem_Icc.mpr ⟨hj, hjN⟩))

/--
@isnad1 id=eq.1h2v.s5.62964e33bc4f from=translated src=- shape=d398b756 vocab=cf127f4d
-/
theorem packetSum_eq_zero {N : ℕ} {x : ℝ}
    (hx : ∀ j ∈ Finset.Icc 1 N, wavePacket (j : ℝ) (packetScale N j) x = 0) :
    packetSum N x = 0 := by
  rw [packetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero hx

/--
@isnad1 id=or.1h2v.s6.a16070cddf4f from=translated src=- shape=44519af0 vocab=356420f4
-/
theorem packetSum_eq_zero_or_eq_wavePacket {N : ℕ} (hN : 0 < N) (x : ℝ) :
    packetSum N x = 0 ∨
      ∃ j ∈ Finset.Icc 1 N,
        packetSum N x = wavePacket (j : ℝ) (packetScale N j) x := by
  by_cases hpacket : ∃ j ∈ Finset.Icc 1 N,
      wavePacket (j : ℝ) (packetScale N j) x ≠ 0
  · rcases hpacket with ⟨j, hj, hxj⟩
    right
    exact ⟨j, hj, packetSum_eq_wavePacket hN (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2 hxj⟩
  · left
    apply packetSum_eq_zero
    intro j hj
    by_contra hxj
    exact hpacket ⟨j, hj, hxj⟩

/-- The real-valued finite superposition `χ_N`.-/
noncomputable def counterexampleReal (N : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * packetSum N x

/-- The same counterexample regarded as a complex-valued function, as required
by the quadratic Hilbert transform.-/
noncomputable def counterexample (N : ℕ) (x : ℝ) : ℂ :=
  counterexampleReal N x

/--
@isnad1 id=le.0h2v.s4.1c5dfc24778a from=translated src=- shape=787c1379 vocab=641ee951
-/
theorem counterexampleReal_nonneg (N : ℕ) (x : ℝ) : 0 ≤ counterexampleReal N x := by
  rw [counterexampleReal, packetSum, Finset.sum_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) <|
    sum_nonneg fun j _ => wavePacket_nonneg (j : ℝ) x (packetScale_pos N j)

/--
@isnad1 id=continuo.0h1v.s4.012b78675faf from=translated src=- shape=8735051e vocab=2ba34329
-/
theorem continuous_packetSum (N : ℕ) : Continuous (packetSum N) := by
  rw [packetSum, Finset.sum_fn]
  exact continuous_finsetSum (Icc 1 N) fun j _ =>
    continuous_wavePacket (j : ℝ) (packetScale N j)

/--
@isnad1 id=continuo.0h1v.s4.aeca64b29b7f from=translated src=- shape=8735051e vocab=f289ee4c
-/
theorem continuous_counterexampleReal (N : ℕ) : Continuous (counterexampleReal N) := by
  exact continuous_const.mul (continuous_packetSum N)

/--
@isnad1 id=hascompa.0h1v.s3.5b0666ab4b13 from=translated src=- shape=8735051e vocab=b2ee2c87
-/
theorem packetSum_hasCompactSupport (N : ℕ) : HasCompactSupport (packetSum N) := by
  rw [packetSum]
  apply HasCompactSupport.finset_sum
  intro j _
  exact wavePacket_hasCompactSupport (j : ℝ) (packetScale_pos N j)

/--
@isnad1 id=hascompa.0h1v.s3.c5c5225a74b4 from=translated src=- shape=8735051e vocab=871b7836
-/
theorem counterexampleReal_hasCompactSupport (N : ℕ) :
    HasCompactSupport (counterexampleReal N) := by
  change HasCompactSupport ((fun _ : ℝ => (N : ℝ)⁻¹) * packetSum N)
  exact (packetSum_hasCompactSupport N).mul_left

/--
@isnad1 id=integrab.0h1v.s4.53a1a20cb8af from=translated src=- shape=b684bfc9 vocab=3b100a99
-/
theorem counterexampleReal_integrable (N : ℕ) : Integrable (counterexampleReal N) :=
  (continuous_counterexampleReal N).integrable_of_hasCompactSupport
    (counterexampleReal_hasCompactSupport N)

/--
@isnad1 id=eq.1h1v.s5.ff6a11afe1b6 from=translated src=- shape=c698b70c vocab=a16daecb
-/
theorem counterexampleReal_integral {N : ℕ} (hN : 0 < N) :
    ∫ x : ℝ, counterexampleReal N x = 1 := by
  have hpacket : ∀ j : ℕ,
      ∫ x : ℝ, wavePacket (j : ℝ) (packetScale N j) x = 1 := fun j =>
    wavePacket_integral (j : ℝ) (packetScale_pos N j)
  change ∫ x : ℝ, (N : ℝ)⁻¹ * packetSum N x = 1
  rw [integral_const_mul, packetSum, Finset.sum_fn]
  rw [integral_finsetSum (Icc 1 N) (fun j _ =>
    wavePacket_integrable (j : ℝ) (packetScale_pos N j))]
  simp_rw [hpacket]
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

/--
@isnad1 id=continuo.0h1v.s4.a3ad06339a4a from=translated src=- shape=7000f90d vocab=72f88125
-/
theorem continuous_counterexample (N : ℕ) : Continuous (counterexample N) := by
  exact Complex.continuous_ofReal.comp (continuous_counterexampleReal N)

/--
@isnad1 id=measurab.0h1v.s3.83b5e106b362 from=translated src=- shape=7000f90d vocab=5baa8c55
-/
theorem measurable_counterexample (N : ℕ) : Measurable (counterexample N) :=
  (continuous_counterexample N).measurable

/--
@isnad1 id=hascompa.0h1v.s3.2fbc4988c07e from=translated src=- shape=7000f90d vocab=46ec6b90
-/
theorem counterexample_hasCompactSupport (N : ℕ) : HasCompactSupport (counterexample N) := by
  change HasCompactSupport (Complex.ofReal ∘ counterexampleReal N)
  exact (counterexampleReal_hasCompactSupport N).comp_left Complex.ofReal_zero

/--
@isnad1 id=ex.0h1v.s4.1ff8b83efe41 from=translated src=- shape=267e3eac vocab=901ac9ea
-/
theorem counterexample_bounded (N : ℕ) : ∃ C : ℝ, ∀ x, ‖counterexample N x‖ ≤ C :=
  (continuous_counterexample N).bounded_above_of_compact_support
    (counterexample_hasCompactSupport N)

/-- The counterexample `χ_N`, packaged as a bounded, compactly supported,
measurable function in the domain used by the paper.-/
noncomputable def counterexampleL0Infinity (N : ℕ) : L0Infinity where
  toFun := counterexample N
  measurable_toFun := measurable_counterexample N
  bounded_toFun := counterexample_bounded N
  hasCompactSupport_toFun := counterexample_hasCompactSupport N

end QuadraticCarleson
