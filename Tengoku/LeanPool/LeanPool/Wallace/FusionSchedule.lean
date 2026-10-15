/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import Tengoku.LeanPool.LeanPool.Wallace.FiniteCombinatorics
public import Tengoku.LeanPool.LeanPool.Wallace.UniformKronecker
public import Tengoku

/-!
# A concrete schedule for the Wallace fusion

This file fixes, once and for all, the numerical parameters used by the character-fusion
construction.  At stage `l`, `accumulatedSize l` is the total size allotted to all earlier
blocks, `protectedBound l` bounds the finite set whose character values must be protected, and
`blockSize l` is the size of the new block.  The identity

`blockSize l = (l + 2) * protectedBound l`

makes the discarded proportion tend to zero.  The errors form a geometric series of total mass
`1 / 32`, leaving a large margin around an initial character value of `1 / 2`.
-/

@[expose] public section

open Filter Topology

namespace Wallace
namespace FusionSchedule

noncomputable section

open FiniteCombinatorics

/-- Total number of positions allotted to blocks strictly before stage `l`. -/
def accumulatedSize : ℕ → ℕ
  | 0 => 0
  | l + 1 =>
      accumulatedSize l + (l + 2) * (accumulatedSize l + 2 * l + 2)

/-- Cardinality bound for the protected set at stage `l`. -/
def protectedBound (l : ℕ) : ℕ :=
  accumulatedSize l + 2 * l + 2

/-- Size of the fresh finite block at stage `l`. -/
def blockSize (l : ℕ) : ℕ :=
  (l + 2) * protectedBound l

/--
@isnad1 id=eq.0h1v.s4.10ad5b9c22da from=translated src=- shape=a3b61a71 vocab=8c011f77
-/
@[simp]
theorem accumulatedSize_succ (l : ℕ) :
    accumulatedSize (l + 1) = accumulatedSize l + blockSize l := by
  rfl

/--
@isnad1 id=lt.0h1v.s3.d6f94d076d64 from=translated src=- shape=8a62b088 vocab=0fdc543f
-/
theorem protectedBound_pos (l : ℕ) : 0 < protectedBound l := by
  simp only [protectedBound]
  omega

/--
@isnad1 id=le.0h1v.s4.9b7b987086c3 from=translated src=- shape=8ebb3917 vocab=bad3bdda
-/
theorem accumulatedSize_add_le_protectedBound (l : ℕ) :
    accumulatedSize l + l + 2 ≤ protectedBound l := by
  simp only [protectedBound]
  omega

/--
@isnad1 id=ne.0h1v.s3.191fba4fdf0d from=translated src=- shape=b14ee516 vocab=6b591d4a
-/
theorem protectedBound_ne_zero (l : ℕ) : protectedBound l ≠ 0 :=
  Nat.ne_of_gt (protectedBound_pos l)

/--
@isnad1 id=lt.0h1v.s3.7cc7c8669a10 from=translated src=- shape=8a62b088 vocab=966e2c5b
-/
theorem blockSize_pos (l : ℕ) : 0 < blockSize l := by
  simp only [blockSize]
  exact Nat.mul_pos (by omega) (protectedBound_pos l)

/-- The exact discarded-proportion identity behind the density-one argument.
@isnad1 id=eq.0h1v.s5.eb4cec92cf97 from=translated src=- shape=645b1280 vocab=a42f4a1c
-/
theorem protectedBound_div_blockSize (l : ℕ) :
    (protectedBound l : ℝ) / (blockSize l : ℝ) =
      1 / ((l : ℝ) + 2) := by
  rw [blockSize, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [protectedBound_ne_zero l]

/-- The proportion of a block which bounded deletion may discard tends to zero.
@isnad1 id=tendsto.0h0v.s5.bfa3652a9564 from=translated src=- shape=3386506e vocab=83e396c1
-/
theorem tendsto_protectedBound_div_blockSize :
    Tendsto (fun l : ℕ ↦ (protectedBound l : ℝ) / (blockSize l : ℝ))
      atTop (nhds 0) := by
  have hshift := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hmain : Tendsto (fun l : ℕ ↦ 1 / ((l : ℝ) + 2)) atTop (nhds 0) := by
    convert hshift using 1
    ext l
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  exact hmain.congr' (Eventually.of_forall fun l ↦ (protectedBound_div_blockSize l).symm)

/-- Stage error.  In elementary notation this is `2^(-(l+6))`. -/
def stageError (l : ℕ) : ℝ :=
  (1 / 32 : ℝ) / 2 / 2 ^ l

/--
@isnad1 id=lt.0h1v.s3.817d98008901 from=translated src=- shape=b9369acb vocab=1ef69b5a
-/
theorem stageError_pos (l : ℕ) : 0 < stageError l := by
  simp only [stageError]
  positivity

/-- Exact geometric-tail identity, convenient for the completeness estimate.
@isnad1 id=eq.0h2v.s5.c3f99de83d2d from=translated src=- shape=07968900 vocab=8bf400c4
-/
theorem stageError_add (L n : ℕ) :
    stageError (L + n) = stageError L / 2 ^ n := by
  simp only [stageError, pow_add]
  ring

/-- The tail beginning at stage `L` has total mass exactly `2 * stageError L`.
@isnad1 id=hassum.0h1v.s5.81d5264a4173 from=translated src=- shape=3727a3b9 vocab=67ff554a
-/
theorem hasSum_stageError_add (L : ℕ) :
    HasSum (fun n : ℕ ↦ stageError (L + n)) (2 * stageError L) := by
  convert hasSum_geometric_two' (2 * stageError L) using 1
  ext n
  rw [stageError_add]
  ring

/--
@isnad1 id=summable.0h1v.s4.7d7926989771 from=translated src=- shape=7119c14c vocab=c11c5143
-/
theorem summable_stageError_add (L : ℕ) :
    Summable (fun n : ℕ ↦ stageError (L + n)) :=
  (hasSum_stageError_add L).summable

/--
@isnad1 id=eq.0h1v.s5.d388dad1d170 from=translated src=- shape=14f1cffc vocab=eb2c6757
-/
theorem tsum_stageError_add (L : ℕ) :
    ∑' n : ℕ, stageError (L + n) = 2 * stageError L :=
  (hasSum_stageError_add L).tsum_eq

/--
@isnad1 id=summable.0h0v.s3.791820182309 from=translated src=- shape=ef4b497d vocab=2caf10aa
-/
theorem summable_stageError : Summable stageError := by
  change Summable (fun n : ℕ ↦ (1 / 32 : ℝ) / 2 / 2 ^ n)
  exact summable_geometric_two' (1 / 32 : ℝ)

/--
@isnad1 id=tendsto.0h0v.s4.6f2f79cc74c5 from=translated src=- shape=8e2810f0 vocab=af3e7cee
-/
theorem tendsto_stageError : Tendsto stageError atTop (nhds 0) :=
  summable_stageError.tendsto_atTop_zero

/-- The total perturbation budget of the entire fusion is `1/32`.
@isnad1 id=eq.0h0v.s5.57497ab48393 from=translated src=- shape=5cc1707c vocab=56c77a16
-/
theorem tsum_stageError : ∑' l : ℕ, stageError l = (1 / 32 : ℝ) := by
  change (∑' n : ℕ, (1 / 32 : ℝ) / 2 / 2 ^ n) = 1 / 32
  exact tsum_geometric_two' (1 / 32 : ℝ)

/-- Independence threshold used before the bounded-deletion step. -/
def independenceBound (l Q : ℕ) : ℕ :=
  deletionIndependenceBound (protectedBound l) Q

/-! ## Uniform Kronecker and deletion bounds -/

/-- Maximum tuple length which can occur at stage `l`. -/
def tupleLengthBound (l : ℕ) : ℕ :=
  protectedBound l + blockSize l

/-- One uniform Kronecker bound for a fixed tuple length.  All groups in the Wallace
construction live in universe zero, so fixing that universe here makes the numerical schedule
literally a single sequence of natural numbers. -/
noncomputable def rawKroneckerBound (l m : ℕ) : ℕ :=
  Classical.choose (exists_uniformKroneckerBound.{0} m (stageError_pos l))

/--
@isnad1 id=isunifor.0h2v.s3.9f0495031cf0 from=translated src=- shape=58ccb911 vocab=c90ab4be
-/
theorem rawKroneckerBound_spec (l m : ℕ) :
    IsUniformKroneckerBound.{0} m (stageError l) (rawKroneckerBound l m) :=
  Classical.choose_spec (exists_uniformKroneckerBound.{0} m (stageError_pos l))

/-- A single relation-height bound which works for every *positive* tuple length possible at
stage `l`.  This is the paper's maximum over `1 ≤ m ≤ R_l + N_l`; the maximum with `1` is used
by the finite disjointness argument.  The empty-tuple case is handled separately below and does
not enter the numerical schedule. -/
noncomputable def kroneckerBound (l : ℕ) : ℕ :=
  max 1 ((Finset.Icc 1 (tupleLengthBound l)).sup (rawKroneckerBound l))

/--
@isnad1 id=le.0h1v.s3.c672a62cb3e8 from=translated src=- shape=8a62b088 vocab=5b4a8e3f
-/
theorem one_le_kroneckerBound (l : ℕ) : 1 ≤ kroneckerBound l := by
  exact Nat.le_max_left _ _

/--
@isnad1 id=le.2h2v.s4.f3610de54a7f from=translated src=- shape=bce740fa vocab=c2b63c2d
-/
theorem rawKroneckerBound_le (l m : ℕ) (hm0 : 0 < m)
    (hm : m ≤ tupleLengthBound l) :
    rawKroneckerBound l m ≤ kroneckerBound l := by
  apply le_trans _ (Nat.le_max_right 1 _)
  apply Finset.le_sup
  exact Finset.mem_Icc.mpr ⟨hm0, hm⟩

/-- The uniform Kronecker assertion is vacuous for an empty tuple, so no value `q(0, ε_l)` is
needed in the paper's maximum.
@isnad1 id=isunifor.0h1v.s3.55881a81e67d from=translated src=- shape=88774e53 vocab=19fad89a
-/
theorem kroneckerBound_spec_zero (l : ℕ) :
    IsUniformKroneckerBound.{0} 0 (stageError l) (kroneckerBound l) := by
  intro G _inst z t _ht
  exact ⟨0, fun i ↦ Fin.elim0 i⟩

/-- The scheduled height bound is valid for every tuple that can occur at this stage.
@isnad1 id=isunifor.1h2v.s4.8b4bd583dfdc from=translated src=- shape=0659d62e vocab=2f3e772b
-/
theorem kroneckerBound_spec (l m : ℕ) (hm : m ≤ tupleLengthBound l) :
    IsUniformKroneckerBound.{0} m (stageError l) (kroneckerBound l) :=
  by
    rcases m with _ | m
    · exact kroneckerBound_spec_zero l
    · exact IsUniformKroneckerBound.mono (rawKroneckerBound_spec l (m + 1))
        (rawKroneckerBound_le l (m + 1) (Nat.succ_pos m) hm)

/-- The independence threshold `M_l` used in the preprocessing of stage `l`. -/
noncomputable def stageIndependenceBound (l : ℕ) : ℕ :=
  independenceBound l (kroneckerBound l)

/--
@isnad1 id=le.2h4v.s5.dcdc314ce3c3 from=translated src=- shape=7cb370a1 vocab=c435b920
-/
theorem card_union_le_tupleLengthBound {G : Type*} [DecidableEq G]
    {l : ℕ} {A Y : Finset G}
    (hA : A.card ≤ protectedBound l) (hY : Y.card ≤ blockSize l) :
    (A ∪ Y).card ≤ tupleLengthBound l := by
  calc
    (A ∪ Y).card ≤ A.card + Y.card := Finset.card_union_le A Y
    _ ≤ protectedBound l + blockSize l := Nat.add_le_add hA hY
    _ = tupleLengthBound l := rfl

/-- The bounded-deletion lemma specialized to the numerical schedule.
@isnad1 id=ex.2h4v.s6.b75d509d5aad from=translated src=- shape=a9cff4bf vocab=b0845dd8
-/
theorem exists_stage_deletion {G : Type*} [AddCommGroup G] [DecidableEq G]
    {l : ℕ} (A X : Finset G) (hA : A.card ≤ protectedBound l)
    (hX : BoundedIndependent (stageIndependenceBound l) X) :
    ∃ Y : Finset G, Y ⊆ X ∧ (X \ Y).card ≤ A.card ∧
      MixedRelationFree (kroneckerBound l) A Y := by
  classical
  simpa only [stageIndependenceBound, independenceBound] using
    bounded_deletion (protectedBound l) (kroneckerBound l) A X hA hX

end

end FusionSchedule
end Wallace
