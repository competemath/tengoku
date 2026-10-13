/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Bounded changes on a Boolean cube

A bound for changing one coordinate extends to the ordinary, unnormalized
Hamming distance. It also gives a discrete intermediate-value theorem: a
natural-valued function on a finite Boolean cube cannot skip an interval
wider than its one-coordinate bound. Neither conclusion assumes monotonicity.
-/

@[expose] public section

namespace Algebraic.BooleanCube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every Boolean vector is reachable from any other by coordinate updates.
@isnad1 id=var.0h6v.s5.bc0c5b2f9185 from=translated src=- shape=083093a7 vocab=42ebbc39
-/
theorem update_induction (start finish : ι → Bool) (P : (ι → Bool) → Prop)
    (initial : P start)
    (step : ∀ vector index value, P vector → P (Function.update vector index value)) :
    P finish := by
  classical
  have patches : ∀ s : Finset ι, P (fun i => if i ∈ s then finish i else start i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using initial
    | @insert index s absent ih =>
      have next := step _ index (finish index) ih
      convert next using 1
      funext i
      by_cases equal : i = index <;> simp [equal]
  simpa using patches Finset.univ

private theorem update_distance (start finish : ι → Bool) (index : ι)
    (different : start index ≠ finish index) :
    hammingDist start (Function.update finish index (start index)) + 1 =
      hammingDist start finish := by
  classical
  have changed :
      Finset.univ.filter (fun i => start i ≠ Function.update finish index (start index) i) =
        (Finset.univ.filter (fun i => start i ≠ finish i)).erase index := by
    ext i
    by_cases equal : i = index <;> simp [equal, Function.update_apply]
  unfold hammingDist
  rw [changed]
  exact Finset.card_erase_add_one (by simp [different])

/-- A one-coordinate upper bound extends to Hamming distance.
@isnad1 id=le.1h5v.s6.ffd538cf5ee6 from=translated src=- shape=5652f199 vocab=7db8b6f1
-/
theorem le_add_mul_hammingDist (measure : (ι → Bool) → Nat) (bound : Nat)
    (step : ∀ vector index value,
      measure (Function.update vector index value) ≤ measure vector + bound)
    (start finish : ι → Bool) :
    measure finish ≤ measure start + bound * hammingDist start finish := by
  classical
  generalize distance : hammingDist start finish = d
  induction d using Nat.strong_induction_on generalizing finish with
  | h d ih =>
    by_cases equal : start = finish
    · subst finish
      have : d = 0 := by simpa using distance.symm
      subst d
      simp
    · obtain ⟨index, different⟩ := Function.ne_iff.mp equal
      let previous := Function.update finish index (start index)
      have decrease : hammingDist start previous + 1 = d := by
        simpa [previous, distance] using update_distance start finish index different
      have prior := ih (hammingDist start previous) (by omega) previous rfl
      have next := step previous index (finish index)
      have restored : Function.update previous index (finish index) = finish := by
        simp [previous]
      rw [restored] at next
      calc
        measure finish ≤ measure start + bound * hammingDist start previous + bound := by omega
        _ = measure start + bound * d := by rw [← decrease, Nat.mul_add]; omega

/-- The symmetric form of the Hamming Lipschitz bound, using natural distance.
@isnad1 id=le.1h5v.s6.6271d83858b5 from=translated src=- shape=29f05385 vocab=b9aff4d9
-/
theorem dist_le_mul_hammingDist (measure : (ι → Bool) → Nat) (bound : Nat)
    (step : ∀ vector index value,
      measure (Function.update vector index value) ≤ measure vector + bound)
    (start finish : ι → Bool) :
    Nat.dist (measure start) (measure finish) ≤ bound * hammingDist start finish := by
  have forward := le_add_mul_hammingDist measure bound step start finish
  have backward := le_add_mul_hammingDist measure bound step finish start
  rw [hammingDist_comm finish start] at backward
  unfold Nat.dist
  omega

/-- Discrete intermediate values on a Boolean cube. The first threshold
crossing overshoots by at most the one-coordinate bound.
@isnad1 id=ex.3h6v.s6.89a403dd8b79 from=translated src=- shape=51a39a8e vocab=cb2d626a
-/
theorem exists_between (measure : (ι → Bool) → Nat) (bound threshold : Nat)
    (step : ∀ vector index value,
      measure (Function.update vector index value) ≤ measure vector + bound)
    (start finish : ι → Bool)
    (below : measure start ≤ threshold) (above : threshold < measure finish) :
    ∃ vector, threshold < measure vector ∧ measure vector ≤ threshold + bound := by
  classical
  have reached : measure finish ≤ threshold ∨
      ∃ vector, threshold < measure vector ∧ measure vector ≤ threshold + bound := by
    apply update_induction start finish
      (fun current => measure current ≤ threshold ∨
        ∃ vector, threshold < measure vector ∧ measure vector ≤ threshold + bound)
      (Or.inl below)
    intro current index value previous
    rcases previous with low | found
    · by_cases nextLow : measure (Function.update current index value) ≤ threshold
      · exact Or.inl nextLow
      · exact Or.inr ⟨_, Nat.lt_of_not_ge nextLow,
          (step current index value).trans (Nat.add_le_add_right low bound)⟩
    · exact Or.inr found
  exact reached.resolve_left (by omega)

end Algebraic.BooleanCube
