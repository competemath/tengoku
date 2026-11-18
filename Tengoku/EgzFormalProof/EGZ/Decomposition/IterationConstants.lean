import Tengoku.EgzFormalProof.EGZ.Decomposition.IterationBounds
import Tengoku.EgzFormalProof.EGZ.Decomposition.IntervalCapacity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Uniform constants for the bounded decomposition iteration -/

namespace EGZ.FlagDecomposition.Iteration

/-- A positive integer upper bound for face events on one surviving lineage.-/
noncomputable def faceCapacity (d : ℕ) (ε : ℝ) : ℕ :=
  max 1 ⌈((((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2))⌉₊

/--
@isnad1 id=le.0h2v.s3.039a7c7f6ac1 from=translated src=- shape=25b8bdde vocab=829d2fc9
-/
theorem one_le_faceCapacity (d : ℕ) (ε : ℝ) : 1 ≤ faceCapacity d ε := le_max_left _ _

/--
@isnad1 id=le.1h3v.s6.c32f635104dc from=translated src=- shape=9fb27506 vocab=11f6ae4c
-/
theorem le_faceCapacity_of_real_le {d n : ℕ} {ε : ℝ}
    (h : (n : ℝ) ≤ (((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2)) :
    n ≤ faceCapacity d ε := by
  have hn : n ≤ ⌈((((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2))⌉₊ := by
    exact_mod_cast h.trans (Nat.le_ceil _)
  exact hn.trans (le_max_right _ _)

noncomputable def intervalCapacity (d : ℕ) (ε : ℝ) (a : ℕ) : ℕ :=
  2 ^ a * faceCapacity d ε

/--
@isnad1 id=le.0h3v.s4.73a224bc8343 from=translated src=- shape=f2476271 vocab=cc18e469
-/
theorem pow_le_intervalCapacity (d : ℕ) (ε : ℝ) (a : ℕ) :
    2 ^ a ≤ intervalCapacity d ε a := by
  change 2 ^ a ≤ 2 ^ a * faceCapacity d ε
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ a) (one_le_faceCapacity d ε)

/--
@isnad1 id=le.0h3v.s4.a80d8c09b876 from=translated src=- shape=bad53a6c vocab=1cd323a4
-/
theorem one_le_intervalCapacity (d : ℕ) (ε : ℝ) (a : ℕ) :
    1 ≤ intervalCapacity d ε a :=
  (Nat.one_le_two_pow).trans (pow_le_intervalCapacity d ε a)

noncomputable def stoppingBound (d : ℕ) (ε : ℝ) : ℕ :=
  intervalCapacityBound (2 * (d + 1) ^ 2 + 1) (intervalCapacity d ε)

/--
@isnad1 id=lt.0h2v.s3.66d760c79e5e from=translated src=- shape=25b8bdde vocab=3dbe96c1
-/
theorem stoppingBound_pos (d : ℕ) (ε : ℝ) : 0 < stoppingBound d ε := by
  apply length_lt_intervalCapacityBound _ _ 0 (fun _ ↦ 0)
  · intro i hi
    omega
  · intro a b l _ hb
    omega

noncomputable def finalScale (d : ℕ) (ε : ℝ) : ℝ :=
  stageScale d ε (stoppingBound d ε)

/--
@isnad1 id=lt.1h2v.s4.bd50f2393f39 from=translated src=- shape=696abc3b vocab=196fe9e5
-/
theorem finalScale_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < finalScale d ε :=
  stageScale_pos d hε _

/--
@isnad1 id=le.3h3v.s5.caab3b522b2c from=translated src=- shape=26391b01 vocab=6b8bcd94
-/
theorem finalScale_le {d i : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hi : i ≤ stoppingBound d ε) : finalScale d ε ≤ stageScale d ε i :=
  stageScale_antitone hd hε hi

end EGZ.FlagDecomposition.Iteration
