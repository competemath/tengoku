import Tengoku.Rankamplificationtotient.RankAmplification.Definitions
import Tengoku.Rankamplificationtotient.RankAmplification.Scales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The floored cutoff is the paper's real cutoff The paper displays the above-cutoff diagonal `D^φ_{h,>Y}(x)` at a *real* cutoff, for instance `Y = e^{√J G}` in Theorem 1.1, `Y = e^{√J T}` in Theorem 10.13, and `Y = Z` in Theorem 10.25, whereas the Lean development carries a natural cutoff and instantiates it at `⌊Y⌋₊`. -/

namespace RankAmplification

open Nat

/-- For a natural `n` and a nonnegative real `Y`, the floored strict inequality is the real one.
@isnad1 id=iff.1h2v.s5.0e8efbdd3465 from=translated src=- shape=fcda727e vocab=d41f1159
-/
theorem natFloor_lt_iff_lt {Y : ℝ} (hY : 0 ≤ Y) (n : ℕ) :
    ⌊Y⌋₊ < n ↔ Y < (n : ℝ) :=
  Nat.floor_lt hY

/-- The cutoff clause of a diagonal representation is unchanged by flooring a real cutoff.
@isnad1 id=iff.1h4v.s6.466625d089c9 from=translated src=- shape=aa86c083 vocab=0b5058c2
-/
theorem diagonalCutoff_natFloor_iff {Y : ℝ} (hY : 0 ≤ Y) (h j r : ℕ) :
    ⌊Y⌋₊ < largestPrimeFactor (diagonalGamma h j * r) ↔
      Y < (largestPrimeFactor (diagonalGamma h j * r) : ℝ) :=
  natFloor_lt_iff_lt hY _

/-- A diagonal representation at the floored cutoff is exactly one at the paper's real cutoff.
@isnad1 id=iff.1h5v.s8.a4bcfc68030f from=translated src=- shape=0cdca477 vocab=27a1cfad
-/
theorem isDiagonalRepresentation_natFloor_iff {Y : ℝ} (hY : 0 ≤ Y) (h n j r : ℕ) :
    IsDiagonalRepresentation h ⌊Y⌋₊ n j r ↔
      (IsSameSupportIndex h j ∧
        1 ≤ r ∧
        n = j * (diagonalA h j * r + 1) ∧
        n + h = (j + h) * (diagonalB h j * r + 1) ∧
        Nat.Prime (diagonalA h j * r + 1) ∧
        Nat.Prime (diagonalB h j * r + 1) ∧
        Nat.Coprime (diagonalA h j * r + 1) j ∧
        Nat.Coprime (diagonalB h j * r + 1) (j + h) ∧
        Y < (largestPrimeFactor (diagonalGamma h j * r) : ℝ)) := by
  unfold IsDiagonalRepresentation
  rw [diagonalCutoff_natFloor_iff hY]

/-- Membership in the above-cutoff diagonal at a floored real cutoff is the paper's condition.
@isnad1 id=iff.1h3v.s8.9660f1cbbe2f from=translated src=- shape=a09e6030 vocab=daab8efa
-/
theorem isAboveCutoffDiagonal_natFloor_iff {Y : ℝ} (hY : 0 ≤ Y) (h n : ℕ) :
    IsAboveCutoffDiagonal h ⌊Y⌋₊ n ↔
      ∃ j r, IsSameSupportIndex h j ∧
        1 ≤ r ∧
        n = j * (diagonalA h j * r + 1) ∧
        n + h = (j + h) * (diagonalB h j * r + 1) ∧
        Nat.Prime (diagonalA h j * r + 1) ∧
        Nat.Prime (diagonalB h j * r + 1) ∧
        Nat.Coprime (diagonalA h j * r + 1) j ∧
        Nat.Coprime (diagonalB h j * r + 1) (j + h) ∧
        Y < (largestPrimeFactor (diagonalGamma h j * r) : ℝ) := by
  unfold IsAboveCutoffDiagonal
  constructor
  · rintro ⟨j, r, hrep⟩
    exact ⟨j, r, (isDiagonalRepresentation_natFloor_iff hY h n j r).1 hrep⟩
  · rintro ⟨j, r, hrep⟩
    exact ⟨j, r, (isDiagonalRepresentation_natFloor_iff hY h n j r).2 hrep⟩

/-- Two real cutoffs with the same floor give the same diagonal count.
@isnad1 id=eq.3h4v.s6.02dd996937eb from=translated src=- shape=c6a4c8d9 vocab=a7990440
-/
theorem aboveCutoffDiagonalCount_natFloor_congr {Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hYZ : ∀ n : ℕ, Y < (n : ℝ) ↔ Z < (n : ℝ)) (x h : ℕ) :
    aboveCutoffDiagonalCount x h ⌊Y⌋₊ = aboveCutoffDiagonalCount x h ⌊Z⌋₊ := by
  have hfloor : ⌊Y⌋₊ = ⌊Z⌋₊ := by
    have h1 : ⌊Y⌋₊ < ⌊Z⌋₊ + 1 := by
      rw [natFloor_lt_iff_lt hY]
      refine (hYZ (⌊Z⌋₊ + 1)).2 ?_
      push_cast
      exact Nat.lt_floor_add_one Z
    have h2 : ⌊Z⌋₊ < ⌊Y⌋₊ + 1 := by
      rw [natFloor_lt_iff_lt hZ]
      refine (hYZ (⌊Y⌋₊ + 1)).1 ?_
      push_cast
      exact Nat.lt_floor_add_one Y
    omega
  rw [hfloor]

end RankAmplification
