import Tengoku.Seed.Data.Nat.Totient
import Tengoku.Seed.NumberTheory.SmoothNumbers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Core arithmetic definitions Definitions shared by the formalization of *Rank Amplification for Shifted Equal Values of Euler's Totient Function*. -/

namespace RankAmplification

/-- The finite set of prime divisors of `n`.-/
abbrev primeSupport (n : ℕ) : Finset ℕ := n.primeFactors

/-- The product of the distinct prime divisors of `n`.-/
def radical (n : ℕ) : ℕ := ∏ p ∈ primeSupport n, p

/-- The largest prime factor, with the paper's convention `largestPrimeFactor 1 = 1`.-/
def largestPrimeFactor (n : ℕ) : ℕ := max 1 ((primeSupport n).sup id)

/-- `n` is `y`-smooth when it is positive and all of its prime divisors are at most `y`.-/
def IsSmooth (y n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ primeSupport n, p ≤ y

/-- The number of prime-factor occurrences of `n` strictly above `y`.-/
def largePrimeRank (y n : ℕ) : ℕ :=
  ∑ p ∈ (primeSupport n).filter (y < ·), n.factorization p

/-- The integers in `[1, x]` on which Euler's totient agrees with its shift by `h`.-/
def shiftedEqualTotientSet (x h : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ n.totient = (n + h).totient

/-- The exact shifted equal-totient counting function `S_h^φ(x)`.-/
def shiftedEqualTotientCount (x h : ℕ) : ℕ := (shiftedEqualTotientSet x h).card

/-- The smooth-totient census `Φ(X,Y)`.-/
noncomputable def smoothTotientSet (X Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun m ↦ IsSmooth Y m.totient

/-- The exact cardinality of the smooth-totient census.-/
noncomputable def smoothTotientCount (X Y : ℕ) : ℕ := (smoothTotientSet X Y).card

/-- The nonsmooth shifted set `B_h(x;y)`.-/
def nonsmoothShiftedSet (x h y : ℕ) : Finset ℕ :=
  (shiftedEqualTotientSet x h).filter fun n ↦ y < largestPrimeFactor n.totient

/-- The exact cardinality of `B_h(x;y)`.-/
def nonsmoothShiftedCount (x h y : ℕ) : ℕ := (nonsmoothShiftedSet x h y).card

/-- The same-support index predicate defining `J_h`.-/
def IsSameSupportIndex (h j : ℕ) : Prop := 1 ≤ j ∧ primeSupport j = primeSupport (j + h)

/-- The same-support index set `J_h`.-/
def sameSupportIndices (h : ℕ) : Set ℕ := {j | IsSameSupportIndex h j}

/-- The common divisor `d_j = gcd(j,j+h)`.-/
def diagonalGCD (h j : ℕ) : ℕ := Nat.gcd j (j + h)

/-- The coefficient `A_j = (j+h)/d_j`.-/
def diagonalA (h j : ℕ) : ℕ := (j + h) / diagonalGCD h j

/-- The coefficient `B_j = j/d_j`.-/
def diagonalB (h j : ℕ) : ℕ := j / diagonalGCD h j

/-- The common-totient coefficient `Γ_j = φ(j) A_j`.-/
def diagonalGamma (h j : ℕ) : ℕ := j.totient * diagonalA h j

/-- One representation in the above-cutoff Graham--Holt--Pomerance diagonal.-/
def IsDiagonalRepresentation (h Y n j r : ℕ) : Prop :=
  IsSameSupportIndex h j ∧
    1 ≤ r ∧
    n = j * (diagonalA h j * r + 1) ∧
    n + h = (j + h) * (diagonalB h j * r + 1) ∧
    Nat.Prime (diagonalA h j * r + 1) ∧
    Nat.Prime (diagonalB h j * r + 1) ∧
    Nat.Coprime (diagonalA h j * r + 1) j ∧
    Nat.Coprime (diagonalB h j * r + 1) (j + h) ∧
    Y < largestPrimeFactor (diagonalGamma h j * r)

/-- Membership in the above-cutoff diagonal, counting integers rather than representations.-/
def IsAboveCutoffDiagonal (h Y n : ℕ) : Prop :=
  ∃ j r : ℕ, IsDiagonalRepresentation h Y n j r

/-- The above-cutoff diagonal integers in `[1,x]`.-/
noncomputable def aboveCutoffDiagonalSet (x h Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n ↦ IsAboveCutoffDiagonal h Y n

/-- The exact diagonal counting function `D^φ_{h,>Y}(x)`.-/
noncomputable def aboveCutoffDiagonalCount (x h Y : ℕ) : ℕ :=
  (aboveCutoffDiagonalSet x h Y).card

end RankAmplification
