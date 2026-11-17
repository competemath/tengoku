import Tengoku
import Tengoku.AgrawalR5.AgrawalCore.GoldenMoment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Submitted proof of the independent statement in `Challenge.lean`.

The definitions below are deliberately repeated.  Comparator checks that
their exported declarations, and therefore the theorem statement, are
identical to the trusted challenge before it accepts the proof.
-/
namespace GoldenMomentChallenge

variable {R : Type*} [CommRing R]

def cyclotomicSqrtFive (ζ : R) : R :=
  1 + 2 * (ζ + ζ ^ 4)

def cyclotomicGoldenUnit (ζ : R) : R :=
  1 + ζ + ζ ^ 4

def quadraticMomentUnit (ζ : R) : R :=
  (ζ - 1) * (ζ ^ 2 - 1) ^ 4 * (ζ ^ 3 - 1) ^ 4 * (ζ ^ 4 - 1)

/--
@isnad1 id=eq.1h2v.s7.5766eee0c5f0 from=translated src=- shape=bcea0f78 vocab=19a4edd2
-/
theorem golden_moment_factorization {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    quadraticMomentUnit ζ =
      cyclotomicSqrtFive ζ ^ 5 * cyclotomicGoldenUnit ζ ^ 3 := by
  simpa [quadraticMomentUnit, cyclotomicSqrtFive, cyclotomicGoldenUnit,
    AgrawalCore.quadraticMomentUnit, AgrawalCore.cyclotomicSqrtFive,
    AgrawalCore.cyclotomicGoldenUnit] using
    (AgrawalCore.golden_moment_factorization (R := R) hζ)

end GoldenMomentChallenge
