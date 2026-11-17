/-
The golden moment of Agrawal's congruence at r = 5.

This module isolates the new bridge in two layers:

* a ring-theoretic factorization of the quadratic moment unit;
* its consequence for every quintic index (a multiplicative character
  with values in the additive group Z/5Z).

The classical prior art computes the quintic character of the golden
unit.  The statement formalized here identifies the quadratic moment
unit arising from Agrawal's congruence with the cube of that character.
-/
import Tengoku.Seed.Algebra.Group.TypeTags.Hom
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.RingTheory.ZMod.UnitsCyclic
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {R : Type*} [CommRing R]

/-- The square root of five coordinated with a fifth root `ζ`.-/
def cyclotomicSqrtFive (ζ : R) : R := 1 + 2 * (ζ + ζ ^ 4)

/-- The golden unit coordinated with a fifth root `ζ`.

When `ζ` is a primitive complex fifth root, this is `(1 + √5) / 2`.-/
def cyclotomicGoldenUnit (ζ : R) : R := 1 + ζ + ζ ^ 4

/-- The weighted unit whose quintic index is the quadratic moment `M₂`.

The weights are the quadratic residues `1, 4, 4, 1` modulo five.-/
def quadraticMomentUnit (ζ : R) : R :=
  (ζ - 1) * (ζ ^ 2 - 1) ^ 4 * (ζ ^ 3 - 1) ^ 4 * (ζ ^ 4 - 1)

lemma cyclotomic_sqrtFive_sq {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    cyclotomicSqrtFive ζ ^ 2 = 5 := by
  unfold cyclotomicSqrtFive
  linear_combination (4 * ζ ^ 4 - 4 * ζ ^ 3 + 8 * ζ - 4) * hζ

lemma cyclotomic_pair_left {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    2 * ((ζ - 1) * (ζ ^ 4 - 1)) = 5 - cyclotomicSqrtFive ζ := by
  unfold cyclotomicSqrtFive
  linear_combination (2 * ζ - 2) * hζ

lemma cyclotomic_pair_right {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    2 * ((ζ ^ 2 - 1) * (ζ ^ 3 - 1)) = 5 + cyclotomicSqrtFive ζ := by
  unfold cyclotomicSqrtFive
  linear_combination (2 * ζ - 4) * hζ

lemma cyclotomic_pair_product {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    ((ζ - 1) * (ζ ^ 4 - 1)) * ((ζ ^ 2 - 1) * (ζ ^ 3 - 1)) = 5 := by
  linear_combination (ζ ^ 6 - 2 * ζ ^ 5 + ζ ^ 3 + 3 * ζ - 4) * hζ

lemma cyclotomic_pair_right_eq_sqrt_mul_golden {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    (ζ ^ 2 - 1) * (ζ ^ 3 - 1) =
      cyclotomicSqrtFive ζ * cyclotomicGoldenUnit ζ := by
  unfold cyclotomicSqrtFive cyclotomicGoldenUnit
  linear_combination (-2 * ζ ^ 4 + 2 * ζ ^ 3 - 3 * ζ) * hζ

/-- **Golden factorization of the quadratic moment unit.**

`U₂ = (√5)⁵ ε³`.  Thus every quintic index kills the first factor and
reads `U₂` as three times the index of the golden unit.-/
theorem golden_moment_factorization {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    quadraticMomentUnit ζ =
      cyclotomicSqrtFive ζ ^ 5 * cyclotomicGoldenUnit ζ ^ 3 := by
  let A := (ζ - 1) * (ζ ^ 4 - 1)
  let B := (ζ ^ 2 - 1) * (ζ ^ 3 - 1)
  have hAB : A * B = 5 := by
    simpa [A, B] using cyclotomic_pair_product (R := R) hζ
  have hB : B = cyclotomicSqrtFive ζ * cyclotomicGoldenUnit ζ := by
    simpa [B] using cyclotomic_pair_right_eq_sqrt_mul_golden (R := R) hζ
  have hs : cyclotomicSqrtFive ζ ^ 2 = 5 :=
    cyclotomic_sqrtFive_sq (R := R) hζ
  rw [show quadraticMomentUnit ζ = A * B ^ 4 by
    dsimp [quadraticMomentUnit, A, B]
    ring]
  rw [show A * B ^ 4 = (A * B) * B ^ 3 by ring, hAB, hB, ← hs]
  ring

/-- Any quintic index sends a fifth power times a cube to three times
the index of the cubed element.-/
theorem quintic_index_of_fifth_mul_cube {G : Type*} [CommGroup G]
    (χ : G →* Multiplicative (ZMod 5)) (s ε U : G)
    (hU : U = s ^ 5 * ε ^ 3) :
    (χ U).toAdd = 3 * (χ ε).toAdd := by
  rw [hU, map_mul, map_pow, map_pow]
  rw [toAdd_mul, toAdd_pow, toAdd_pow]
  have hfive : 5 • (χ s).toAdd = 0 := by
    calc
      5 • (χ s).toAdd = (5 : ZMod 5) * (χ s).toAdd := nsmul_eq_mul _ _
      _ = 0 := by change 0 * (χ s).toAdd = 0; rw [zero_mul]
  rw [hfive, zero_add]
  exact nsmul_eq_mul _ _

/-- **The golden theorem, index form.**

If units `U`, `s`, and `ε` represent respectively the quadratic moment
unit, the coordinated square root of five, and the golden unit, then
every quintic index satisfies `ind(U) = 3 · ind(ε)`.-/
theorem golden_moment_index {ζ : R} (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (χ : Rˣ →* Multiplicative (ZMod 5)) (U s ε : Rˣ)
    (hU : (U : R) = quadraticMomentUnit ζ)
    (hs : (s : R) = cyclotomicSqrtFive ζ)
    (hε : (ε : R) = cyclotomicGoldenUnit ζ) :
    (χ U).toAdd = 3 * (χ ε).toAdd := by
  apply quintic_index_of_fifth_mul_cube χ s ε U
  apply Units.ext
  simpa [hU, hs, hε] using golden_moment_factorization (R := R) hζ

/-- A discrete logarithm modulo five on `(ZMod p)ˣ`.

The cyclic generator is chosen noncomputably.  Reducing its full discrete
logarithm modulo five gives the quintic index; changing the generator rescales
all indices by the same nonzero element of `ZMod 5`, so the golden identity is
independent of that choice.-/
noncomputable def quinticIndex {p : ℕ} [Fact p.Prime] (h5 : 5 ∣ p - 1) :
    (ZMod p)ˣ →* Multiplicative (ZMod 5) := by
  let e0 := zmodCyclicMulEquiv (ZMod.isCyclic_units_prime (Fact.out : p.Prime))
  have hc : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  let e : Multiplicative (ZMod (p - 1)) ≃* (ZMod p)ˣ := hc ▸ e0
  let red : Multiplicative (ZMod (p - 1)) →* Multiplicative (ZMod 5) :=
    (ZMod.castHom h5 (ZMod 5)).toAddMonoidHom.toMultiplicative
  exact red.comp e.symm.toMonoidHom

/-- **The golden theorem over a prime field.**

For a prime `p ≡ 1 (mod 5)`, the discrete quintic index of the quadratic
moment unit is three times the index of the golden unit.-/
theorem zmod_golden_moment_index {p : ℕ} [Fact p.Prime] (h5 : 5 ∣ p - 1)
    {ζ : ZMod p} (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (U s ε : (ZMod p)ˣ)
    (hU : (U : ZMod p) = quadraticMomentUnit ζ)
    (hs : (s : ZMod p) = cyclotomicSqrtFive ζ)
    (hε : (ε : ZMod p) = cyclotomicGoldenUnit ζ) :
    (quinticIndex h5 U).toAdd = 3 * (quinticIndex h5 ε).toAdd :=
  golden_moment_index hζ (quinticIndex h5) U s ε hU hs hε

end AgrawalCore
