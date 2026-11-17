/-
The exact bridge between the abstract moment used by the local Fourier
argument and the multiplicative quadratic-moment unit at r = 5.

`MomentObstruction.lean` defines the additive moment

  M_j(e) = ∑ a, a^j e(a).

`GoldenMoment.lean` factors the multiplicative unit

  U₂ = ∏ a, u_a^(a²).

This module proves, in the kernel, that applying a quintic index to the
second product gives exactly the first sum.  It then composes this identity
with the golden factorization.  No table of computed indices and no
Williams--Hardy formula is used as a premise.
-/
import Tengoku.AgrawalR5.AgrawalCore.GoldenMoment
import Tengoku.AgrawalR5.AgrawalCore.MomentObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

open scoped BigOperators

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The four canonical units modulo five.  They are named explicitly so
that the finite `r = 5` product can be replayed without a native evaluator.-/
def zmodFiveUnitTwo : (ZMod 5)ˣ where
  val := 2
  inv := 3
  val_inv := by decide
  inv_val := by decide

def zmodFiveUnitThree : (ZMod 5)ˣ where
  val := 3
  inv := 2
  val_inv := by decide
  inv_val := by decide

def zmodFiveUnitFour : (ZMod 5)ˣ where
  val := 4
  inv := 4
  val_inv := by decide
  inv_val := by decide

/--
@isnad1 id=eq.0h0v.s10.2b258065328c from=translated src=- shape=b3b0fac4 vocab=bd452530
-/
lemma zmodFive_units_univ :
    (Finset.univ : Finset (ZMod 5)ˣ) =
      {1, zmodFiveUnitTwo, zmodFiveUnitThree, zmodFiveUnitFour} := by
  decide

/--
@isnad1 id=eq.0h0v.s7.10cf7831bd0d from=translated src=- shape=8a5ecf25 vocab=6d3ef9b2
-/
@[simp] lemma zmodFiveUnitOne_val :
    (((1 : (ZMod 5)ˣ) : ZMod 5).val) = 1 := by decide

/--
@isnad1 id=eq.0h0v.s5.87de45b48767 from=translated src=- shape=21646f88 vocab=ba5ad323
-/
@[simp] lemma zmodFiveUnitTwo_val :
    (((zmodFiveUnitTwo : (ZMod 5)ˣ) : ZMod 5).val) = 2 := rfl

/--
@isnad1 id=eq.0h0v.s5.01cdd30ea659 from=translated src=- shape=21646f88 vocab=8a8ce62d
-/
@[simp] lemma zmodFiveUnitThree_val :
    (((zmodFiveUnitThree : (ZMod 5)ˣ) : ZMod 5).val) = 3 := rfl

/--
@isnad1 id=eq.0h0v.s5.1f3b00a84f11 from=translated src=- shape=21646f88 vocab=b1c78b03
-/
@[simp] lemma zmodFiveUnitFour_val :
    (((zmodFiveUnitFour : (ZMod 5)ˣ) : ZMod 5).val) = 4 := rfl

/--
@isnad1 id=eq.0h0v.s8.c9302fbeab83 from=translated src=- shape=293c7185 vocab=16396eb0
-/
@[simp] lemma zmodFiveUnitOne_sq_val :
    ((((1 : (ZMod 5)ˣ) : ZMod 5) ^ 2).val) = 1 := by decide

/--
@isnad1 id=eq.0h0v.s7.439d8d7d136a from=translated src=- shape=78b21d5d vocab=b3c18e2d
-/
@[simp] lemma zmodFiveUnitTwo_sq_val :
    ((((zmodFiveUnitTwo : (ZMod 5)ˣ) : ZMod 5) ^ 2).val) = 4 := by
  decide

/--
@isnad1 id=eq.0h0v.s7.b7d057b4b4d0 from=translated src=- shape=78b21d5d vocab=a2e49f3f
-/
@[simp] lemma zmodFiveUnitThree_sq_val :
    ((((zmodFiveUnitThree : (ZMod 5)ˣ) : ZMod 5) ^ 2).val) = 4 := by
  decide

/--
@isnad1 id=eq.0h0v.s7.782194ae843f from=translated src=- shape=78b21d5d vocab=744c76fa
-/
@[simp] lemma zmodFiveUnitFour_sq_val :
    ((((zmodFiveUnitFour : (ZMod 5)ˣ) : ZMod 5) ^ 2).val) = 1 := by
  decide

/-- The multiplicative unit attached to the `j`-th moment over
`(ZMod 5)ˣ`.

The exponent is the canonical representative in `{0,1,2,3,4}` of
`a^j : ZMod 5`.  Changing that representative by a multiple of five does
not change its image under a quintic index.-/
def indexedMomentUnit {G : Type*} [CommGroup G]
    (u : (ZMod 5)ˣ → G) (j : ℕ) : G :=
  ∏ a : (ZMod 5)ˣ, u a ^ (((a : ZMod 5) ^ j).val)

/-- Applying a quintic index to the multiplicative moment unit gives
exactly the additive moment of the indexed family.

This is the missing product-to-sum interface: it identifies the `M_j`
of `MomentObstruction.lean` with the index of `indexedMomentUnit u j`.
@isnad1 id=eq.0h4v.s9.457cefd62855 from=translated src=- shape=906768d1 vocab=fef2bfcb
-/
theorem quintic_index_indexedMomentUnit_eq_moment
    {G : Type*} [CommGroup G]
    (χ : G →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → G) (j : ℕ) :
    (χ (indexedMomentUnit u j)).toAdd =
      moment (fun a : (ZMod 5)ˣ ↦ (χ (u a)).toAdd) j := by
  unfold indexedMomentUnit moment
  rw [map_prod, toAdd_prod]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_pow, toAdd_pow, nsmul_eq_mul]
  change
    (((((a : ZMod 5) ^ j).val : ℕ) : ZMod 5) *
        (χ (u a)).toAdd) =
      (a : ZMod 5) ^ j * (χ (u a)).toAdd
  rw [ZMod.natCast_zmod_val]

/-- The abstract product at `j = 2` is literally the displayed
cyclotomic quadratic-moment unit, once the four entries are
`u_a = ζ^a - 1`.

Unlike a numerical table replay, this is a symbolic identity over every
commutative ring.
@isnad1 id=eq.1h3v.s7.957faca939e5 from=translated src=- shape=0f990898 vocab=81b1e2c9
-/
theorem indexedMomentUnit_two_eq_quadraticMomentUnit
    {R : Type*} [CommRing R]
    {ζ : R}
    (u : (ZMod 5)ˣ → Rˣ)
    (hu : ∀ a : (ZMod 5)ˣ,
      (u a : R) = ζ ^ ((a : ZMod 5).val) - 1) :
    ((indexedMomentUnit u 2 : Rˣ) : R) = quadraticMomentUnit ζ := by
  unfold indexedMomentUnit
  rw [zmodFive_units_univ]
  have hexpand :
      (∏ a ∈ ({1, zmodFiveUnitTwo, zmodFiveUnitThree,
          zmodFiveUnitFour} : Finset (ZMod 5)ˣ),
        u a ^ (((a : ZMod 5) ^ 2).val)) =
        u 1 * u zmodFiveUnitTwo ^ 4 *
          u zmodFiveUnitThree ^ 4 * u zmodFiveUnitFour := by
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_singleton]
    simp only [zmodFiveUnitOne_sq_val, zmodFiveUnitTwo_sq_val,
      zmodFiveUnitThree_sq_val, zmodFiveUnitFour_sq_val, pow_one]
    simp [mul_assoc]
  rw [hexpand]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  rw [hu, hu, hu, hu]
  simp only [zmodFiveUnitOne_val, zmodFiveUnitTwo_val,
    zmodFiveUnitThree_val, zmodFiveUnitFour_val]
  norm_num [zmodFiveUnitTwo, zmodFiveUnitThree, zmodFiveUnitFour]
  unfold quadraticMomentUnit
  ring

/-- **Kernel-checked Agrawal-to-golden moment interface at `r = 5`.**

Let `u a` be the four cyclotomic units indexed by
`a ∈ (ZMod 5)ˣ`.  If their weighted multiplicative product is the
quadratic moment unit `U₂`, then its abstract additive moment is three
times the quintic index of the coordinated golden unit.

The hypothesis `hU` is deliberately visible: the theorem certifies the
exact moment/product interface, while a caller must still identify its
particular local Agrawal logarithm family with the four cyclotomic units.
@isnad1 id=eq.4h6v.s10.ea378318d867 from=translated src=- shape=24a0fcc9 vocab=a09a6cce
-/
theorem agrawal_quadratic_moment_eq_three_golden_index
    {R : Type*} [CommRing R]
    {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (χ : Rˣ →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → Rˣ)
    (s ε : Rˣ)
    (hU :
      ((indexedMomentUnit u 2 : Rˣ) : R) = quadraticMomentUnit ζ)
    (hs : (s : R) = cyclotomicSqrtFive ζ)
    (hε : (ε : R) = cyclotomicGoldenUnit ζ) :
    moment (fun a : (ZMod 5)ˣ ↦ (χ (u a)).toAdd) 2 =
      3 * (χ ε).toAdd := by
  rw [← quintic_index_indexedMomentUnit_eq_moment χ u 2]
  exact golden_moment_index hζ χ (indexedMomentUnit u 2) s ε hU hs hε

/-- **End-to-end golden identity for the four local logarithms.**

Here the product-identification premise of
`agrawal_quadratic_moment_eq_three_golden_index` has been discharged:
the family is explicitly the four units `ζ^a - 1`.
@isnad1 id=eq.4h6v.s10.41be7e958c55 from=translated src=- shape=0af45589 vocab=0d161507
-/
theorem cyclotomic_quadratic_moment_eq_three_golden_index
    {R : Type*} [CommRing R]
    {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (χ : Rˣ →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → Rˣ)
    (s ε : Rˣ)
    (hu : ∀ a : (ZMod 5)ˣ,
      (u a : R) = ζ ^ ((a : ZMod 5).val) - 1)
    (hs : (s : R) = cyclotomicSqrtFive ζ)
    (hε : (ε : R) = cyclotomicGoldenUnit ζ) :
    moment (fun a : (ZMod 5)ˣ ↦ (χ (u a)).toAdd) 2 =
      3 * (χ ε).toAdd := by
  exact agrawal_quadratic_moment_eq_three_golden_index
    hζ χ u s ε
    (indexedMomentUnit_two_eq_quadraticMomentUnit u hu) hs hε

end AgrawalCore
