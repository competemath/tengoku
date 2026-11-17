/-
The exact row-to-moment interface at r = 5.

`GoldenMomentBridge.lean` identifies the weighted multiplicative product
with the additive quadratic moment.  This module closes the preceding
interface: applying one and the same quintic character to a local row

  u_a^m = u_{t a}

gives the covariance relation used by `MomentObstruction.lean`.

The concrete theorem starts from `LocalS5 p m` in
`(ZMod p)[X]/(Phi_5)`.  No generator of a cyclic group and no discrete
logarithm normalization is chosen.
-/
import Tengoku.AgrawalR5.AgrawalCore.GoldenMomentBridge
import Tengoku.AgrawalR5.AgrawalCore.LocalTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- Applying a quintic character to a multiplicative local row produces
the additive covariance relation directly.

The hypothesis `hm` coordinates the natural exponent `m` with its residue
`t` modulo five.  There is no independent choice of logarithm generator.
@isnad1 id=eq.2h6v.s10.78f494d75198 from=translated src=- shape=34a0b1fd vocab=7dd8bb8e
-/
theorem quintic_covariance_of_local_row
    {G : Type*} [CommGroup G]
    (χ : G →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → G) (m : ℕ) (t : (ZMod 5)ˣ)
    (hm : (m : ZMod 5) = (t : ZMod 5))
    (hrow : ∀ a : (ZMod 5)ˣ, u a ^ m = u (t * a)) :
    ∀ a : (ZMod 5)ˣ,
      (t : ZMod 5) * (χ (u a)).toAdd = (χ (u (t * a))).toAdd := by
  intro a
  rw [← hm, ← nsmul_eq_mul, ← toAdd_pow, ← map_pow, hrow]

/-- A local row therefore supplies exactly the covariance premise of the
finite Fourier moment theorem.
@isnad1 id=eq.2h6v.s10.72add98184a1 from=translated src=- shape=f0754242 vocab=9dcefd04
-/
theorem moment_covariance_of_local_row
    {G : Type*} [CommGroup G]
    (χ : G →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → G) (m : ℕ) (t : (ZMod 5)ˣ)
    (hm : (m : ZMod 5) = (t : ZMod 5))
    (hrow : ∀ a : (ZMod 5)ˣ, u a ^ m = u (t * a))
    (j : ℕ) :
    (t : ZMod 5) *
        moment (fun a : (ZMod 5)ˣ ↦ (χ (u a)).toAdd) j =
      ((t⁻¹ : (ZMod 5)ˣ) : ZMod 5) ^ j *
        moment (fun a : (ZMod 5)ˣ ↦ (χ (u a)).toAdd) j :=
  moment_covariance _ t j
    (quintic_covariance_of_local_row χ u m t hm hrow)

/-- End-to-end abstract obstruction from a multiplicative local row.
@isnad1 id=eq.2h6v.s10.6de0dc4f4b9b from=translated src=- shape=af8776c5 vocab=1ddc4056
-/
theorem moment_obstruction_of_local_row
    {G : Type*} [CommGroup G]
    (χ : G →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → G) (m : ℕ) (t : (ZMod 5)ˣ)
    (hm : (m : ZMod 5) = (t : ZMod 5))
    (hrow : ∀ a : (ZMod 5)ˣ, u a ^ m = u (t * a))
    (j : ℕ) :
    ((t : ZMod 5) ^ (j + 1) - 1) *
        moment (fun a : (ZMod 5)ˣ ↦ (χ (u a)).toAdd) j = 0 :=
  moment_obstruction _ t j
    (quintic_covariance_of_local_row χ u m t hm hrow)

variable {p : ℕ} [Fact p.Prime]

/-- Every unit-valued power of the universal fifth root is again a root
of `Phi_5`.  The unit hypothesis excludes the root `1`; cancellation in
the geometric-sum identity then gives the result without a case split.
@isnad1 id=eq.1h2v.s9.1f2e1717791d from=translated src=- shape=b5e210b6 vocab=9edcb3c7
-/
lemma phi5_aeval_zeta_power_of_isUnit (a : ℕ)
    (ha : IsUnit ((zeta5 : Phi5Ring p) ^ a - 1)) :
    Polynomial.aeval ((zeta5 : Phi5Ring p) ^ a) (phi5 p) = 0 := by
  let x : Phi5Ring p := (zeta5 : Phi5Ring p) ^ a
  have hax : IsUnit (x - 1) := by simpa [x] using ha
  have hpow : x ^ 5 = 1 := by
    dsimp [x]
    rw [← pow_mul, mul_comm a 5, pow_mul, zeta5_pow_five, one_pow]
  simp only [phi5, map_add, map_pow, map_one, Polynomial.aeval_X]
  change x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0
  apply hax.mul_left_cancel
  calc
    (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1)
        = x ^ 5 - 1 := by ring
    _ = 0 := sub_eq_zero.mpr hpow
    _ = (x - 1) * 0 := by ring

/-- For `p ≠ 5`, every one of the four canonical cyclotomic entries
`zeta^a - 1`, `a ∈ (ZMod 5)ˣ`, is a unit.

The proof uses the exact product of the four entries, which is `5`, and
therefore does not appeal to a field decomposition of the quotient ring.
@isnad1 id=isunit.1h2v.s7.088759406fc9 from=translated src=- shape=e35b5e59 vocab=2090bed4
-/
lemma zeta5_unit_power_sub_one_isUnit (hp5 : p ≠ 5)
    (a : (ZMod 5)ˣ) :
    IsUnit ((zeta5 : Phi5Ring p) ^ ((a : ZMod 5).val) - 1) := by
  let z : Phi5Ring p := zeta5
  let u1 := z - 1
  let u2 := z ^ 2 - 1
  let u3 := z ^ 3 - 1
  let u4 := z ^ 4 - 1
  have hprod : u1 * u2 * u3 * u4 = 5 := by
    simpa [u1, u2, u3, u4, z] using
      prod_pow_sub_one (R := Phi5Ring p) (ζ := zeta5)
        (zeta5_rel (p := p))
  have h5 : IsUnit (5 : Phi5Ring p) := by
    have hz : IsUnit (5 : ZMod p) := (five_ne_zero hp5).isUnit
    have hmap := hz.map (algebraMap (ZMod p) (Phi5Ring p))
    rwa [map_ofNat] at hmap
  have h1 : IsUnit u1 := by
    have h : u1 * (u2 * u3 * u4) = 5 := by
      calc
        u1 * (u2 * u3 * u4) = u1 * u2 * u3 * u4 := by ring
        _ = 5 := hprod
    exact isUnit_of_mul_isUnit_left (h ▸ h5)
  have h2 : IsUnit u2 := by
    have h : u2 * (u1 * u3 * u4) = 5 := by
      calc
        u2 * (u1 * u3 * u4) = u1 * u2 * u3 * u4 := by ring
        _ = 5 := hprod
    exact isUnit_of_mul_isUnit_left (h ▸ h5)
  have h3 : IsUnit u3 := by
    have h : u3 * (u1 * u2 * u4) = 5 := by
      calc
        u3 * (u1 * u2 * u4) = u1 * u2 * u3 * u4 := by ring
        _ = 5 := hprod
    exact isUnit_of_mul_isUnit_left (h ▸ h5)
  have h4 : IsUnit u4 := by
    have h : u4 * (u1 * u2 * u3) = 5 := by
      calc
        u4 * (u1 * u2 * u3) = u1 * u2 * u3 * u4 := by ring
        _ = 5 := hprod
    exact isUnit_of_mul_isUnit_left (h ▸ h5)
  have ha : a = 1 ∨ a = zmodFiveUnitTwo ∨
      a = zmodFiveUnitThree ∨ a = zmodFiveUnitFour := by
    have hm : a ∈
        ({1, zmodFiveUnitTwo, zmodFiveUnitThree,
          zmodFiveUnitFour} : Finset (ZMod 5)ˣ) := by
      rw [← zmodFive_units_univ]
      exact Finset.mem_univ a
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with rfl | rfl | rfl | rfl
  · rw [zmodFiveUnitOne_val, pow_one]
    simpa [u1, z] using h1
  · simpa [u2, z, zmodFiveUnitTwo_val] using h2
  · simpa [u3, z, zmodFiveUnitThree_val] using h3
  · simpa [u4, z, zmodFiveUnitFour_val] using h4

/-- The canonical unit lift of `zeta^a - 1`.-/
noncomputable def localCyclotomicUnit (hp5 : p ≠ 5)
    (a : (ZMod 5)ˣ) : (Phi5Ring p)ˣ :=
  (zeta5_unit_power_sub_one_isUnit hp5 a).unit

/--
@isnad1 id=eq.1h2v.s7.45379f5a6767 from=translated src=- shape=d68d5d80 vocab=3b3fab38
-/
@[simp] lemma localCyclotomicUnit_val (hp5 : p ≠ 5)
    (a : (ZMod 5)ˣ) :
    (localCyclotomicUnit hp5 a : Phi5Ring p) =
      zeta5 ^ ((a : ZMod 5).val) - 1 :=
  (zeta5_unit_power_sub_one_isUnit hp5 a).unit_spec

/-- The coordinated cyclotomic square root of five is a unit for `p ≠ 5`.
@isnad1 id=isunit.1h1v.s5.25b2b56b4c00 from=translated src=- shape=cd2bc50c vocab=0b8e97e6
-/
lemma cyclotomicSqrtFive_isUnit (hp5 : p ≠ 5) :
    IsUnit (cyclotomicSqrtFive (zeta5 : Phi5Ring p)) := by
  have hsq := cyclotomic_sqrtFive_sq (R := Phi5Ring p)
    (zeta5_rel (p := p))
  have h5 : IsUnit (5 : Phi5Ring p) := by
    have hz : IsUnit (5 : ZMod p) := (five_ne_zero hp5).isUnit
    have hmap := hz.map (algebraMap (ZMod p) (Phi5Ring p))
    rwa [map_ofNat] at hmap
  have hmul : IsUnit
      (cyclotomicSqrtFive (zeta5 : Phi5Ring p) *
        cyclotomicSqrtFive (zeta5 : Phi5Ring p)) := by
    rw [← pow_two, hsq]
    exact h5
  exact isUnit_of_mul_isUnit_left hmul

/-- The scalar five is a unit in the local cyclotomic ring for `p ≠ 5`.
@isnad1 id=isunit.1h1v.s5.ae689e4174a3 from=translated src=- shape=c59b7855 vocab=c362a49b
-/
lemma localFive_isUnit (hp5 : p ≠ 5) :
    IsUnit (5 : Phi5Ring p) := by
  have hz : IsUnit (5 : ZMod p) := (five_ne_zero hp5).isUnit
  have hmap := hz.map (algebraMap (ZMod p) (Phi5Ring p))
  rwa [map_ofNat] at hmap

/-- The canonical unit lift of the scalar five.-/
noncomputable def localFiveUnit (hp5 : p ≠ 5) : (Phi5Ring p)ˣ :=
  (localFive_isUnit hp5).unit

/--
@isnad1 id=eq.1h1v.s6.3cbc295e833e from=translated src=- shape=a7ccacd1 vocab=2b052891
-/
@[simp] lemma localFiveUnit_val (hp5 : p ≠ 5) :
    (localFiveUnit hp5 : Phi5Ring p) = 5 :=
  (localFive_isUnit hp5).unit_spec

/-- The canonical unit lift of the coordinated square root of five.-/
noncomputable def localSqrtFiveUnit (hp5 : p ≠ 5) : (Phi5Ring p)ˣ :=
  (cyclotomicSqrtFive_isUnit hp5).unit

/--
@isnad1 id=eq.1h1v.s5.f4473075f540 from=translated src=- shape=a75d6b97 vocab=96d305b1
-/
@[simp] lemma localSqrtFiveUnit_val (hp5 : p ≠ 5) :
    (localSqrtFiveUnit hp5 : Phi5Ring p) =
      cyclotomicSqrtFive zeta5 :=
  (cyclotomicSqrtFive_isUnit hp5).unit_spec

/-- The canonical unit lift of the coordinated golden unit.-/
noncomputable def localGoldenUnit : (Phi5Ring p)ˣ :=
  (cycloEps_isUnit (p := p)).unit

/--
@isnad1 id=eq.0h1v.s5.d7e0ad0d10d3 from=translated src=- shape=f99968bd vocab=e95bc906
-/
@[simp] lemma localGoldenUnit_val :
    (localGoldenUnit (p := p) : Phi5Ring p) =
      cyclotomicGoldenUnit zeta5 := by
  rw [show localGoldenUnit (p := p) =
      (cycloEps_isUnit (p := p)).unit by rfl]
  rw [IsUnit.unit_spec]
  rfl

/-- At weight zero, the product of the four canonical local cyclotomic
units is exactly the canonical lift of five.
@isnad1 id=eq.1h1v.s6.dbd9056a62fb from=translated src=- shape=1b50eaa4 vocab=2754eb30
-/
lemma indexedMomentUnit_zero_eq_localFiveUnit (hp5 : p ≠ 5) :
    indexedMomentUnit (localCyclotomicUnit hp5) 0 =
      localFiveUnit hp5 := by
  apply Units.ext
  change
    Units.coeHom (Phi5Ring p)
        (∏ a : (ZMod 5)ˣ,
          localCyclotomicUnit hp5 a ^
            (((a : ZMod 5) ^ 0).val)) =
      (localFiveUnit hp5 : Phi5Ring p)
  rw [map_prod]
  simp only [Units.coeHom_apply, pow_zero, ZMod.val_one, pow_one]
  rw [zmodFive_units_univ]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  simp only [localCyclotomicUnit_val, zmodFiveUnitOne_val,
    zmodFiveUnitTwo_val, zmodFiveUnitThree_val, zmodFiveUnitFour_val,
    localFiveUnit_val]
  simpa only [pow_one, mul_assoc] using
    prod_pow_sub_one (R := Phi5Ring p) (ζ := zeta5)
      (zeta5_rel (p := p))

/-- The literal local congruence `LocalS5 p m` gives the four
multiplicative rows on any chosen unit lifts of `zeta^a - 1`.

This is the formal bridge from the quotient-ring row to the row family
used by the character and moment theorems.
@isnad1 id=eq.3h5v.s9.3e225490d4ad from=translated src=- shape=d23e13cf vocab=0e381ea5
-/
theorem localS5_unit_rows {m : ℕ} (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (u : (ZMod 5)ˣ → (Phi5Ring p)ˣ)
    (hu : ∀ a : (ZMod 5)ˣ,
      (u a : Phi5Ring p) = zeta5 ^ ((a : ZMod 5).val) - 1) :
    ∀ a : (ZMod 5)ˣ, u a ^ m = u (t * a) := by
  intro a
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  rw [hu, hu]
  have haunit : IsUnit
      ((zeta5 : Phi5Ring p) ^ ((a : ZMod 5).val) - 1) := by
    simpa [hu a] using (u a).isUnit
  have hrow := localS5_row (p := p) hlocal
    (phi5_aeval_zeta_power_of_isUnit ((a : ZMod 5).val) haunit)
  calc
    (zeta5 ^ (a : ZMod 5).val - 1) ^ m
        = zeta5 ^ ((a : ZMod 5).val * m) - 1 := hrow
    _ = zeta5 ^ (((t * a : (ZMod 5)ˣ) : ZMod 5).val) - 1 := by
      rw [zeta5_pow_mod, zeta5_pow_mod]
      have hmval : m % 5 = (t : ZMod 5).val := by
        simpa [ZMod.val_natCast] using congrArg ZMod.val hm
      have hmod :
          ((a : ZMod 5).val * m) % 5 =
            (((t * a : (ZMod 5)ˣ) : ZMod 5).val) := by
        change
          ((a : ZMod 5).val * m) % 5 =
            ((t : ZMod 5) * (a : ZMod 5)).val
        rw [ZMod.val_mul]
        calc
          ((a : ZMod 5).val * m) % 5 =
              (((a : ZMod 5).val % 5) * (m % 5)) % 5 :=
            Nat.mul_mod _ _ _
          _ = ((a : ZMod 5).val * (m % 5)) % 5 := by
            rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
          _ = ((a : ZMod 5).val * (t : ZMod 5).val) % 5 := by
            rw [hmval]
          _ = ((t : ZMod 5).val * (a : ZMod 5).val) % 5 := by
            rw [Nat.mul_comm]
      rw [hmod, Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- The concrete local congruence supplies quintic covariance, with the
same character on both sides.
@isnad1 id=eq.3h6v.s10.6b58a523d8d9 from=translated src=- shape=67500215 vocab=37c0d413
-/
theorem localS5_quintic_covariance {m : ℕ} (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → (Phi5Ring p)ˣ)
    (hu : ∀ a : (ZMod 5)ˣ,
      (u a : Phi5Ring p) = zeta5 ^ ((a : ZMod 5).val) - 1) :
    ∀ a : (ZMod 5)ˣ,
      (t : ZMod 5) * (χ (u a)).toAdd = (χ (u (t * a))).toAdd :=
  quintic_covariance_of_local_row χ u m t hm
    (localS5_unit_rows hlocal t hm u hu)

/-- **Concrete local-row-to-golden obstruction at `r = 5`.**

Starting from `LocalS5 p m`, this theorem:

1. evaluates the local congruence at all four primitive fifth roots;
2. applies a single quintic character to obtain covariance;
3. forms the quadratic moment;
4. identifies it with three times the golden-unit index.

Thus the displayed conclusion has no hidden generator-normalization
interface.
@isnad1 id=eq.5h7v.s10.11d78517a8ed from=translated src=- shape=bff55cd0 vocab=c4bcea5e
-/
theorem localS5_golden_moment_obstruction {m : ℕ}
    (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → (Phi5Ring p)ˣ)
    (s ε : (Phi5Ring p)ˣ)
    (hu : ∀ a : (ZMod 5)ˣ,
      (u a : Phi5Ring p) = zeta5 ^ ((a : ZMod 5).val) - 1)
    (hs : (s : Phi5Ring p) = cyclotomicSqrtFive zeta5)
    (hε : (ε : Phi5Ring p) = cyclotomicGoldenUnit zeta5) :
    ((t : ZMod 5) ^ 3 - 1) * (3 * (χ ε).toAdd) = 0 := by
  have hrows := localS5_unit_rows hlocal t hm u hu
  have hobs := moment_obstruction_of_local_row χ u m t hm hrows 2
  have hgold := cyclotomic_quadratic_moment_eq_three_golden_index
    (zeta5_rel (p := p)) χ u s ε hu hs hε
  rw [hgold] at hobs
  norm_num at hobs ⊢
  exact hobs

/-- If the golden quintic index is nonzero, the concrete local row forces
the order-three residue constraint `t^3 = 1`.
@isnad1 id=eq.6h7v.s10.df38b8f7ed9c from=translated src=- shape=b742a420 vocab=9264b090
-/
theorem localS5_golden_order_constraint {m : ℕ}
    (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (u : (ZMod 5)ˣ → (Phi5Ring p)ˣ)
    (s ε : (Phi5Ring p)ˣ)
    (hu : ∀ a : (ZMod 5)ˣ,
      (u a : Phi5Ring p) = zeta5 ^ ((a : ZMod 5).val) - 1)
    (hs : (s : Phi5Ring p) = cyclotomicSqrtFive zeta5)
    (hε : (ε : Phi5Ring p) = cyclotomicGoldenUnit zeta5)
    (hχ : (χ ε).toAdd ≠ 0) :
    (t : ZMod 5) ^ 3 = 1 := by
  have hobs := localS5_golden_moment_obstruction
    hlocal t hm χ u s ε hu hs hε
  have hthree : (3 : ZMod 5) ≠ 0 := by decide
  have hne : 3 * (χ ε).toAdd ≠ 0 := mul_ne_zero hthree hχ
  exact sub_eq_zero.mp ((mul_eq_zero.mp hobs).resolve_right hne)

/-- **Canonical end-to-end local-to-golden obstruction at `r = 5`.**

Unlike `localS5_golden_moment_obstruction`, this corollary constructs all
cyclotomic and golden units internally. Its only mathematical inputs are the
literal local row, `p ≠ 5`, the residue coordinate, and one quintic
character.
@isnad1 id=eq.3h4v.s10.bfd0b6e90f6b from=translated src=- shape=d68bc76d vocab=fedac77c
-/
theorem localS5_canonical_golden_moment_obstruction {m : ℕ}
    (hp5 : p ≠ 5) (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5)) :
    ((t : ZMod 5) ^ 3 - 1) *
      (3 * (χ (localGoldenUnit (p := p))).toAdd) = 0 :=
  localS5_golden_moment_obstruction hlocal t hm χ
    (localCyclotomicUnit hp5) (localSqrtFiveUnit hp5)
    (localGoldenUnit (p := p))
    (localCyclotomicUnit_val hp5)
    (localSqrtFiveUnit_val hp5)
    (localGoldenUnit_val (p := p))

/-- Canonical residue-order constraint, with no user-supplied unit lifts.
@isnad1 id=eq.4h4v.s9.a581f580aa78 from=translated src=- shape=33556ffb vocab=f9f77691
-/
theorem localS5_canonical_golden_order_constraint {m : ℕ}
    (hp5 : p ≠ 5) (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (hχ : (χ (localGoldenUnit (p := p))).toAdd ≠ 0) :
    (t : ZMod 5) ^ 3 = 1 :=
  localS5_golden_order_constraint hlocal t hm χ
    (localCyclotomicUnit hp5) (localSqrtFiveUnit hp5)
    (localGoldenUnit (p := p))
    (localCyclotomicUnit_val hp5)
    (localSqrtFiveUnit_val hp5)
    (localGoldenUnit_val (p := p)) hχ

/-- The only unit of `ZMod 5` whose cube is one is one itself.
@isnad1 id=eq.1h1v.s8.b81db27423ee from=translated src=- shape=f914d108 vocab=13cfd96a
-/
lemma zmodFiveUnit_eq_one_of_cube_eq_one (t : (ZMod 5)ˣ)
    (ht : (t : ZMod 5) ^ 3 = 1) :
    t = 1 := by
  have hm : t ∈
      ({1, zmodFiveUnitTwo, zmodFiveUnitThree,
        zmodFiveUnitFour} : Finset (ZMod 5)ˣ) := by
    rw [← zmodFive_units_univ]
    exact Finset.mem_univ t
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rfl
  · exact False.elim ((by decide :
      ((zmodFiveUnitTwo : ZMod 5) ^ 3 ≠ 1)) ht)
  · exact False.elim ((by decide :
      ((zmodFiveUnitThree : ZMod 5) ^ 3 ≠ 1)) ht)
  · exact False.elim ((by decide :
      ((zmodFiveUnitFour : ZMod 5) ^ 3 ≠ 1)) ht)

/-- Direct form of the golden lock: a nontrivial residue coordinate forces
the golden quintic index to vanish.
@isnad1 id=eq.4h4v.s9.363d78ae50f0 from=translated src=- shape=aedd1e00 vocab=1557dddc
-/
theorem localS5_canonical_golden_index_zero_of_ne_one {m : ℕ}
    (hp5 : p ≠ 5) (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (ht : t ≠ 1) :
    (χ (localGoldenUnit (p := p))).toAdd = 0 := by
  by_contra hχ
  exact ht (zmodFiveUnit_eq_one_of_cube_eq_one t
    (localS5_canonical_golden_order_constraint hp5 hlocal t hm χ hχ))

/-- The zeroth local moment is the quintic index of the scalar five.
@isnad1 id=eq.3h4v.s9.750fc8d7f4e9 from=translated src=- shape=403407cc vocab=d7126e9e
-/
theorem localS5_canonical_five_moment_obstruction {m : ℕ}
    (hp5 : p ≠ 5) (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5)) :
    ((t : ZMod 5) - 1) * (χ (localFiveUnit hp5)).toAdd = 0 := by
  have hrows := localS5_unit_rows hlocal t hm
    (localCyclotomicUnit hp5) (localCyclotomicUnit_val hp5)
  have hobs := moment_obstruction_of_local_row χ
    (localCyclotomicUnit hp5) m t hm hrows 0
  rw [← quintic_index_indexedMomentUnit_eq_moment] at hobs
  rw [indexedMomentUnit_zero_eq_localFiveUnit hp5] at hobs
  simpa using hobs

/-- Direct form of the scalar-five lock.
@isnad1 id=eq.4h4v.s9.736c57c0c2a3 from=translated src=- shape=0578feb1 vocab=3a7ae70a
-/
theorem localS5_canonical_five_index_zero_of_ne_one {m : ℕ}
    (hp5 : p ≠ 5) (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (ht : t ≠ 1) :
    (χ (localFiveUnit hp5)).toAdd = 0 := by
  have hobs :=
    localS5_canonical_five_moment_obstruction hp5 hlocal t hm χ
  have htval : (t : ZMod 5) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact ht (Units.ext h)
  exact (mul_eq_zero.mp hobs).resolve_left htval

/-- **Canonical two-lock consequence of a nontrivial local class.**

With one and the same quintic character, the literal `LocalS5` row forces
both the scalar-five and golden-unit indices to vanish.
@isnad1 id=and.4h4v.s10.2be48c44555b from=translated src=- shape=5daa43ac vocab=f82a5e84
-/
theorem localS5_canonical_quintic_locks_of_ne_one {m : ℕ}
    (hp5 : p ≠ 5) (hlocal : LocalS5 p m)
    (t : (ZMod 5)ˣ) (hm : (m : ZMod 5) = (t : ZMod 5))
    (χ : (Phi5Ring p)ˣ →* Multiplicative (ZMod 5))
    (ht : t ≠ 1) :
    (χ (localFiveUnit hp5)).toAdd = 0 ∧
      (χ (localGoldenUnit (p := p))).toAdd = 0 :=
  ⟨localS5_canonical_five_index_zero_of_ne_one hp5 hlocal t hm χ ht,
    localS5_canonical_golden_index_zero_of_ne_one hp5 hlocal t hm χ ht⟩

end AgrawalCore
