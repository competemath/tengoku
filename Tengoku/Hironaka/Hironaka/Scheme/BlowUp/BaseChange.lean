/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Scheme.BlowUp.AffineAlgebra
public import Tengoku.Seed.RingTheory.Flat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of the affine blow-up algebra

For a ring map `R → S`, `J = IS` and `b` the image of `a`, the induced map `R[I/a] → S[J/b]`
and the `S`-algebra map `S ⊗[R] R[I/a] → S[J/b]`, which is surjective with kernel the `b`-power
torsion [Sta, Tag 0BIP], and is an isomorphism when `S` is flat over `R` (the ring-level form of
the compatibility of blow-ups with flat base change [Sta, Tag 0805]: flatness preserves the
injectivity of multiplication by `a`).

## Main declarations

* `AlgebraicGeometry.awayMapₐ S a : Localization.Away a →ₐ[R] Localization.Away (algebraMap R S a)`,
  the map of localizations induced by `R → S`.
* `affineBlowUpAlgebra.baseChangeHom I a S : R[I/a] →ₐ[R] S[IS/b]` with `baseChangeHom_frac`
  and `baseChangeHom_unique`.
* `affineBlowUpAlgebra.tensorHom I a S : S ⊗[R] R[I/a] →ₐ[S] S[IS/b]` with `tensorHom_tmul_frac`,
  `tensorHom_unique`, `tensorHom_surjective`, `tensorHom_apply_eq_zero_iff` and
  `tensorHom_bijective_of_flat`.

## The arguments

*The induced map.*  `R_a → S_b` sends `x/a` to `(image of x)/b`, so it maps the generators of
`R[I/a]` into `S[J/b]`.

*Surjectivity.*  `S[J/b]` is generated over `S` by the `y/b`, `y ∈ J = IS`, and
`y = ∑ sᵢ (image of xᵢ)` gives `y/b = ∑ sᵢ · (image of xᵢ)/b`, the image of `∑ sᵢ ⊗ xᵢ/a`.

*Kernel.*  Every element `w` of `S ⊗[R] R[I/a]` satisfies `bⁿ w = p ⊗ 1` for some `n` and
`p ∈ S`: for a pure tensor `s ⊗ z` with `z aⁿ = r` in `R_a` (`z ∈ R[I/a] ⊆ R_a`) one has
`bⁿ (s ⊗ z) = s ⊗ aⁿ z = s ⊗ r = (image of r) s ⊗ 1`, and the property is additive.  If `w` maps
to `0` then `p` maps to `0` in `S_b`, so `bᵏ p = 0` and `bⁿ⁺ᵏ w = 0`.  Conversely `b` is a
nonzerodivisor of `S[J/b]` (`affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors`), so `b`-power
torsion maps to `0`.  The Stacks Project proves the kernel statement by constructing the inverse
map on `S[J/b]`; the common-denominator computation above is the same identity
`bⁿ (s ⊗ x/aⁿ) = s x ⊗ 1` read forwards.

*Flat case.*  If `S` is flat over `R`, multiplication by `a` on `R[I/a]` (injective) stays
injective after `S ⊗[R] -`, and it is multiplication by `b` on the tensor product; so the
`b`-power torsion vanishes and the surjection is bijective.

## Conventions

No hypothesis `a ∈ I` is needed ([Sta, Tag 0BIP] assumes it; it is not used here).  The
`b`-power torsion of the `S`-module `S ⊗[R] R[I/a]` is written `∃ k, bᵏ • w = 0`.

## Boundary cases

`S = 0`: both sides are the zero ring.  `a = 0`: `S[J/0]` is the zero ring and every `w` is
`0`-power torsion (`0¹ • w = 0`), consistently.
-/

@[expose] public section

universe u v

open TensorProduct

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a : R)

/-- The map `R_a → S_b` induced by `R → S` on localizations, as an `R`-algebra map.-/
noncomputable def awayMapₐ : Localization.Away a →ₐ[R] Localization.Away (algebraMap R S a) :=
  IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R (Localization.Away (algebraMap R S a)))
    (by
      rw [Algebra.ofId_apply,
        IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S a))]
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem awayMapₐ_algebraMap (r : R) :
    awayMapₐ S a (algebraMap R (Localization.Away a) r) =
      algebraMap S (Localization.Away (algebraMap R S a)) (algebraMap R S r) := by
  rw [awayMapₐ, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    ← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S a))]
  rfl

theorem awayMapₐ_invSelf :
    awayMapₐ S a (IsLocalization.Away.invSelf a) =
      IsLocalization.Away.invSelf (algebraMap R S a) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (algebraMap R S a)) (algebraMap R S a)
  have h1 : awayMapₐ S a (IsLocalization.Away.invSelf a) *
      algebraMap S (Localization.Away (algebraMap R S a)) (algebraMap R S a) = 1 := by
    rw [← awayMapₐ_algebraMap, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have h2 : IsLocalization.Away.invSelf (algebraMap R S a) *
      algebraMap S (Localization.Away (algebraMap R S a)) (algebraMap R S a) = 1 := by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]
  exact hu.mul_left_injective (h1.trans h2.symm)

namespace affineBlowUpAlgebra

variable (I : Ideal R)

theorem awayMapₐ_mem (z : affineBlowUpAlgebra I a) :
    awayMapₐ S a z ∈ affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a) := by
  obtain ⟨z, hz⟩ := z
  induction hz using induction_on with
  | mem x hx =>
    change awayMapₐ S a (algebraMap R (Localization.Away a) x * IsLocalization.Away.invSelf a) ∈ _
    rw [map_mul, awayMapₐ_algebraMap, awayMapₐ_invSelf]
    exact mul_invSelf_mem (Ideal.mem_map_of_mem _ hx)
  | algebraMap r =>
    change awayMapₐ S a (algebraMap R (Localization.Away a) r) ∈ _
    rw [awayMapₐ_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz =>
    change awayMapₐ S a (y + z) ∈ _
    rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz =>
    change awayMapₐ S a (y * z) ∈ _
    rw [map_mul]; exact mul_mem hy hz

/-- The induced map `R[I/a] → S[IS/b]`, `x/a ↦ (image of x)/b` [Sta, Tag 0BIP].-/
noncomputable def baseChangeHom :
    affineBlowUpAlgebra I a →ₐ[R] affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a)
    where
  toFun z := ⟨awayMapₐ S a z, awayMapₐ_mem S a I z⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by
    change awayMapₐ S a (algebraMap R (Localization.Away a) r) = _
    rw [awayMapₐ_algebraMap, ← IsScalarTower.algebraMap_apply]
    rfl)

@[simp]
theorem coe_baseChangeHom (z : affineBlowUpAlgebra I a) :
    (baseChangeHom S a I z : Localization.Away (algebraMap R S a)) = awayMapₐ S a z :=
  rfl

theorem baseChangeHom_frac {x : R} (hx : x ∈ I) :
    baseChangeHom S a I (frac hx) = frac (Ideal.mem_map_of_mem (algebraMap R S) hx) := by
  apply Subtype.ext
  change awayMapₐ S a (algebraMap R (Localization.Away a) x * IsLocalization.Away.invSelf a) = _
  rw [map_mul, awayMapₐ_algebraMap, awayMapₐ_invSelf]
  rfl

/-- The induced map is the unique `R`-algebra map with `x/a ↦ (image of x)/b`.-/
theorem baseChangeHom_unique
    (ψ : affineBlowUpAlgebra I a →ₐ[R]
      affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a))
    (hψ : ∀ x (hx : x ∈ I), ψ (frac hx) = frac (Ideal.mem_map_of_mem (algebraMap R S) hx)) :
    ψ = baseChangeHom S a I :=
  algHom_ext fun x hx => by rw [hψ x hx, baseChangeHom_frac]

/-- The `S`-algebra map `S ⊗[R] R[I/a] → S[IS/b]` [Sta, Tag 0BIP].-/
noncomputable def tensorHom :
    S ⊗[R] affineBlowUpAlgebra I a →ₐ[S]
      affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (baseChangeHom S a I) fun _ _ => Commute.all _ _

@[simp]
theorem tensorHom_tmul (s : S) (z : affineBlowUpAlgebra I a) :
    tensorHom S a I (s ⊗ₜ z) = algebraMap S _ s * baseChangeHom S a I z := by
  rw [tensorHom, Algebra.TensorProduct.lift_tmul]
  rfl

end affineBlowUpAlgebra

end AlgebraicGeometry
