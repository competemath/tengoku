/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.GaloisCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Root characters for Kummer theory

Support API for root-quotient constructions in concrete Kummer extensions.
-/

namespace KummerTheory

open groupCohomology

section RootQuotientPrelim

variable {L : Type*} [Field L]

/-- Two unit roots with the same `n`-th power differ by an `n`-th root of unity.
@isnad1 id=eq.1h4v.s8.2a556a731816 from=translated src=- shape=69a907a7 vocab=70f3b9e8
-/
theorem div_pow_eq_one_of_pow_eq_pow
    {n : ℕ} {u v : Lˣ} (h : u ^ n = v ^ n) :
    (u / v) ^ n = 1 := by
  rw [div_pow, h]
  exact div_self' (v ^ n)

end RootQuotientPrelim

section TorsionSubgroups

variable (L : Type*) [Field L]

/-- The subgroup of units whose `n`-th power is `1`.-/
def nthRootsSubgroup (n : ℕ) : Subgroup Lˣ where
  carrier := {u | u ^ n = 1}
  one_mem' := one_pow n
  mul_mem' := by
    intro u v hu hv
    change (u * v) ^ n = 1
    rw [mul_pow, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change u⁻¹ ^ n = 1
    rw [inv_pow, hu, inv_one]

/-- Membership in the roots subgroup is equivalent to satisfying the `n`th-root equation.
@isnad1 id=iff.0h3v.s7.eedb3645291d from=translated src=- shape=af5c13f0 vocab=382a1db8
-/
@[simp] theorem mem_nthRootsSubgroup_iff {n : ℕ} {u : Lˣ} :
    u ∈ nthRootsSubgroup L n ↔ u ^ n = 1 :=
  Iff.rfl

end TorsionSubgroups

section RootQuotients

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The basic root-quotient attached to a unit `β` and a Galois automorphism `σ`.-/
def rootQuotient (β : Lˣ) (σ : Gal(L/K)) : Lˣ :=
  σ • β / β

/-- The root-quotient attached to the identity automorphism is trivial.
@isnad1 id=eq.0h3v.s8.647058f2b44d from=translated src=- shape=6a9e16b2 vocab=121b011e
-/
@[simp] theorem rootQuotient_one (β : Lˣ) :
    rootQuotient (K := K) (L := L) β 1 = 1 := by
  simp [rootQuotient]

/-- Multiplying the root-quotient by the chosen root recovers its Galois transform.
@isnad1 id=eq.0h4v.s9.84f5fc44f0a6 from=translated src=- shape=8b2fb565 vocab=ca266e7e
-/
@[simp] theorem rootQuotient_mul_right (β : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ * β = σ • β := by
  simp [rootQuotient]

/-- Base-field units have trivial root-quotient.
@isnad1 id=eq.0h4v.s8.ab44db380505 from=translated src=- shape=f4664864 vocab=82943e7f
-/
@[simp] theorem rootQuotient_algebraMap_unit (u : Kˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (Units.map (algebraMap K L).toMonoidHom u) σ = 1 := by
  unfold rootQuotient
  have hfixed : σ • Units.map (algebraMap K L).toMonoidHom u =
      Units.map (algebraMap K L).toMonoidHom u := by
    apply Units.ext
    exact σ.commutes (u : K)
  rw [hfixed, div_self']

/-- The root-quotient attached to a product is the product of the root-quotients.
@isnad1 id=eq.0h5v.s7.2d7f2abbcd9a from=translated src=- shape=e0ee5ba7 vocab=ef4fe4ce
-/
theorem rootQuotient_mul_root (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (u * v) σ =
      rootQuotient (K := K) (L := L) u σ *
        rootQuotient (K := K) (L := L) v σ := by
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The root-quotient is trivial exactly when the chosen root is fixed by `σ`.
@isnad1 id=iff.0h4v.s9.7dc7d28a301c from=translated src=- shape=1dd18141 vocab=5ad90423
-/
theorem rootQuotient_eq_one_iff (β : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ = 1 ↔ σ • β = β := by
  unfold rootQuotient
  exact div_eq_one

/-- The root-quotient construction satisfies the multiplicative cocycle identity.
@isnad1 id=eq.0h5v.s9.c7cdf5ed5082 from=translated src=- shape=68ed2ad9 vocab=ca266e7e
-/
theorem rootQuotient_mul (β : Lˣ) (σ τ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β (σ * τ) =
      σ • rootQuotient (K := K) (L := L) β τ *
        rootQuotient (K := K) (L := L) β σ := by
  rw [rootQuotient]
  rw [mul_smul]
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The root-quotient of a quotient is the quotient of the root-quotients.
@isnad1 id=eq.0h5v.s7.aae459c17b14 from=translated src=- shape=e0ee5ba7 vocab=50b71b8a
-/
theorem rootQuotient_div (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (u / v) σ =
      rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ := by
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Changing the chosen root changes the corresponding quotient cocycle by a coboundary.
@isnad1 id=eq.0h5v.s7.512d64a1e260 from=translated src=- shape=8f275fb3 vocab=50b71b8a
-/
theorem rootQuotient_changeRoot (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ =
      rootQuotient (K := K) (L := L) (u / v) σ := by
  exact (rootQuotient_div (K := K) (L := L) u v σ).symm

/-- If `β ^ n` is fixed by Galois, then `σ(β) / β` is `n`-torsion.
@isnad1 id=eq.1h5v.s9.f802618adcee from=translated src=- shape=e6ef4755 vocab=0b42598b
-/
theorem rootQuotient_pow_eq_one_of_pow_fixed
    {n : ℕ} {β : Lˣ} (hβ : ∀ σ : Gal(L/K), σ • (β ^ n) = β ^ n)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ ^ n = 1 := by
  unfold rootQuotient
  apply div_pow_eq_one_of_pow_eq_pow
  exact (map_pow (MulDistribMulAction.toMonoidHom Lˣ σ) β n).symm.trans (hβ σ)

end RootQuotients

section RadicalData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/--
A radical datum of exponent `n` consists of a subgroup of `Kˣ` together with a chosen
`n`-th root in `Lˣ` for each of its elements.-/
structure RadicalDatum (n : ℕ+) where
  /-- The subgroup of base-field units for which roots are chosen.-/
  carrier : Subgroup Kˣ
  /-- A chosen `n`-th root in `Lˣ` for each unit in `carrier`.-/
  root : carrier → Lˣ
  /-- Each chosen root has `n`-th power equal to the image of its base-field unit in `Lˣ`.-/
  root_pow_eq : ∀ a : carrier,
    root a ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1

namespace RadicalDatum

variable {n : ℕ+} (D : RadicalDatum (K := K) (L := L) n)

/-- The chosen root witness has the prescribed `n`-th power.
@isnad1 id=eq.0h5v.s9.27c7fb2053d2 from=translated src=- shape=5981fa86 vocab=c20e3b8d
-/
@[simp] theorem root_pow_eq_map (a : D.carrier) :
    D.root a ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1 :=
  D.root_pow_eq a

/-- Two `n`-th roots of the same radical element differ by an `n`-th root of unity.
@isnad1 id=eq.2h7v.s10.99ea6d389a9f from=translated src=- shape=ef232927 vocab=93c69e83
-/
theorem div_pow_eq_one_of_same_image
    {u v : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (hv : v ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1) :
    (u / v) ^ (n : ℕ) = 1 := by
  exact div_pow_eq_one_of_pow_eq_pow (n := (n : ℕ)) (hu.trans hv.symm)

/-- The root-quotient map `σ ↦ σ(β) / β` attached to the chosen root witness of `a`.-/
def rootCocycle (a : D.carrier) (σ : Gal(L/K)) : Lˣ :=
  rootQuotient (K := K) (L := L) (D.root a) σ

/-- The chosen root-quotient is trivial at the identity automorphism.
@isnad1 id=eq.0h5v.s8.66be41a66588 from=translated src=- shape=0b4b5926 vocab=a1ef6b1f
-/
@[simp] theorem rootCocycle_one (a : D.carrier) :
    D.rootCocycle a 1 = 1 := by
  simp [rootCocycle]

/-- The chosen root-quotient satisfies the multiplicative cocycle identity.
@isnad1 id=eq.0h7v.s9.02102608f3fc from=translated src=- shape=56e0decd vocab=01e1797d
-/
theorem rootCocycle_mul (a : D.carrier) (σ τ : Gal(L/K)) :
    D.rootCocycle a (σ * τ) =
      σ • D.rootCocycle a τ * D.rootCocycle a σ := by
  exact rootQuotient_mul (K := K) (L := L) (D.root a) σ τ

/-- Galois automorphisms fix units coming from the base field.
@isnad1 id=eq.0h4v.s9.3b3cf1b381bf from=translated src=- shape=b8d6b497 vocab=903e73ec
-/
@[simp] theorem smul_algebraMap_unit (σ : Gal(L/K)) (u : Kˣ) :
    σ • Units.map (algebraMap K L).toMonoidHom u =
      Units.map (algebraMap K L).toMonoidHom u := by
  apply Units.ext
  exact σ.commutes (u : K)

/-- The chosen root-quotient of `a` lands in the `n`-torsion subgroup of `Lˣ`.
@isnad1 id=eq.0h6v.s8.27913241491a from=translated src=- shape=51023823 vocab=ca14b26c
-/
theorem rootCocycle_pow_eq_one (a : D.carrier) (σ : Gal(L/K)) :
    D.rootCocycle a σ ^ (n : ℕ) = 1 := by
  refine rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := L)
      (β := D.root a) ?_ σ
  intro τ
  rw [D.root_pow_eq_map]
  exact smul_algebraMap_unit (K := K) (L := L) τ a.1

/-- If `μₙ(L)` is fixed by Galois, root-quotients for the same radical element agree.
@isnad1 id=eq.2h7v.s10.5f9bdeff9c69 from=translated src=- shape=fe7da3fc vocab=3a0f310f
-/
theorem rootQuotient_eq_rootCocycle_of_same_pow
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {u : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ = D.rootCocycle a σ := by
  have hpow : (u / D.root a) ^ (n : ℕ) = 1 := by
    exact D.div_pow_eq_one_of_same_image a hu (D.root_pow_eq_map a)
  have hfixed_delta : σ • (u / D.root a) = u / D.root a :=
    hfixed σ (u / D.root a) hpow
  have hquot_one : rootQuotient (K := K) (L := L) (u / D.root a) σ = 1 :=
    (rootQuotient_eq_one_iff (K := K) (L := L) (u / D.root a) σ).2 hfixed_delta
  have hdiv_one : rootQuotient (K := K) (L := L) u σ / D.rootCocycle a σ = 1 := by
    rw [rootCocycle, rootQuotient_changeRoot]
    exact hquot_one
  exact div_eq_one.mp hdiv_one

/-- If `μₙ(L)` is fixed by Galois, the chosen root-quotient is a character.-/
def rootCharacter (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Gal(L/K) →* Lˣ where
  toFun := D.rootCocycle a
  map_one' := by
    exact D.rootCocycle_one a
  map_mul' := by
    intro σ τ
    rw [D.rootCocycle_mul]
    rw [hfixed σ (D.rootCocycle a τ) (D.rootCocycle_pow_eq_one a τ)]
    exact mul_comm _ _

/-- The Kummer root character evaluates as the Galois translate divided by the chosen root.
@isnad1 id=eq.1h6v.s10.7dcf5c1f2ef5 from=translated src=- shape=55f8aad3 vocab=a2a28f3f
-/
@[simp] theorem rootCharacter_apply (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ = D.rootCocycle a σ :=
  rfl

/-- The canonical character agrees with any root quotient having the same `n`-th power.
@isnad1 id=eq.2h7v.s10.78ba94524170 from=translated src=- shape=bb192e27 vocab=93eef74b
-/
theorem rootCharacter_eq_of_same_pow
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {u : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ = D.rootCharacter a hfixed σ := by
  rw [D.rootCharacter_apply]
  exact D.rootQuotient_eq_rootCocycle_of_same_pow hfixed a hu σ

/-- The character obtained from a chosen root still takes values in `μₙ(L)`.
@isnad1 id=eq.1h6v.s10.ffa4a94a8a4d from=translated src=- shape=3d9b6196 vocab=dd755ecf
-/
theorem rootCharacter_pow_eq_one (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ ^ (n : ℕ) = 1 := by
  rw [D.rootCharacter_apply]
  exact D.rootCocycle_pow_eq_one a σ

/-- The character obtained from a chosen root lands in `μₙ(L)`.
@isnad1 id=mem.1h6v.s10.daccde7c641a from=translated src=- shape=2286f073 vocab=fe747281
-/
theorem rootCharacter_mem_nthRootsSubgroup (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ ∈ nthRootsSubgroup L (n : ℕ) := by
  rw [mem_nthRootsSubgroup_iff]
  exact D.rootCharacter_pow_eq_one a hfixed σ

end RadicalDatum
end RadicalData

end KummerTheory
