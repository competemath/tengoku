/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Algebra.Group.Subgroup.Even
import Tengoku.Seed.GroupTheory.Index
import Tengoku.Seed.GroupTheory.Torsion
import Tengoku.Seed.RingTheory.ClassGroup.Basic
import Tengoku.QuadraticNumberFields.QNFMathlib.RingTheory.ClassGroup.Narrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Torsion in Class Groups

This file defines power-torsion subgroups and square quotients for commutative
groups, together with their maps under homomorphisms and equivalences. The final
sections specialize the torsion results to ordinary and narrow ideal class groups.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
namespace CommGroup

variable (G : Type*) [CommGroup G]

/-- The quotient of a commutative group by its subgroup of squares.-/
abbrev squareQuotient := G ⧸ Subgroup.square G

end CommGroup

namespace Subgroup
variable (G) (n : ℕ)
variable [CommGroup G]

/-- Deprecated alias for `CommGroup.squareQuotient`.-/
@[deprecated CommGroup.squareQuotient (since := "2026-07-12")]
abbrev squareQuotient := CommGroup.squareQuotient G

/-- The subgroup of elements killed by the `n`th-power map in a multiplicative
group. This is the multiplicative-group analogue of `AddSubgroup.torsionBy`.-/
noncomputable abbrev powTorsion : Subgroup G :=
  MonoidHom.ker (powMonoidHom (α := G) n)

/-- Membership in the subgroup killed by the `n`th-power map.
@isnad1 id=iff.0h3v.s6.e5f7410e4c64 from=translated src=- shape=86309c43 vocab=85aa47e3
-/
theorem mem_powTorsion_iff (x : G) :
    x ∈ powTorsion G n ↔ x ^ n = 1 :=
  Iff.rfl

/-- The two-torsion subgroup of a multiplicative commutative group.-/
noncomputable abbrev twoTorsion : Subgroup G :=
  powTorsion G 2

variable {G}

/-- Membership in the two-torsion subgroup.
@isnad1 id=iff.0h2v.s6.ea48fda71ad6 from=translated src=- shape=77871553 vocab=6c457a48
-/
theorem mem_twoTorsion_iff (x : G) :
    x ∈ twoTorsion G ↔ x ^ 2 = 1 :=
  mem_powTorsion_iff G 2 x

/-- Membership in the square subgroup.
@isnad1 id=iff.0h2v.s5.1bdc2072f795 from=translated src=- shape=246ccc88 vocab=2674b679
-/
theorem mem_square_iff (x : G) :
    x ∈ square G ↔ ∃ y : G, y ^ 2 = x := by
  simp [Subgroup.mem_square, IsSquare, pow_two, eq_comm]

/-- The square subgroup agrees with the range of the square map.
@isnad1 id=eq.0h1v.s5.8dd4ee3dfd82 from=translated src=- shape=59ca8f69 vocab=2642bf5d
-/
theorem square_eq_powMonoidHom_range :
    square G = (powMonoidHom (α := G) 2).range := by
  ext x
  simp [Subgroup.mem_square, IsSquare, pow_two, eq_comm]

/-- A two-torsion element has square one.
@isnad1 id=eq.0h2v.s6.a69f22755df3 from=translated src=- shape=86630628 vocab=c3af12a2
-/
theorem twoTorsion_mul_self_eq_one (x : twoTorsion G) :
    (x.1 : G) * x.1 = 1 := by
  simpa [pow_two] using (mem_twoTorsion_iff x.1).mp x.2

/-- A two-torsion element is fixed by inversion.
@isnad1 id=eq.0h2v.s6.e5e9939c2b00 from=translated src=- shape=1a60274a vocab=a3c19320
-/
theorem twoTorsion_eq_inv (x : twoTorsion G) :
    (x.1 : G) = x.1⁻¹ :=
  (eq_inv_iff_mul_eq_one).2 (twoTorsion_mul_self_eq_one x)

end Subgroup

namespace Subgroup

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- A homomorphism of commutative groups maps squares to squares.
@isnad1 id=le.0h3v.s6.87a3437bdbc7 from=translated src=- shape=31ae4cb2 vocab=36299f3f
-/
theorem square_le_comap_square (f : G →* H) :
    square G ≤ (square H).comap f := by
  intro x hx
  exact (mem_square.mp hx).map f

/-- A surjective homomorphism of commutative groups maps the square subgroup
onto the square subgroup.
@isnad1 id=eq.1h3v.s6.481ff975b5b4 from=translated src=- shape=e837f32e vocab=819c89bf
-/
theorem map_square_eq_square_of_surjective
    (f : G →* H) (hf : Function.Surjective f) :
    Subgroup.map f (square G) = square H := by
  ext y
  change y ∈ f '' {x : G | IsSquare x} ↔ IsSquare y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    exact isSquare_subset_image_isSquare hf hy

/-- For a surjective homomorphism, the preimage of the square subgroup is the
product of the square subgroup and the kernel.
@isnad1 id=eq.1h3v.s7.c3ac619bf8cd from=translated src=- shape=e1b93248 vocab=10fb323e
-/
theorem comap_square_eq_square_sup_ker_of_surjective
    (f : G →* H) (hf : Function.Surjective f) :
    (square H).comap f = square G ⊔ f.ker := by
  rw [← map_square_eq_square_of_surjective f hf]
  exact Subgroup.comap_map_eq f (square G)

end Subgroup

namespace CommGroup

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- A homomorphism of commutative groups descends to their square quotients.-/
def squareQuotientMap (f : G →* H) : squareQuotient G →* squareQuotient H :=
  QuotientGroup.map (Subgroup.square G) (Subgroup.square H) f
    (Subgroup.square_le_comap_square f)

/-- On representatives, `squareQuotientMap f` is given by `f`.
@isnad1 id=eq.0h4v.s7.1722491a8ac6 from=translated src=- shape=a29ef101 vocab=1ccbe689
-/
@[simp]
theorem squareQuotientMap_mk (f : G →* H) (x : G) :
    squareQuotientMap f (x : squareQuotient G) = (f x : squareQuotient H) :=
  QuotientGroup.map_mk (Subgroup.square G) (Subgroup.square H) f _ x

/-- A surjective homomorphism gives a surjective map on square quotients.
@isnad1 id=surjecti.1h3v.s7.429fc912901f from=translated src=- shape=1aeb3f0b vocab=27286f40
-/
theorem squareQuotientMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (squareQuotientMap f) := by
  exact QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hf) _

/-- The kernel on square quotients is the image of the original kernel when
the homomorphism is surjective.
@isnad1 id=eq.1h3v.s7.93bf1b04ffdf from=translated src=- shape=28a6e86f vocab=966f9875
-/
theorem squareQuotientMap_ker_eq_map_ker_of_surjective
    (f : G →* H) (hf : Function.Surjective f) :
    (squareQuotientMap f).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square G)) f.ker := by
  rw [squareQuotientMap, QuotientGroup.ker_map]
  rw [Subgroup.comap_square_eq_square_sup_ker_of_surjective f hf]
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

/-- Isomorphic commutative groups have isomorphic square quotients.-/
noncomputable def squareQuotientMulEquiv (e : G ≃* H) :
    squareQuotient G ≃* squareQuotient H :=
  QuotientGroup.congr (Subgroup.square G) (Subgroup.square H) e (by
    rw [Subgroup.square_eq_powMonoidHom_range,
      Subgroup.square_eq_powMonoidHom_range]
    exact MulEquiv.map_range_powMonoidHom e 2)

/-- On representatives, `squareQuotientMulEquiv e` is given by `e`.
@isnad1 id=eq.0h4v.s8.ecb211feba33 from=translated src=- shape=a29ef101 vocab=76c071a7
-/
@[simp]
theorem squareQuotientMulEquiv_mk (e : G ≃* H) (x : G) :
    squareQuotientMulEquiv e (x : squareQuotient G) = (e x : squareQuotient H) :=
  rfl

/-- For a finite commutative group, the square quotient has the same cardinality
as the two-torsion subgroup.
@isnad1 id=eq.0h1v.s5.948542613c0d from=translated src=- shape=c6406c98 vocab=718f9689
-/
theorem card_squareQuotient_eq_card_twoTorsion [Finite G] :
    Nat.card (squareQuotient G) = Nat.card (Subgroup.twoTorsion G) := by
  rw [squareQuotient, Subgroup.square_eq_powMonoidHom_range,
    ← (powMonoidHom (α := G) 2).range.index_eq_card]
  exact Subgroup.index_range (f := powMonoidHom (α := G) 2)

end CommGroup

namespace Subgroup

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- Deprecated namespace alias for the square-quotient/two-torsion cardinality theorem.
@isnad1 id=eq.0h1v.s5.948542613c0d from=translated src=- shape=c6406c98 vocab=718f9689
-/
@[deprecated CommGroup.card_squareQuotient_eq_card_twoTorsion (since := "2026-07-12")]
theorem card_squareQuotient_eq_card_twoTorsion [Finite G] :
    Nat.card (CommGroup.squareQuotient G) = Nat.card (twoTorsion G) :=
  CommGroup.card_squareQuotient_eq_card_twoTorsion

/-- An isomorphism restricts to the `n`-power torsion subgroups.-/
def powTorsionMulEquiv (e : G ≃* H) (n : ℕ) :
    powTorsion G n ≃* powTorsion H n :=
  { Equiv.subtypeEquiv e.toEquiv fun x ↦ by
      simp only [mem_powTorsion_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
        ← map_pow, EmbeddingLike.map_eq_one_iff] with
    map_mul' := fun _ _ ↦ Subtype.ext (map_mul e _ _) }

/-- On the underlying groups, `powTorsionMulEquiv e n` is given by `e`.
@isnad1 id=eq.0h5v.s9.15f8b12f6839 from=translated src=- shape=0721fb71 vocab=34d8cc78
-/
@[simp]
theorem coe_powTorsionMulEquiv_apply (e : G ≃* H) (n : ℕ) (x : powTorsion G n) :
    ((powTorsionMulEquiv e n x : powTorsion H n) : H) = e x :=
  rfl

/-- Isomorphic commutative groups have `n`-power torsion subgroups of the same
cardinality.
@isnad1 id=eq.0h4v.s6.7338eb975344 from=translated src=- shape=94145b89 vocab=7afc14e6
-/
theorem card_powTorsion_congr (e : G ≃* H) (n : ℕ) :
    Nat.card (powTorsion G n) = Nat.card (powTorsion H n) :=
  Nat.card_congr (powTorsionMulEquiv e n).toEquiv

/-- Isomorphic commutative groups have two-torsion subgroups of the same
cardinality.
@isnad1 id=eq.0h3v.s6.0dc7250de4b5 from=translated src=- shape=08738174 vocab=71343088
-/
theorem card_twoTorsion_congr (e : G ≃* H) :
    Nat.card (twoTorsion G) = Nat.card (twoTorsion H) :=
  card_powTorsion_congr e 2

end Subgroup

namespace ClassGroup

variable (R)
variable [CommRing R] [IsDomain R]

/-- The subgroup of ideal classes killed by the `n`th-power map. This is the
multiplicative class-group version of `AddSubgroup.torsionBy`.-/
noncomputable abbrev torsionBy (n : ℕ) : Subgroup (ClassGroup R) :=
  Subgroup.powTorsion (ClassGroup R) n

/-- The two-torsion subgroup `Cl[2]` of the ideal class group.-/
noncomputable abbrev twoTorsion : Subgroup (ClassGroup R) :=
  Subgroup.twoTorsion (ClassGroup R)

variable {R}

variable [IsDedekindDomain R]

/-- The `n`th power of the ideal class `mk0 I` is trivial exactly when the `n`th
power of the ideal `I` is principal.
@isnad1 id=iff.0h3v.s11.ac1c34836dad from=translated src=- shape=5c474e8c vocab=52508509
-/
@[simp]
theorem mk0_pow_eq_one_iff_pow_isPrincipal
    (I : nonZeroDivisors (Ideal R)) (n : ℕ) :
    (mk0 I : ClassGroup R) ^ n = 1 ↔ ((I : Ideal R) ^ n).IsPrincipal := by
  rw [← map_pow, mk0_eq_one_iff, SubmonoidClass.coe_pow]

/-- The ideal class `mk0 I` lies in the `n`-power torsion subgroup `Cl[n]` exactly
when `I ^ n` is principal.
@isnad1 id=iff.0h3v.s11.3b2a580a3652 from=translated src=- shape=daed4ffb vocab=646d5206
-/
theorem mk0_mem_torsionBy_iff
    (I : nonZeroDivisors (Ideal R)) (n : ℕ) :
    mk0 I ∈ torsionBy R n ↔ ((I : Ideal R) ^ n).IsPrincipal := by
  rw [torsionBy, Subgroup.mem_powTorsion_iff, mk0_pow_eq_one_iff_pow_isPrincipal]

/-- The ideal class `mk0 I` lies in the two-torsion subgroup `Cl[2]` exactly when
`I ^ 2` is principal.
@isnad1 id=iff.0h2v.s11.213998e1ef50 from=translated src=- shape=209c6047 vocab=6fc47617
-/
theorem mk0_mem_twoTorsion_iff
    (I : nonZeroDivisors (Ideal R)) :
    mk0 I ∈ twoTorsion R ↔ ((I : Ideal R) ^ 2).IsPrincipal := by
  rw [twoTorsion, Subgroup.mem_twoTorsion_iff, mk0_pow_eq_one_iff_pow_isPrincipal]

end ClassGroup

namespace Tengoku.QuadraticNumberFields.NarrowClassGroup

variable (R)
variable [CommRing R] [IsDomain R]

/-- The subgroup of narrow ideal classes killed by the `n`th-power map. This is
the narrow-class-group analogue of `ClassGroup.torsionBy`.-/
noncomputable abbrev torsionBy (n : ℕ) : Subgroup (NarrowClassGroup R) :=
  Subgroup.powTorsion (NarrowClassGroup R) n

/-- The two-torsion subgroup `Cl⁺[2]` of the narrow ideal class group.-/
noncomputable abbrev twoTorsion : Subgroup (NarrowClassGroup R) :=
  Subgroup.twoTorsion (NarrowClassGroup R)

variable {R}

section DedekindDomain

variable [IsDedekindDomain R]

/-- If `[I] = C` and `C ∈ Cl⁺(R)[2]`, then `[I]² = 1`.
@isnad1 id=eq.1h3v.s12.43034afcb781 from=translated src=- shape=a3bd12cd vocab=a31f7446
-/
theorem mk0_mul_self_eq_one_of_twoTorsion
    {C : twoTorsion R} {I : nonZeroDivisors (Ideal R)}
    (hI : mk0 I = C.1) :
    mk0 (I * I) = 1 := by
  simpa only [map_mul, hI] using Subgroup.twoTorsion_mul_self_eq_one C

end DedekindDomain

end Tengoku.QuadraticNumberFields.NarrowClassGroup

/-
Exact Sequence
1 → Cl⁺(R)[2] → Cl⁺(R) → Cl⁺(R)² → 1
Definition of narrow class group. 1 → P⁺(R) → I(R) → Cl⁺(R) → 1.
1 → (O R)ˣ⁺ → (Rˣ)⁺ → P⁺(R) → 1
rank F₂ Cl⁺(R)[2] =t-1
-/
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
