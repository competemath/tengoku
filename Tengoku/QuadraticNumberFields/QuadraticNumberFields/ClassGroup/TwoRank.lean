/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.Algebra.Module.ZMod
import Tengoku.Seed.FieldTheory.Finiteness
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.ClassGroup.Torsion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The 2-Rank of Class Groups

When `G / G²` is finite, the **2-rank** of `G` is its dimension over `ZMod 2`.
The square quotient has a canonical `ZMod 2`-module structure, and group
homomorphisms act linearly on it. The definition below relates this dimension
to the cardinality of `G / G²` and is then specialized to class groups.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
namespace CommGroup

variable (G : Type*) [CommGroup G]

/-- The canonical `ZMod 2`-module structure on the additive form of `G / G²`.-/
noncomputable instance instModuleSquareQuotient :
    Module (ZMod 2) (Additive (squareQuotient G)) :=
  AddCommGroup.zmodModule fun x ↦ by
    change x.toMul ^ 2 = 1
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.square G) x.toMul
    rw [← hg, ← map_pow]
    change ((g ^ 2 : G) : G ⧸ Subgroup.square G) = 1
    exact (QuotientGroup.eq_one_iff (g ^ 2)).mpr
      ((Subgroup.mem_square_iff (g ^ 2)).mpr ⟨g, rfl⟩)

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- The `ZMod 2`-linear map on square quotients induced by a group homomorphism.-/
noncomputable def squareQuotientLinearMap (f : G →* H) :
    Additive (squareQuotient G) →ₗ[ZMod 2] Additive (squareQuotient H) :=
  (MonoidHom.toAdditive (squareQuotientMap f)).toZModLinearMap 2

/-- The underlying group map of `squareQuotientLinearMap f` is `squareQuotientMap f`.
@isnad1 id=eq.0h4v.s9.ff855ef3613e from=translated src=- shape=386249d2 vocab=1781d85e
-/
@[simp]
theorem squareQuotientLinearMap_apply (f : G →* H) (x : Additive (squareQuotient G)) :
    (squareQuotientLinearMap f x).toMul = squareQuotientMap f x.toMul :=
  rfl

/-- The linear map on square quotients is surjective when the group homomorphism is.
@isnad1 id=surjecti.1h3v.s8.c67603e57ac3 from=translated src=- shape=a9ce6f8f vocab=a46030f8
-/
theorem squareQuotientLinearMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (squareQuotientLinearMap f) := by
  simpa [squareQuotientLinearMap] using squareQuotientMap_surjective f hf

/-- An isomorphism of commutative groups gives a linear equivalence of their
square quotients over `ZMod 2`.-/
noncomputable def squareQuotientLinearEquiv (e : G ≃* H) :
    Additive (squareQuotient G) ≃ₗ[ZMod 2] Additive (squareQuotient H) :=
  { (squareQuotientMulEquiv e).toAdditive with
    map_smul' := ZMod.map_smul (squareQuotientMulEquiv e).toAdditive }

/-- The underlying group equivalence is `squareQuotientMulEquiv e`.
@isnad1 id=eq.0h4v.s9.6ed5c5b98ee5 from=translated src=- shape=2c6631cf vocab=4e86dbdc
-/
@[simp]
theorem squareQuotientLinearEquiv_apply (e : G ≃* H)
    (x : Additive (squareQuotient G)) :
    (squareQuotientLinearEquiv e x).toMul = squareQuotientMulEquiv e x.toMul :=
  rfl

variable (G) in
/-- The `ZMod 2`-dimension of `G / G²`.-/
noncomputable def twoRank : ℕ :=
  Module.finrank (ZMod 2) (Additive (squareQuotient G))

/-- A finite square-class group has cardinality
`2 ^ twoRank G`.
@isnad1 id=eq.0h1v.s5.a4d2e1e157a7 from=translated src=- shape=52472c73 vocab=87d7d730
-/
theorem card_squareQuotient_eq_two_pow_twoRank [Finite (squareQuotient G)] :
    Nat.card (squareQuotient G) = 2 ^ twoRank G := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change Nat.card (squareQuotient G) =
    2 ^ Module.finrank (ZMod 2) (Additive (squareQuotient G))
  calc
    Nat.card (squareQuotient G) = Nat.card (Additive (squareQuotient G)) :=
      Nat.card_congr Additive.ofMul
    _ = 2 ^ Module.finrank (ZMod 2) (Additive (squareQuotient G)) :=
      by simpa using
        (Module.natCard_eq_pow_finrank
          (K := ZMod 2) (V := Additive (squareQuotient G)))

end CommGroup

namespace ClassGroup

variable (R) [CommRing R] [IsDomain R]
variable [Finite (CommGroup.squareQuotient (ClassGroup R))]

/-- The 2-rank of the ideal class group.-/
noncomputable abbrev twoRank : ℕ :=
  CommGroup.twoRank (ClassGroup R)

end ClassGroup

namespace Tengoku.QuadraticNumberFields.NarrowClassGroup

variable (R) [CommRing R] [IsDomain R]
variable [Finite (CommGroup.squareQuotient (NarrowClassGroup R))]

/-- The 2-rank of the narrow ideal class group.-/
noncomputable abbrev twoRank : ℕ :=
  CommGroup.twoRank (NarrowClassGroup R)

end Tengoku.QuadraticNumberFields.NarrowClassGroup
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
