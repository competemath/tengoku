/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Lie.EngelSubalgebra
public import Tengoku.Seed.Algebra.Lie.OfAssociative
public import Tengoku.Seed.Algebra.Module.LinearMap.Polynomial
public import Tengoku.Seed.LinearAlgebra.Eigenspace.Zero

/-!
# Rank of a Lie algebra and regular elements

Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.

Continuing to write `n` for the rank of `L`, an element `x` of `L` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero.

## Main declarations

* `LieAlgebra.rank R L` is the rank of a Lie algebra `L` over a commutative ring `R`.
* `LieAlgebra.IsRegular R x` is the predicate that an element `x` of a Lie algebra `L` is regular.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

@[expose] public section

open Module

variable {R L M ι ιₘ : Type*}
variable [CommRing R]
variable [LieRing L] [LieAlgebra R L] [Module.Finite R L] [Module.Free R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite R M] [Module.Free R M]
variable [Fintype ι]
variable [Fintype ιₘ]
variable (b : Basis ι R L) (bₘ : Basis ιₘ R M) (x : L)

namespace LieModule

open LieAlgebra LinearMap Module.Free
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L M)

local notation "φ" => LieHom.toLinearMap (LieModule.toEnd R L M)

/--
Let `M` be a representation of a Lie algebra `L` over a nontrivial commutative ring `R`,
and assume that `L` and `M` are finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `⁅x, ·⁆` are polynomial in `x`.
The *rank* of `M` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
def rank : ℕ := nilRank φ

/--
@isnad1 id=ne.0h5v.s8.1d894ad2cd9c from=seed src=0 shape=2e3e2fe6 vocab=73aa7f06
-/
lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly φ b).coeff (rank R L M) ≠ 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _

/--
@isnad1 id=eq.0h5v.s8.bc7ed7700217 from=seed src=0 shape=e0c66ad2 vocab=f050dfc0
-/
lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L M = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include bₘ in
/--
@isnad1 id=le.0h5v.s7.e27ff5f146d3 from=seed src=0 shape=becb6fb2 vocab=2cb775db
-/
lemma rank_le_card [Nontrivial R] : rank R L M ≤ Fintype.card ιₘ :=
  nilRank_le_card _ bₘ

open Module
/--
@isnad1 id=le.0h3v.s7.de4494da8554 from=seed src=0 shape=4b10af0f vocab=2ae42855
-/
lemma rank_le_finrank [Nontrivial R] : rank R L M ≤ finrank R M :=
  nilRank_le_finrank _

variable {L}

/--
@isnad1 id=le.0h4v.s8.162d315d6dbe from=seed src=0 shape=6300e622 vocab=29ead0e5
-/
lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L M ≤ (toEnd R L M x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop := LinearMap.IsNilRegular φ x

/--
@isnad1 id=iff.0h4v.s8.04575df4acf1 from=seed src=0 shape=1a1a31f2 vocab=cbdbb0ba
-/
lemma isRegular_def :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.coeff (rank R L M) ≠ 0 := Iff.rfl

/--
@isnad1 id=iff.0h6v.s9.51a6678b4f89 from=seed src=0 shape=965327b1 vocab=bad3e4a3
-/
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R M x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (rank R L M)) ≠ 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

/--
@isnad1 id=iff.0h4v.s8.910a3ba1c835 from=seed src=0 shape=614f44a4 vocab=85f71024
-/
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.natTrailingDegree = rank R L M :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
/--
@isnad1 id=ex.1h3v.s7.b591cd354626 from=seed src=0 shape=634f71ee vocab=454a0fdb
-/
lemma exists_isRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h

/--
@isnad1 id=ex.0h3v.s7.59da3e5a8857 from=seed src=0 shape=57e6f69a vocab=e0700a7e
-/
lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieModule

namespace LieAlgebra

open LieAlgebra LinearMap Module.Free
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L)

/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
abbrev rank : ℕ := LieModule.rank R L L

/--
@isnad1 id=ne.0h4v.s8.f0acd04a79f5 from=seed src=0 shape=c8b4c6d3 vocab=e49d3759
-/
lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly (ad R L).toLinearMap b).coeff (rank R L) ≠ 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _

/--
@isnad1 id=eq.0h4v.s8.182e4147b6ce from=seed src=0 shape=a7c8f7e6 vocab=73bac950
-/
lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L = (polyCharpoly (ad R L).toLinearMap b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include b in
/--
@isnad1 id=le.0h4v.s6.6a12c3b41d87 from=seed src=0 shape=77474985 vocab=1b4c5111
-/
lemma rank_le_card [Nontrivial R] : rank R L ≤ Fintype.card ι :=
  nilRank_le_card _ b

/--
@isnad1 id=le.0h2v.s6.1bc10ca0a0ef from=seed src=0 shape=b56f0586 vocab=32ee6dea
-/
lemma rank_le_finrank [Nontrivial R] : rank R L ≤ finrank R L :=
  nilRank_le_finrank _

variable {L}

/--
@isnad1 id=le.0h3v.s8.69d71a958efd from=seed src=0 shape=9e367bfa vocab=0b8fb582
-/
lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L ≤ (ad R L x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
abbrev IsRegular (x : L) : Prop := LieModule.IsRegular R L x

/--
@isnad1 id=iff.0h3v.s8.53f7c68eac32 from=seed src=0 shape=46a35496 vocab=71001bdf
-/
lemma isRegular_def :
    IsRegular R x ↔ (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := Iff.rfl

/--
@isnad1 id=iff.0h5v.s9.51fbddfff7a0 from=seed src=0 shape=16f4251a vocab=fa9fae7d
-/
lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly (ad R L).toLinearMap b).coeff (rank R L)) ≠ 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

/--
@isnad1 id=iff.0h3v.s8.c7a03c66c1fb from=seed src=0 shape=ca7c566a vocab=a3df5d5a
-/
lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
/--
@isnad1 id=ex.1h2v.s6.c55ea721b610 from=seed src=0 shape=5059afd9 vocab=fe25329a
-/
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h

/--
@isnad1 id=ex.0h2v.s6.fa91affe503b from=seed src=0 shape=2dd74354 vocab=327465c8
-/
lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieAlgebra

namespace LieAlgebra

variable (K : Type*) {L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open Module LieSubalgebra

/--
@isnad1 id=eq.0h3v.s9.6a8ef5fb6567 from=seed src=0 shape=cfa60ef3 vocab=4587c37b
-/
lemma finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree :=
  (ad K L x).finrank_maxGenEigenspace_zero_eq

/--
@isnad1 id=le.0h3v.s8.0997249cc784 from=seed src=0 shape=e9cfc35a vocab=197d4fda
-/
lemma rank_le_finrank_engel (x : L) :
    rank K L ≤ finrank K (engel K x) :=
  (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge

/--
@isnad1 id=iff.0h3v.s8.5861edd9b224 from=seed src=0 shape=abf96d12 vocab=5dfdf993
-/
lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular K x ↔ finrank K (engel K x) = rank K L := by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank, finrank_engel]

end LieAlgebra
