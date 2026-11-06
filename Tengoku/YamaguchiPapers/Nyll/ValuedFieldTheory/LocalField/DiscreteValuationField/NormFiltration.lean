/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norm compatibility with unit filtrations

A compatibility hypothesis for a norm and two unit filtrations immediately
produces homomorphisms on every filtration level.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)
variable (UG : AntitoneSubgroupFiltration G) (UH : AntitoneSubgroupFiltration H)
variable (targetLevel : ℕ → ℕ)

/-- A compatibility hypothesis for the norm and two filtrations.-/
abbrev MapsFiltrationLevels : Prop :=
  ∀ n {x : H}, x ∈ UH.principalUnitSubgroup n →
    N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n)

/-- The norm map restricted to a filtration level.-/
def mapLevelOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    UH.principalUnitSubgroup n →* UG.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨N.toHom x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact N.toHom.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact N.toHom.map_mul x.1 y.1

/--
The defining evaluation formula for `mapLevelOfMapsFiltrationLevels` is
`(mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) = N.toHom x.1`.
@isnad1 id=eq.1h10v.s9.b56f98efa87c from=translated src=- shape=9616fcc0 vocab=ffb5cdff
-/
@[simp] theorem mapLevelOfMapsFiltrationLevels_apply
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (x : UH.principalUnitSubgroup n) :
    (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) =
      N.toHom x.1 :=
  rfl

/-- A compatible norm descends to the quotient by a filtration level.-/
def quotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    H ⧸ UH.principalUnitSubgroup n →*
      G ⧸ UG.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UH.principalUnitSubgroup n)
    (UG.principalUnitSubgroup (targetLevel n)) N.toHom (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `quotientMapOfMapsFiltrationLevels` is
`quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n (QuotientGroup.mk x) =
QuotientGroup.mk (N.toHom x)`.
@isnad1 id=eq.1h10v.s9.433a65899f9a from=translated src=- shape=47069901 vocab=63d8e974
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (N.toHom x) :=
  rfl

/--
Establishes the identity `quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x) = QuotientGroup.mk' (UG.principalUnitSubgroup
(targetLevel n)) (N.toHom x)`.
@isnad1 id=eq.1h10v.s9.2e57bbe154bf from=translated src=- shape=66fd7e0f vocab=7456ad83
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk'
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) :=
  rfl

/-- The preimage of the target filtration subgroup under the valued norm.-/
def filtrationPreimageSubgroup (n : ℕ) : Subgroup H :=
  (UG.principalUnitSubgroup (targetLevel n)).comap N.toHom

/--
Characterizes `x ∈ N.filtrationPreimageSubgroup UG targetLevel n` by the equivalent condition
`N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n)`.
@isnad1 id=iff.0h9v.s7.82ff572f3fa0 from=translated src=- shape=c79c8047 vocab=f4607d25
-/
@[simp] theorem mem_filtrationPreimageSubgroup_iff (n : ℕ) (x : H) :
    x ∈ N.filtrationPreimageSubgroup UG targetLevel n ↔
      N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n) :=
  Iff.rfl

/-- The subgroup appearing in `(N.filtrationPreimageSubgroup UG targetLevel n).Normal` is normal.
@isnad1 id=normal.0h8v.s5.8e51f6aa5db0 from=translated src=- shape=0f3170f9 vocab=dcd9481d
-/
instance filtrationPreimageSubgroup_normal
    (n : ℕ) [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageSubgroup UG targetLevel n).Normal := by
  dsimp [filtrationPreimageSubgroup]
  infer_instance

/-- The class of the norm-preimage of the target filtration subgroup inside
the source quotient `H ⧸ U_H^n`.-/
def filtrationPreimageClassInQuotient (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal] :
    Subgroup (H ⧸ UH.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UH.principalUnitSubgroup n))
    (N.filtrationPreimageSubgroup UG targetLevel n)

/--
The subgroup appearing in `(N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal` is
normal.
@isnad1 id=normal.0h9v.s6.69f78cfe825a from=translated src=- shape=222b7a18 vocab=1b52d04d
-/
instance filtrationPreimageClassInQuotient_normal
    (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal := by
  dsimp [filtrationPreimageClassInQuotient]
  infer_instance

/-- The kernel of the quotient norm map is the class of the preimage of the
target filtration subgroup in the source quotient.
@isnad1 id=eq.1h9v.s7.62fac7670b57 from=translated src=- shape=94dadb85 vocab=0220a696
-/
theorem quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).ker =
      N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  exact QuotientGroup.ker_map (UH.principalUnitSubgroup n)
    (UG.principalUnitSubgroup (targetLevel n)) N.toHom (fun _ hx => hN n hx)

/-- First-isomorphism form of the filtration quotient norm map, with codomain
the actual range when no surjectivity hypothesis is available.-/
noncomputable def quotientModuloFiltrationPreimageClassEquivRange
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (H ⧸ UH.principalUnitSubgroup n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q`.
@isnad1 id=eq.1h10v.s12.b2c81df095c3 from=translated src=- shape=f267d1da vocab=25405cf0
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)) = (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).rangeRestrict (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)`.
@isnad1 id=eq.1h10v.s12.c5d408828d01 from=translated src=- shape=09927972 vocab=25405cf0
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) :=
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) : G ⧸ UG.principalUnitSubgroup
(targetLevel n)) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
@isnad1 id=eq.1h10v.s12.76762996e160 from=translated src=- shape=8953b14b vocab=816e586a
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n q]
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)) : (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).range) : G ⧸ UG.principalUnitSubgroup (targetLevel n)) = QuotientGroup.mk'
(UG.principalUnitSubgroup (targetLevel n)) (N.toHom x)`.
@isnad1 id=eq.1h10v.s12.fda35dca703d from=translated src=- shape=9c6f60d6 vocab=2de17ad4
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) := by
  rw [N.coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n
    (QuotientGroup.mk' (UH.principalUnitSubgroup n) x),
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
@isnad1 id=eq.1h10v.s12.25ebf6f62dd6 from=translated src=- shape=fd5f34c5 vocab=3f5bb16a
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivRange
    UG UH targetLevel hN n).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        ((N.quotientModuloFiltrationPreimageClassEquivRange
          UG UH targetLevel hN n).symm
          ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivRange
            UG UH targetLevel hN n).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
          UG UH targetLevel hN n q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) = QuotientGroup.mk'
(N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)`.
@isnad1 id=eq.1h10v.s13.1a696d70b25c from=translated src=- shape=678280b9 vocab=3f5bb16a
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    UG UH targetLevel hN n]

/-- First-isomorphism form of a surjective filtration quotient norm map.-/
noncomputable def quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) :
    (H ⧸ UH.principalUnitSubgroup n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      G ⧸ UG.principalUnitSubgroup (targetLevel n) :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) hSurj)

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel
n) q) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
@isnad1 id=eq.2h10v.s11.d421ca64824b from=translated src=- shape=4159454b vocab=34067dce
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (q : H ⧸ UH.principalUnitSubgroup n) :
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  change QuotientGroup.kerLift
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)
      ((QuotientGroup.quotientMulEquivOfEq
        (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
          UG UH targetLevel hN n).symm) (QuotientGroup.mk q)) =
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) q

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel
n) (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) = QuotientGroup.mk'
(UG.principalUnitSubgroup (targetLevel n)) (N.toHom x)`.
@isnad1 id=eq.2h10v.s12.5d1a5f7284cf from=translated src=- shape=7657d5c6 vocab=b3eee551
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
    UG UH targetLevel hN n hSurj,
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj).symm (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
@isnad1 id=eq.2h10v.s12.d11b3013b111 from=translated src=- shape=07610b83 vocab=61f723a7
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (q : H ⧸ UH.principalUnitSubgroup n) :
    (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj).symm
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
    UG UH targetLevel hN n hSurj).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        ((N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
          UG UH targetLevel hN n hSurj).symm
          (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
            UG UH targetLevel hN n hSurj).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
          UG UH targetLevel hN n hSurj q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj).symm (QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
(N.toHom x)) = QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x)`.
@isnad1 id=eq.2h10v.s12.28008999dcf9 from=translated src=- shape=f38f03ef vocab=b74c08e6
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj).symm
        (QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
          (N.toHom x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) := by
  rw [← N.quotientMapOfMapsFiltrationLevels_apply_mk'
    UG UH targetLevel hN n x,
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_map
      UG UH targetLevel hN n hSurj]

/-- A filtration-compatible norm induces maps on principal-unit subquotients:
`U_H^m/U_H^n → U_G^(targetLevel m)/U_G^(targetLevel n)`.-/
def principalUnitSubquotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (_hmn : m ≤ n) (_htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    UH.principalUnitSubquotient m n →*
      UG.principalUnitSubquotient (targetLevel m) (targetLevel n) :=
  UH.principalUnitSubquotientLift m n
    ((UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)).comp
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m))
    (by
      intro x hx
      change UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
          (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) = 1
      rw [UG.principalUnitSubquotient_mk_eq_one_iff]
      exact hN n hx)

/--
The defining evaluation formula for `principalUnitSubquotientMapOfMapsFiltrationLevels` is
`N.principalUnitSubquotientMapOfMapsFiltrationLevels UG UH targetLevel hN hmn htarget
(UH.principalUnitSubquotientMk m n x) = UG.principalUnitSubquotientMk (targetLevel m) (targetLevel
n) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x)`.
@isnad1 id=eq.3h11v.s10.faa0978d140c from=translated src=- shape=a8c37cd1 vocab=1157981f
-/
@[simp] theorem principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (x : UH.principalUnitSubgroup m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) =
      UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) :=
  rfl

/-- The subquotient norm map agrees with the ambient quotient norm map under
the canonical embeddings of subquotients as classes in ambient quotients.
@isnad1 id=eq.3h11v.s11.df3a4b00ebe5 from=translated src=- shape=83c60190 vocab=d9cef1b9
-/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotient_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (z : UH.principalUnitSubquotient m n) :
    ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
        (N.principalUnitSubquotientMapOfMapsFiltrationLevels
          UG UH targetLevel hN hmn htarget z) :
      UG.principalUnitSubgroupClassInQuotient (targetLevel m)
        (targetLevel n)) :
      G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z :
          UH.principalUnitSubgroupClassInQuotient m n) :
          H ⧸ UH.principalUnitSubgroup n) := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      UH m n
        (motive := fun z' ↦
          ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
              (N.principalUnitSubquotientMapOfMapsFiltrationLevels
                UG UH targetLevel hN hmn htarget z') :
            UG.principalUnitSubgroupClassInQuotient (targetLevel m)
              (targetLevel n)) :
            G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
          quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
            ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z' :
              UH.principalUnitSubgroupClassInQuotient m n) :
              H ⧸ UH.principalUnitSubgroup n)) z ?_
  intro x
  rw [principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk,
    UG.coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk,
    UH.coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk,
    quotientMapOfMapsFiltrationLevels_apply_mk', mapLevelOfMapsFiltrationLevels_apply]

/-- The graded-piece form of
`principalUnitSubquotientMapOfMapsFiltrationLevels`.-/
def principalUnitGradedPieceMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.principalUnitSubgroup (n + 1)).Normal]
    [(UG.principalUnitSubgroup (targetLevel (n + 1))).Normal] :
    UH.principalUnitGradedPiece n →*
      UG.principalUnitSubquotient (targetLevel n) (targetLevel (n + 1)) :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels
    UG UH targetLevel hN (Nat.le_succ n) htarget).comp
      (UH.principalUnitGradedPieceEquivSubquotient n).toMonoidHom

/--
The defining evaluation formula for `principalUnitGradedPieceMapOfMapsFiltrationLevels` is
`N.principalUnitGradedPieceMapOfMapsFiltrationLevels UG UH targetLevel hN n htarget
(UH.principalUnitGradedPieceMk n x) = UG.principalUnitSubquotientMk (targetLevel n) (targetLevel
(n + 1)) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x)`.
@isnad1 id=eq.2h10v.s11.4670d5c44422 from=translated src=- shape=c97e42e2 vocab=6106642e
-/
@[simp] theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.principalUnitSubgroup (n + 1)).Normal]
    [(UG.principalUnitSubgroup (targetLevel (n + 1))).Normal]
    (x : UH.principalUnitSubgroup n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) =
      UG.principalUnitSubquotientMk (targetLevel n) (targetLevel (n + 1))
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x) :=
  rfl

end ValuedNorm
end DiscreteValuationField

end

end LocalFieldTheory
