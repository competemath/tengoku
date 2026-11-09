/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.GaloisCohomology.GroupTheory.Augmentation
import Tengoku.ClassfieldtheoryYamaguchi.GaloisCohomology.GroupTheory.Transfer.RelativeAugmentation
import Tengoku.Seed.GroupTheory.Finiteness
import Tengoku.Seed.GroupTheory.Transfer
import Tengoku.Seed.GroupTheory.Torsion
import Tengoku.Seed.GroupTheory.FreeGroup.GeneratorEquiv
import Tengoku.Seed.LinearAlgebra.Dimension.Localization
import Tengoku.Seed.LinearAlgebra.Dimension.Torsion.Finite
import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.CardQuotient
import Tengoku.Seed.LinearAlgebra.FreeModule.PID
import Tengoku.Seed.LinearAlgebra.Matrix.Adjugate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Witt's transfer theorem

For a finitely generated group `G` with finite abelianization, the transfer
from `G / G'` to `G' / G''` is trivial.

The proof follows Witt's group-ring argument. This file first
constructs the required right Fox coefficients directly from free words; no
presentation relations are assumed as extra input.
-/

open scoped BigOperators Pointwise

noncomputable section

namespace GroupTheory
namespace Transfer
namespace Witt

open GroupTheory.Augmentation
open Subgroup
open GroupTheory.Transfer.RelativeAugmentation

variable {G : Type*} [Group G]

/-- Finite index of the commutator gives finiteness of the
abelianization.
@isnad1 id=finite.0h1v.s4.da4598dc4afe from=translated src=- shape=bfa1dd92 vocab=0eca8523
-/
noncomputable instance finiteAbelianizationOfFiniteIndex
    [FiniteIndex (commutator G)] :
    Finite (Abelianization G) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  exact Finite.of_fintype _

/-- The transfer between the successive commutator abelianizations
`G / G'` and `G' / G''`.-/
noncomputable def commutatorTransfer
    [FiniteIndex (commutator G)] :
    Abelianization G →* Abelianization (commutator G) :=
  Abelianization.lift
    (MonoidHom.transfer
      (Abelianization.of :
        commutator G →* Abelianization (commutator G)))

/--
@isnad1 id=eq.0h2v.s10.6b493c407c5a from=translated src=- shape=1d4d5944 vocab=7a2b0f48
-/
@[simp]
theorem commutatorTransfer_of
    [FiniteIndex (commutator G)] (g : G) :
    commutatorTransfer (G := G) (Abelianization.of g) =
      MonoidHom.transfer
        (Abelianization.of :
          commutator G →* Abelianization (commutator G)) g :=
  rfl

/-- The integral group-ring element `[g] - 1`.-/
def groupRingDelta (g : G) : IntegralGroupRing G :=
  MonoidAlgebra.single g 1 -
    MonoidAlgebra.single (1 : G) 1

/--
@isnad1 id=eq.0h1v.s5.d1f967f9d9cb from=translated src=- shape=be87aaac vocab=359b0b52
-/
@[simp]
theorem groupRingDelta_one :
    groupRingDelta (1 : G) = 0 := by
  simp [groupRingDelta]

/--
@isnad1 id=eq.0h3v.s6.397a7fd5f992 from=translated src=- shape=d1ffcc1c vocab=598d22ac
-/
theorem groupRingDelta_mul (g h : G) :
    groupRingDelta (g * h) =
      groupRingDelta g * MonoidAlgebra.single h 1 +
        groupRingDelta h := by
  have hs :
      MonoidAlgebra.single (g * h) (1 : ℤ) =
        MonoidAlgebra.single g 1 *
          MonoidAlgebra.single h 1 := by
    simp
  rw [groupRingDelta, groupRingDelta, groupRingDelta, hs,
    ← MonoidAlgebra.one_def]
  noncomm_ring

/--
@isnad1 id=eq.0h3v.s6.1b80aa98cf63 from=translated src=- shape=3e38a067 vocab=598d22ac
-/
theorem groupRingDelta_mul_left (g h : G) :
    groupRingDelta (g * h) =
      MonoidAlgebra.single g 1 * groupRingDelta h +
        groupRingDelta g := by
  have hs :
      MonoidAlgebra.single (g * h) (1 : ℤ) =
        MonoidAlgebra.single g 1 *
          MonoidAlgebra.single h 1 := by
    simp
  rw [groupRingDelta, groupRingDelta, groupRingDelta, hs,
    ← MonoidAlgebra.one_def]
  noncomm_ring

/--
@isnad1 id=eq.0h2v.s6.9308333e39b9 from=translated src=- shape=5649c4aa vocab=91fc366c
-/
theorem groupRingDelta_inv (g : G) :
    groupRingDelta g⁻¹ =
      groupRingDelta g *
        (-MonoidAlgebra.single g⁻¹ 1) := by
  let x : IntegralGroupRing G :=
    MonoidAlgebra.single g 1
  let y : IntegralGroupRing G :=
    MonoidAlgebra.single g⁻¹ 1
  have hs :
      x * y =
        (1 : IntegralGroupRing G) := by
    simp [x, y, ← MonoidAlgebra.one_def]
  calc
    groupRingDelta g⁻¹ = y - 1 := rfl
    _ = y - x * y := by rw [hs]
    _ = (x - 1) * (-y) := by noncomm_ring
    _ = groupRingDelta g *
        (-MonoidAlgebra.single g⁻¹ 1) := rfl

/--
@isnad1 id=eq.0h2v.s6.2e0c2879cf72 from=translated src=- shape=9054d089 vocab=91fc366c
-/
theorem groupRingDelta_inv_left (g : G) :
    groupRingDelta g⁻¹ =
      (-MonoidAlgebra.single g⁻¹ 1) *
        groupRingDelta g := by
  let x : IntegralGroupRing G :=
    MonoidAlgebra.single g 1
  let y : IntegralGroupRing G :=
    MonoidAlgebra.single g⁻¹ 1
  have hyx : y * x = (1 : IntegralGroupRing G) := by
    simp [x, y, ← MonoidAlgebra.one_def]
  calc
    groupRingDelta g⁻¹ = y - 1 := rfl
    _ = y - y * x := by rw [hyx]
    _ = (-y) * (x - 1) := by noncomm_ring
    _ = (-MonoidAlgebra.single g⁻¹ 1) *
        groupRingDelta g := rfl

/--
@isnad1 id=eq.0h2v.s6.9a4cba5571e1 from=translated src=- shape=fdbe5369 vocab=4a3a3e2d
-/
@[simp]
theorem augmentation_groupRingDelta (g : G) :
    augmentation G (groupRingDelta g) = 0 := by
  simp [groupRingDelta]

/-- The exponent-sum vector of a free word.-/
def wordExponent {X : Type*} (w : FreeGroup X) : X →₀ ℤ :=
  FreeAbelianGroup.toFinsupp
    (Additive.ofMul (Abelianization.of w))

/--
@isnad1 id=eq.0h1v.s5.b915cb13e500 from=translated src=- shape=ff2a7e38 vocab=b350a754
-/
@[simp]
theorem wordExponent_one {X : Type*} :
    wordExponent (1 : FreeGroup X) = 0 := by
  exact map_zero FreeAbelianGroup.toFinsupp

/--
@isnad1 id=eq.0h2v.s5.fdc037f7722d from=translated src=- shape=b2d57611 vocab=b2ce0cd4
-/
@[simp]
theorem wordExponent_of {X : Type*} (x : X) :
    wordExponent (FreeGroup.of x) =
      Finsupp.single x 1 := by
  exact FreeAbelianGroup.toFinsupp_of x

/--
@isnad1 id=eq.0h2v.s5.34b0c78f866a from=translated src=- shape=b969bb3a vocab=0b7ad3d9
-/
@[simp]
theorem wordExponent_inv {X : Type*} (w : FreeGroup X) :
    wordExponent w⁻¹ = -wordExponent w := by
  show
    FreeAbelianGroup.toFinsupp
        (-Additive.ofMul (Abelianization.of w)) =
      -FreeAbelianGroup.toFinsupp
        (Additive.ofMul (Abelianization.of w))
  exact map_neg FreeAbelianGroup.toFinsupp _

/--
@isnad1 id=eq.0h3v.s6.55c56504c96b from=translated src=- shape=7e4b7a89 vocab=aed85a54
-/
@[simp]
theorem wordExponent_mul {X : Type*} (u v : FreeGroup X) :
    wordExponent (u * v) =
      wordExponent u + wordExponent v := by
  show
    FreeAbelianGroup.toFinsupp
        (Additive.ofMul (Abelianization.of u) +
          Additive.ofMul (Abelianization.of v)) =
      FreeAbelianGroup.toFinsupp
          (Additive.ofMul (Abelianization.of u)) +
        FreeAbelianGroup.toFinsupp
          (Additive.ofMul (Abelianization.of v))
  exact map_add FreeAbelianGroup.toFinsupp _ _

/-- A right Fox expansion of a free word, together with the fact that the
augmentation of each coefficient is the corresponding exponent sum.

This is the source-producing form needed for Witt's relation matrix.
@isnad1 id=ex.0h4v.s8.437f623ac6f0 from=translated src=- shape=b94ea5c8 vocab=6fd86beb
-/
theorem exists_rightFoxExpansion
    {X : Type*} [Fintype X] [DecidableEq X]
    (φ : FreeGroup X →* G) (w : FreeGroup X) :
    ∃ μ : X → IntegralGroupRing G,
      groupRingDelta (φ w) =
          ∑ i : X,
            groupRingDelta (φ (FreeGroup.of i)) * μ i ∧
      ∀ i : X,
        augmentation G (μ i) =
          wordExponent w i := by
  induction w using FreeGroup.induction_on with
  | one =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · intro i
        rw [wordExponent_one]
        rfl
  | of x =>
      refine
        ⟨Pi.single x 1, ?_, ?_⟩
      · rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hy
          simp [Pi.single_eq_of_ne hy]
        · simp
      · intro i
        by_cases hxi : x = i
        · subst i
          simp
        · rw [Pi.single_eq_of_ne (Ne.symm hxi), map_zero,
            wordExponent_of,
            Finsupp.single_eq_of_ne (Ne.symm hxi)]
  | inv_of x hx =>
      refine
        ⟨Pi.single x
            (-MonoidAlgebra.single
              (φ (FreeGroup.of x))⁻¹ 1),
          ?_, ?_⟩
      · rw [Finset.sum_eq_single x]
        · simpa using
            groupRingDelta_inv
              (φ (FreeGroup.of x))
        · intro y _ hy
          simp [Pi.single_eq_of_ne hy]
        · simp
      · intro i
        by_cases hxi : x = i
        · subst i
          simp
        · rw [Pi.single_eq_of_ne (Ne.symm hxi), map_zero,
            wordExponent_inv]
          change 0 = -(wordExponent (FreeGroup.of x) i)
          rw [wordExponent_of,
            Finsupp.single_eq_of_ne (Ne.symm hxi), neg_zero]
  | mul u v hu hv =>
      obtain ⟨μ, hμ, haugμ⟩ := hu
      obtain ⟨ν, hν, haugν⟩ := hv
      refine
        ⟨fun i =>
            μ i * MonoidAlgebra.single (φ v) 1 + ν i,
          ?_, ?_⟩
      · rw [map_mul, groupRingDelta_mul, hμ, hν,
          Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_add, mul_assoc]
      · intro i
        rw [map_add, map_mul, haugμ, haugν]
        simp only [augmentation_single, mul_one]
        rw [wordExponent_mul]
        rfl

/-- The map on free abelianizations induced by a free presentation.-/
def presentationMap
    {X : Type*} (φ : FreeGroup X →* G) :
    FreeAbelianGroup X →+
      Additive (Abelianization G) :=
  (Abelianization.map φ).toAdditive

/--
@isnad1 id=eq.0h4v.s8.a34659f0e346 from=translated src=- shape=8b732f9f vocab=5bc86136
-/
@[simp]
theorem presentationMap_of
    {X : Type*} (φ : FreeGroup X →* G) (x : X) :
    presentationMap φ (FreeAbelianGroup.of x) =
      Additive.ofMul
        (Abelianization.of (φ (FreeGroup.of x))) :=
  rfl

/--
@isnad1 id=surjecti.1h3v.s7.b7b2acdb62c5 from=translated src=- shape=f8b3048e vocab=051769ef
-/
theorem presentationMap_surjective
    {X : Type*} (φ : FreeGroup X →* G)
    (hφ : Function.Surjective φ) :
    Function.Surjective (presentationMap φ) := by
  change
    ∀ a : Abelianization G,
      ∃ b : FreeAbelianGroup X,
        presentationMap φ b = Additive.ofMul a
  intro a
  refine QuotientGroup.induction_on a ?_
  intro g
  obtain ⟨w, rfl⟩ := hφ g
  exact
    ⟨Additive.ofMul (Abelianization.of w), rfl⟩

/-- The same presentation map, regarded as a `ℤ`-linear map.-/
def presentationLinearMap
    {X : Type*} (φ : FreeGroup X →* G) :
    FreeAbelianGroup X →ₗ[ℤ]
      Additive (Abelianization G) :=
  (presentationMap φ).toIntLinearMap

/--
@isnad1 id=eq.0h4v.s8.42b53dc2098a from=translated src=- shape=dbc20e6a vocab=014dbcd9
-/
@[simp]
theorem presentationLinearMap_apply
    {X : Type*} (φ : FreeGroup X →* G)
    (a : FreeAbelianGroup X) :
    presentationLinearMap φ a =
      presentationMap φ a :=
  rfl

/-- Finite abelianization makes the relation lattice of a finite free
presentation have full rank.
@isnad1 id=eq.0h3v.s8.d437c1ee3d9c from=translated src=- shape=ccc28103 vocab=b422db32
-/
theorem presentationKernel_finrank_eq
    {X : Type*} [Fintype X]
    (φ : FreeGroup X →* G)
    [FiniteIndex (commutator G)] :
    Module.finrank ℤ (presentationLinearMap φ).ker =
      Module.finrank ℤ (FreeAbelianGroup X) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  let f := presentationLinearMap φ
  let e := f.quotKerEquivRange
  let : Finite f.range :=
    Finite.of_injective
      ((↑) : f.range →
        Additive (Abelianization G))
      Subtype.coe_injective
  have ht :
      Module.IsTorsion ℤ f.range :=
    isAddTorsion_iff_isTorsion_int.mp
      isAddTorsion_of_finite
  have hrange :
      Module.finrank ℤ f.range = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr ht
  have hzero :
      Module.finrank ℤ
          ((FreeAbelianGroup X) ⧸ f.ker) = 0 :=
    e.finrank_eq.trans hrange
  change
    Module.finrank ℤ f.ker =
      Module.finrank ℤ (FreeAbelianGroup X)
  have hrank := f.ker.finrank_quotient_add_finrank
  calc
    Module.finrank ℤ f.ker =
        0 + Module.finrank ℤ f.ker := by
          rw [zero_add]
    _ = Module.finrank ℤ
          ((FreeAbelianGroup X) ⧸ f.ker) +
        Module.finrank ℤ f.ker := by
          rw [hzero]
    _ = Module.finrank ℤ (FreeAbelianGroup X) :=
      hrank

/-- A basis of the relation lattice, indexed by the generators.-/
noncomputable def relationBasis
    {X : Type*} [Fintype X]
    (φ : FreeGroup X →* G)
    [FiniteIndex (commutator G)] :
    Module.Basis X ℤ (presentationLinearMap φ).ker :=
  Submodule.smithNormalFormBotBasis
    (FreeAbelianGroup.basis X)
    (presentationKernel_finrank_eq φ)

/-- Every vector in the relation lattice is represented by an actual
relation word.  The correction from a lift to a relation is made inside
the commutator subgroup of the free group, so it does not change the
free abelianization.
@isnad1 id=ex.1h4v.s9.f0c09a015344 from=translated src=- shape=181fcaef vocab=3f7bae3b
-/
theorem exists_relationWord
    {X : Type*}
    (φ : FreeGroup X →* G)
    (hφ : Function.Surjective φ)
    (m : (presentationLinearMap φ).ker) :
    ∃ r : FreeGroup X,
      φ r = 1 ∧
      Additive.ofMul (Abelianization.of r) =
        (m : FreeAbelianGroup X) := by
  obtain ⟨w, hw⟩ :=
    QuotientGroup.mk'_surjective
      (commutator (FreeGroup X))
      (Additive.toMul (m : FreeAbelianGroup X))
  have hw' :
      Additive.ofMul (Abelianization.of w) =
        (m : FreeAbelianGroup X) :=
    congrArg Additive.ofMul hw
  have habAdd :
      Additive.ofMul
          (Abelianization.of (φ w)) = 0 := by
    calc
      Additive.ofMul
          (Abelianization.of (φ w)) =
          presentationLinearMap φ
            (Additive.ofMul
              (Abelianization.of w)) := rfl
      _ = presentationLinearMap φ
            (m : FreeAbelianGroup X) := by
              rw [hw']
      _ = 0 := m.property
  have hab :
      Abelianization.of (φ w) = 1 := by
    exact congrArg Additive.toMul habAdd
  have hφw :
      φ w ∈ commutator G :=
    (QuotientGroup.eq_one_iff (φ w)).mp hab
  have hmap :
      (commutator (FreeGroup X)).map φ =
        commutator G := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr hφ]
    rfl
  have hinv :
      (φ w)⁻¹ ∈
        (commutator (FreeGroup X)).map φ := by
    rw [hmap]
    exact (commutator G).inv_mem hφw
  obtain ⟨c, hc, hcφ⟩ := hinv
  have hcAb :
      Abelianization.of c = 1 :=
    (QuotientGroup.eq_one_iff c).mpr hc
  refine ⟨w * c, ?_, ?_⟩
  · rw [map_mul, hcφ]
    exact mul_inv_cancel _
  · rw [map_mul, ofMul_mul, hw', hcAb, ofMul_one]
    exact add_zero _

/-- The group-ring map induced by abelianization.-/
def abelianizationRingMap :
    IntegralGroupRing G →+*
      IntegralGroupRing (Abelianization G) :=
  MonoidAlgebra.mapDomainRingHom ℤ Abelianization.of

/--
@isnad1 id=eq.0h3v.s7.c3147cb89d77 from=translated src=- shape=b696d639 vocab=4f26f9e8
-/
@[simp]
theorem abelianizationRingMap_single
    (g : G) (n : ℤ) :
    abelianizationRingMap
        (MonoidAlgebra.single g n) =
      MonoidAlgebra.single (Abelianization.of g) n := by
  simp [abelianizationRingMap]

/--
@isnad1 id=eq.0h2v.s7.c5ae407bae9f from=translated src=- shape=e88f88de vocab=36ef8ec7
-/
@[simp]
theorem abelianizationRingMap_groupRingDelta
    (g : G) :
    abelianizationRingMap (groupRingDelta g) =
      groupRingDelta (Abelianization.of g) := by
  simp [groupRingDelta]

/--
@isnad1 id=eq.0h2v.s7.df19ad952a3b from=translated src=- shape=727f8552 vocab=eb6ce5f9
-/
@[simp]
theorem augmentation_abelianizationRingMap
    (x : IntegralGroupRing G) :
    augmentation (Abelianization G)
        (abelianizationRingMap x) =
      augmentation G x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      simp [MonoidAlgebra.of]
  | add x y hx hy =>
      simp [hx, hy]
  | smul n x hx =>
      simp [hx]

/-- An additive section of the group-ring abelianization map, obtained
by choosing the quotient representative of every abelianization class.-/
def abelianizationRingSection :
    IntegralGroupRing (Abelianization G) →+
      IntegralGroupRing G where
  toFun :=
    MonoidAlgebra.mapDomain
      (fun a : Abelianization G => a.out)
  map_zero' := MonoidAlgebra.mapDomain_zero _
  map_add' := MonoidAlgebra.mapDomain_add _

/--
@isnad1 id=eq.0h3v.s6.456631c81cb9 from=translated src=- shape=6d694fbf vocab=28d353d3
-/
@[simp]
theorem abelianizationRingSection_single
    (a : Abelianization G) (n : ℤ) :
    abelianizationRingSection
        (MonoidAlgebra.single a n) =
      MonoidAlgebra.single a.out n := by
  simp [abelianizationRingSection]

/--
@isnad1 id=eq.0h2v.s7.4cca4c6e6663 from=translated src=- shape=56d022f4 vocab=eceb3dfc
-/
@[simp]
theorem abelianizationRingMap_section
    (z : IntegralGroupRing (Abelianization G)) :
    abelianizationRingMap
        (abelianizationRingSection z) = z := by
  induction z using MonoidAlgebra.induction_on with
  | of a =>
      simp only [MonoidAlgebra.of_apply,
        abelianizationRingSection_single,
        abelianizationRingMap_single]
      congr 1
      exact Quotient.out_eq a
  | add x y hx hy =>
      simp [hx, hy]
  | smul n x hx =>
      simp only [map_zsmul, hx]

/-- Multiplying an element of `I_G` by an element killed by
`ℤ[G] → ℤ[Gᵃᵇ]` lands in `I_G I_{G'}`.
@isnad1 id=mem.2h3v.s8.c83c5691c6e0 from=translated src=- shape=1f36e7e4 vocab=f077c4fc
-/
theorem ideal_mul_mem_mixed_of_abelianizationRingMap_eq_zero
    (x y : IntegralGroupRing G)
    (hx : x ∈ ideal G)
    (hy : abelianizationRingMap y = 0) :
    x * y ∈
      mixedAugmentationProduct
        (commutator G) := by
  have hgeneral :
      ∀ z : IntegralGroupRing G,
        x * (z -
          abelianizationRingSection
            (abelianizationRingMap z)) ∈
          mixedAugmentationProduct
            (commutator G) := by
    intro z
    induction z using MonoidAlgebra.induction_on with
    | of g =>
        let q : Abelianization G :=
          Abelianization.of g
        let r : G := q.out
        have hrq : Abelianization.of r = q := by
          exact Quotient.out_eq q
        have hh :
            r⁻¹ * g ∈ commutator G := by
          apply
            (QuotientGroup.eq_one_iff
              (r⁻¹ * g)).mp
          change Abelianization.of (r⁻¹ * g) = 1
          rw [map_mul, map_inv, hrq]
          simp [q]
        let h : commutator G := ⟨r⁻¹ * g, hh⟩
        have hfactor :
            (MonoidAlgebra.of ℤ G g -
                abelianizationRingSection
                  (abelianizationRingMap
                    (MonoidAlgebra.of ℤ G g))) =
              MonoidAlgebra.single r 1 *
                embeddedDelta
                  (commutator G) h := by
          simp only [MonoidAlgebra.of_apply,
            abelianizationRingMap_single,
            abelianizationRingSection_single]
          rw [embeddedDelta_eq]
          simp only [deltaElement_val]
          change
            MonoidAlgebra.single g 1 -
                MonoidAlgebra.single r 1 =
              MonoidAlgebra.single r 1 *
                (MonoidAlgebra.single (r⁻¹ * g) 1 -
                  MonoidAlgebra.single 1 1)
          simp [mul_sub]
        rw [hfactor, ← mul_assoc]
        apply AddSubgroup.subset_closure
        refine
          ⟨x * MonoidAlgebra.single r 1, ?_,
            embeddedDelta
              (commutator G) h,
            embeddedDelta_mem_embeddedSubgroupIdeal
                (commutator G) h, rfl⟩
        rw [mem_ideal_iff, map_mul]
        simp [(mem_ideal_iff G x).mp hx]
    | add a b ha hb =>
        convert
          (mixedAugmentationProduct
              (commutator G)).add_mem ha hb using 1
        simp only [map_add]
        noncomm_ring
    | smul n a ha =>
        convert
          (mixedAugmentationProduct
              (commutator G)).zsmul_mem ha n using 1
        simp only [map_zsmul]
        rw [← smul_sub, Algebra.mul_smul_comm]
  have h := hgeneral y
  simpa [hy] using h

/-- The mixed product is stable under left multiplication by arbitrary
group-ring elements.
@isnad1 id=mem.1h4v.s7.f4c57d230fd2 from=translated src=- shape=85392ec1 vocab=7db9b9a9
-/
theorem mul_mem_mixed
    (H : Subgroup G)
    (z m : IntegralGroupRing G)
    (hm : m ∈ mixedAugmentationProduct H) :
    z * m ∈ mixedAugmentationProduct H := by
  rw [mixedAugmentationProduct] at hm
  refine AddSubgroup.closure_induction
    (p := fun m _ =>
      z * m ∈ mixedAugmentationProduct H)
    ?_ ?_ ?_ ?_ hm
  · rintro m ⟨x, hx, y, hy, rfl⟩
    apply AddSubgroup.subset_closure
    exact
      ⟨z * x, (ideal G).mul_mem_left z x hx,
        y, hy, (mul_assoc z x y).symm⟩
  · simp
  · intro a b _ _ ha hb
    rw [mul_add]
    exact (mixedAugmentationProduct H).add_mem ha hb
  · intro a _ ha
    rw [mul_neg]
    exact (mixedAugmentationProduct H).neg_mem ha

/-- A row vector annihilating a square matrix is annihilated by its
determinant.
@isnad1 id=eq.1h5v.s6.37f19c536693 from=translated src=- shape=54b1ece9 vocab=eb6dfba1
-/
theorem mul_det_eq_zero_of_vecMul_eq_zero
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (v : ι → R)
    (h : Matrix.vecMul v A = 0) (i : ι) :
    v i * A.det = 0 := by
  have h' :
      Matrix.vecMul (Matrix.vecMul v A)
        A.adjugate = 0 := by
    rw [h]
    simp
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate] at h'
  have hi := congrFun h' i
  simpa [Matrix.vecMul, dotProduct,
    Matrix.one_apply] using hi

section Presentation

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (φ : FreeGroup X →* G)
variable (hφ : Function.Surjective φ)
variable [FiniteIndex (commutator G)]

/-- The chosen relation word representing the corresponding relation
basis vector.-/
noncomputable def relationWord (j : X) :
    FreeGroup X :=
  (exists_relationWord φ hφ (relationBasis φ j)).choose

omit [DecidableEq X] in
/--
@isnad1 id=eq.1h4v.s7.6aec545f12ac from=translated src=- shape=396cb1a8 vocab=723b79af
-/
@[simp]
theorem relationWord_map (j : X) :
    φ (relationWord φ hφ j) = 1 :=
  (exists_relationWord φ hφ
    (relationBasis φ j)).choose_spec.1

omit [DecidableEq X] in
/--
@isnad1 id=eq.1h4v.s10.c87a9c03a439 from=translated src=- shape=613b2bf1 vocab=32fc4332
-/
theorem relationWord_abelianization (j : X) :
    Additive.ofMul
        (Abelianization.of (relationWord φ hφ j)) =
      ((relationBasis φ j :
        (presentationLinearMap φ).ker) :
          FreeAbelianGroup X) :=
  (exists_relationWord φ hφ
    (relationBasis φ j)).choose_spec.2

/-- The chosen right Fox coefficient of the `j`-th relation at the
`i`-th generator.-/
noncomputable def foxCoefficient (i j : X) :
    IntegralGroupRing G :=
  ((exists_rightFoxExpansion φ
    (relationWord φ hφ j)).choose i)

/--
@isnad1 id=eq.1h4v.s8.445dc1abcf83 from=translated src=- shape=0f4a3091 vocab=181322a8
-/
theorem foxExpansion_relation (j : X) :
    ∑ i : X,
        groupRingDelta (φ (FreeGroup.of i)) *
          foxCoefficient φ hφ i j =
      0 := by
  have h :
      groupRingDelta (φ (relationWord φ hφ j)) =
        ∑ i : X,
          groupRingDelta (φ (FreeGroup.of i)) *
            foxCoefficient φ hφ i j :=
    (exists_rightFoxExpansion φ
      (relationWord φ hφ j)).choose_spec.1
  exact h.symm.trans (by
    rw [relationWord_map, groupRingDelta_one])

/--
@isnad1 id=eq.1h5v.s7.3d891f84c749 from=translated src=- shape=283e802e vocab=0c5f69d2
-/
theorem augmentation_foxCoefficient (i j : X) :
    augmentation G (foxCoefficient φ hφ i j) =
      wordExponent (relationWord φ hφ j) i :=
  (exists_rightFoxExpansion φ
    (relationWord φ hφ j)).choose_spec.2 i

/--
@isnad1 id=eq.1h5v.s10.5e46f6f26012 from=translated src=- shape=805d2b8b vocab=7a41c324
-/
theorem augmentation_foxCoefficient_eq_repr
    (i j : X) :
    augmentation G (foxCoefficient φ hφ i j) =
      (FreeAbelianGroup.basis X).repr
        (((relationBasis φ j :
          (presentationLinearMap φ).ker) :
            FreeAbelianGroup X)) i := by
  rw [augmentation_foxCoefficient]
  unfold wordExponent
  rw [relationWord_abelianization]
  rfl

/-- Witt's relation matrix, with entries reduced to the group ring of
the finite abelianization.-/
noncomputable def foxMatrix :
    Matrix X X
      (IntegralGroupRing (Abelianization G)) :=
  fun i j =>
    abelianizationRingMap
      (foxCoefficient φ hφ i j)

/-- A chosen lift of an adjugate-matrix entry back to `ℤ[G]`.-/
noncomputable def adjugateCoefficientLift (j k : X) :
    IntegralGroupRing G :=
  abelianizationRingSection
    ((foxMatrix φ hφ).adjugate j k)

/--
@isnad1 id=eq.1h5v.s8.5f45a1201e3d from=translated src=- shape=e82cb453 vocab=2fd4e33f
-/
@[simp]
theorem abelianizationRingMap_adjugateCoefficientLift
    (j k : X) :
    abelianizationRingMap
        (adjugateCoefficientLift φ hφ j k) =
      (foxMatrix φ hφ).adjugate j k :=
  abelianizationRingMap_section _

/-- A chosen lift of the determinant.-/
noncomputable def foxDeterminantLift :
    IntegralGroupRing G :=
  abelianizationRingSection (foxMatrix φ hφ).det

/--
@isnad1 id=eq.1h3v.s8.e5692b27860c from=translated src=- shape=cf6f6fe5 vocab=47f98ff2
-/
@[simp]
theorem abelianizationRingMap_foxDeterminantLift :
    abelianizationRingMap
        (foxDeterminantLift φ hφ) =
      (foxMatrix φ hφ).det :=
  abelianizationRingMap_section _

/-- The coefficients obtained by multiplying the Fox matrix by a lift
of its adjugate.-/
noncomputable def foxAdjugateCoefficient (i k : X) :
    IntegralGroupRing G :=
  ∑ j : X,
    foxCoefficient φ hφ i j *
      adjugateCoefficientLift φ hφ j k

/--
@isnad1 id=eq.1h5v.s8.fdf86bc65efa from=translated src=- shape=2dde22a1 vocab=8a098ab7
-/
theorem abelianizationRingMap_foxAdjugateCoefficient
    (i k : X) :
    abelianizationRingMap
        (foxAdjugateCoefficient φ hφ i k) =
      if i = k then (foxMatrix φ hφ).det else 0 := by
  calc
    abelianizationRingMap
        (foxAdjugateCoefficient φ hφ i k) =
        ∑ j : X,
          foxMatrix φ hφ i j *
            (foxMatrix φ hφ).adjugate j k := by
      simp [foxAdjugateCoefficient, foxMatrix]
    _ = ((foxMatrix φ hφ) *
          (foxMatrix φ hφ).adjugate) i k := by
      rw [Matrix.mul_apply]
    _ = if i = k then
          (foxMatrix φ hφ).det else 0 := by
      rw [Matrix.mul_adjugate]
      simp [Matrix.one_apply]

/--
@isnad1 id=eq.1h4v.s8.9b69279b3825 from=translated src=- shape=0f4a3091 vocab=b3b43962
-/
theorem foxAdjugate_relation (k : X) :
    ∑ i : X,
        groupRingDelta (φ (FreeGroup.of i)) *
          foxAdjugateCoefficient φ hφ i k =
      0 := by
  simp only [foxAdjugateCoefficient,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  simp [foxExpansion_relation]

/--
@isnad1 id=mem.1h4v.s8.17f086f59315 from=translated src=- shape=d2625536 vocab=1a7492a7
-/
theorem generator_mul_foxDeterminantLift_mem_mixed
    (k : X) :
    groupRingDelta (φ (FreeGroup.of k)) *
        foxDeterminantLift φ hφ ∈
      mixedAugmentationProduct (commutator G) := by
  let error : X → IntegralGroupRing G :=
    fun i =>
      foxAdjugateCoefficient φ hφ i k -
        if i = k then
          foxDeterminantLift φ hφ else 0
  have herrMap (i : X) :
      abelianizationRingMap (error i) = 0 := by
    dsimp [error]
    by_cases hik : i = k
    · subst i
      rw [ite_eq_left rfl]
      rw [map_sub,
        abelianizationRingMap_foxAdjugateCoefficient,
        ite_eq_left rfl,
        abelianizationRingMap_foxDeterminantLift,
        sub_self]
    · rw [ite_eq_right hik]
      rw [map_sub,
        abelianizationRingMap_foxAdjugateCoefficient,
        ite_eq_right hik, map_zero, sub_zero]
  have hdelta (i : X) :
      groupRingDelta (φ (FreeGroup.of i)) ∈
        ideal G := by
    rw [mem_ideal_iff]
    exact augmentation_groupRingDelta _
  have herr (i : X) :
      groupRingDelta (φ (FreeGroup.of i)) *
          error i ∈
        mixedAugmentationProduct (commutator G) :=
    ideal_mul_mem_mixed_of_abelianizationRingMap_eq_zero
      _ _ (hdelta i) (herrMap i)
  have hsum :
      ∑ i : X,
          groupRingDelta (φ (FreeGroup.of i)) *
            error i ∈
        mixedAugmentationProduct (commutator G) :=
    AddSubgroup.sum_mem _ (fun i _ => herr i)
  have hdiag :
      ∑ i : X,
          groupRingDelta (φ (FreeGroup.of i)) *
            (if i = k then
              foxDeterminantLift φ hφ else 0) =
        groupRingDelta (φ (FreeGroup.of k)) *
          foxDeterminantLift φ hφ := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [hik]
    · simp
  have heq :
      ∑ i : X,
          groupRingDelta (φ (FreeGroup.of i)) *
            error i =
        -(groupRingDelta (φ (FreeGroup.of k)) *
          foxDeterminantLift φ hφ) := by
    simp only [error, mul_sub,
      Finset.sum_sub_distrib]
    rw [foxAdjugate_relation, hdiag]
    exact zero_sub _
  have hneg :
      -(groupRingDelta (φ (FreeGroup.of k)) *
          foxDeterminantLift φ hφ) ∈
        mixedAugmentationProduct (commutator G) := by
    rw [← heq]
    exact hsum
  have :=
    (mixedAugmentationProduct
      (commutator G)).neg_mem hneg
  simpa using this

/--
@isnad1 id=eq.1h3v.s8.e449f3d4f58c from=translated src=- shape=064467a3 vocab=62fb99ce
-/
theorem delta_vecMul_foxMatrix :
    Matrix.vecMul
        (fun i : X =>
          groupRingDelta
            (Abelianization.of
              (φ (FreeGroup.of i))))
        (foxMatrix φ hφ) =
      0 := by
  funext j
  have h :=
    congrArg abelianizationRingMap
      (foxExpansion_relation φ hφ j)
  simpa [Matrix.vecMul, dotProduct, foxMatrix,
    map_sum] using h

/--
@isnad1 id=eq.1h4v.s8.091b0a7fc0ee from=translated src=- shape=43cd53d8 vocab=d64a6175
-/
theorem delta_generator_mul_foxMatrix_det (i : X) :
    groupRingDelta
          (Abelianization.of
            (φ (FreeGroup.of i))) *
        (foxMatrix φ hφ).det =
      0 :=
  mul_det_eq_zero_of_vecMul_eq_zero
    (foxMatrix φ hφ)
    (fun k : X =>
      groupRingDelta
        (Abelianization.of
          (φ (FreeGroup.of k))))
    (delta_vecMul_foxMatrix φ hφ) i

/--
@isnad1 id=eq.1h4v.s8.a8b916ac209d from=translated src=- shape=0655807f vocab=8376fee2
-/
theorem delta_word_mul_foxMatrix_det
    (w : FreeGroup X) :
    groupRingDelta
          (Abelianization.of (φ w)) *
        (foxMatrix φ hφ).det =
      0 := by
  induction w using FreeGroup.induction_on with
  | one =>
      simp
  | of i =>
      exact delta_generator_mul_foxMatrix_det φ hφ i
  | inv_of i hi =>
      rw [map_inv, map_inv, groupRingDelta_inv]
      calc
        groupRingDelta
              (Abelianization.of
                (φ (FreeGroup.of i))) *
            (-MonoidAlgebra.single
              (Abelianization.of
                (φ (FreeGroup.of i)))⁻¹ 1) *
            (foxMatrix φ hφ).det =
            (groupRingDelta
                (Abelianization.of
                  (φ (FreeGroup.of i))) *
              (foxMatrix φ hφ).det) *
              (-MonoidAlgebra.single
                (Abelianization.of
                  (φ (FreeGroup.of i)))⁻¹ 1) := by
                  ac_rfl
        _ = 0 := by rw [hi, zero_mul]
  | mul u v hu hv =>
      rw [map_mul, map_mul, groupRingDelta_mul,
        add_mul]
      calc
        (groupRingDelta
              (Abelianization.of (φ u)) *
              MonoidAlgebra.single
                (Abelianization.of (φ v)) 1) *
              (foxMatrix φ hφ).det +
            groupRingDelta
                (Abelianization.of (φ v)) *
              (foxMatrix φ hφ).det =
            (groupRingDelta
                (Abelianization.of (φ u)) *
              (foxMatrix φ hφ).det) *
                MonoidAlgebra.single
                  (Abelianization.of (φ v)) 1 +
              groupRingDelta
                  (Abelianization.of (φ v)) *
                (foxMatrix φ hφ).det := by
                  congr 1
                  ac_rfl
        _ = 0 := by rw [hu, hv, zero_mul, zero_add]

/--
@isnad1 id=eq.1h4v.s8.cb01c3545e9e from=translated src=- shape=9bdd1b05 vocab=99482cef
-/
theorem delta_mul_foxMatrix_det
    (a : Abelianization G) :
    groupRingDelta a * (foxMatrix φ hφ).det =
      0 := by
  refine QuotientGroup.induction_on a ?_
  intro g
  obtain ⟨w, rfl⟩ := hφ g
  exact delta_word_mul_foxMatrix_det φ hφ w

/--
@isnad1 id=eq.1h4v.s7.8a8b77b981f7 from=translated src=- shape=9836a5c9 vocab=f92a7666
-/
theorem single_mul_foxMatrix_det
    (a : Abelianization G) :
    MonoidAlgebra.single a 1 *
        (foxMatrix φ hφ).det =
      (foxMatrix φ hφ).det := by
  have h := delta_mul_foxMatrix_det φ hφ a
  rw [groupRingDelta, sub_mul,
    ← MonoidAlgebra.one_def, one_mul] at h
  exact sub_eq_zero.mp h

/--
@isnad1 id=eq.1h3v.s10.f676e5a5b29d from=translated src=- shape=f6a76582 vocab=0a1dadca
-/
theorem augmentation_foxMatrix_det :
    augmentation (Abelianization G)
        (foxMatrix φ hφ).det =
      (FreeAbelianGroup.basis X).det
        (fun j : X =>
          (((relationBasis φ j :
            (presentationLinearMap φ).ker) :
              FreeAbelianGroup X))) := by
  calc
    augmentation (Abelianization G)
        (foxMatrix φ hφ).det =
        (RingHom.mapMatrix
          (augmentation (Abelianization G))
          (foxMatrix φ hφ)).det :=
      RingHom.map_det
        (augmentation (Abelianization G))
        (foxMatrix φ hφ)
    _ = (FreeAbelianGroup.basis X).det
        (fun j : X =>
          (((relationBasis φ j :
            (presentationLinearMap φ).ker) :
              FreeAbelianGroup X))) := by
      rw [Module.Basis.det_apply]
      congr 1
      ext i j
      simp [foxMatrix, Module.Basis.toMatrix_apply,
        augmentation_foxCoefficient_eq_repr]

/--
@isnad1 id=eq.1h3v.s7.8407e78620bb from=translated src=- shape=e08c8d26 vocab=d2268657
-/
theorem natAbs_augmentation_foxMatrix_det :
    Int.natAbs
        (augmentation (Abelianization G)
          (foxMatrix φ hφ).det) =
      Nat.card (Abelianization G) := by
  rw [augmentation_foxMatrix_det]
  calc
    Int.natAbs
        ((FreeAbelianGroup.basis X).det
          (fun j : X =>
            (((relationBasis φ j :
              (presentationLinearMap φ).ker) :
                FreeAbelianGroup X)))) =
        Nat.card
          ((FreeAbelianGroup X) ⧸
            (presentationLinearMap φ).ker) :=
      Submodule.natAbs_det_basis_change
        (FreeAbelianGroup.basis X)
        (presentationLinearMap φ).ker
        (relationBasis φ)
    _ = Nat.card
          (Additive (Abelianization G)) := by
      exact Nat.card_congr
        ((presentationLinearMap φ).quotKerEquivOfSurjective
          (presentationMap_surjective φ hφ)).toEquiv
    _ = Nat.card (Abelianization G) := rfl

end Presentation

/-- The norm element of a finite group.-/
def groupNormElement
    (Q : Type*) [Group Q] [Finite Q] :
    IntegralGroupRing Q :=
  letI := Fintype.ofFinite Q
  ∑ q : Q, MonoidAlgebra.single q 1

/--
@isnad1 id=eq.0h1v.s6.1d7b63b4e0ff from=translated src=- shape=ce717c5b vocab=666acfa5
-/
@[simp]
theorem augmentation_groupNormElement
    (Q : Type*) [Group Q] [Finite Q] :
    augmentation Q (groupNormElement Q) =
      Nat.card Q := by
  let := Fintype.ofFinite Q
  simp [groupNormElement, Nat.card_eq_fintype_card]

/-- The image in the abelianized group ring of the sum of any left
transversal is the norm element of the abelianization.
@isnad1 id=eq.0h2v.s7.864e00fbd464 from=translated src=- shape=a291c88b vocab=e3ccaf18
-/
theorem abelianizationRingMap_transversalNormElement
    [FiniteIndex (commutator G)]
    (T : (commutator G).LeftTransversal) :
    abelianizationRingMap
        (transversalNormElement (commutator G) T) =
      groupNormElement (Abelianization G) := by
  let := (commutator G).fintypeQuotientOfFiniteIndex
  unfold transversalNormElement groupNormElement
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [abelianizationRingMap_single]
  congr 2
  exact T.2.leftQuotientEquiv.symm_apply_apply q

/-- A left-translation invariant element of a finite group ring is a
scalar multiple of the norm element.-/
theorem eq_coeff_one_smul_groupNormElement
    {Q : Type*} [Group Q] [Fintype Q]
    (z : IntegralGroupRing Q)
    (hz : ∀ q : Q,
      MonoidAlgebra.single q 1 * z = z) :
    z = z.coeff 1 • groupNormElement Q := by
  classical
  ext q
  have hq :=
    congrArg (fun x : IntegralGroupRing Q =>
      x.coeff q) (hz q)
  have hcoeff : z.coeff q = z.coeff 1 := by
    simpa using hq.symm
  show
    z.coeff q =
      z.coeff 1 * (groupNormElement Q).coeff q
  rw [hcoeff]
  simp [groupNormElement]

section PresentationNorm

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (φ : FreeGroup X →* G)
variable (hφ : Function.Surjective φ)
variable [FiniteIndex (commutator G)]

/-- Witt's determinant is a unit multiple of the norm element of the
finite abelianization.
@isnad1 id=ex.1h3v.s7.36ae701aa888 from=translated src=- shape=cada3c87 vocab=50eebf55
-/
theorem exists_unit_foxMatrix_det_eq_smul_norm :
    ∃ u : ℤˣ,
      (foxMatrix φ hφ).det =
        (u : ℤ) •
          groupNormElement (Abelianization G) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  let d := (foxMatrix φ hφ).det
  let c := d.coeff 1
  have hd :
      d = c • groupNormElement (Abelianization G) :=
    eq_coeff_one_smul_groupNormElement d
      (single_mul_foxMatrix_det φ hφ)
  have haug :
      augmentation (Abelianization G) d =
        c * (Fintype.card
          (Abelianization G) : ℤ) := by
    have h := congrArg
      (augmentation (Abelianization G)) hd
    simpa [c] using h
  have hnat :
      Int.natAbs
          (augmentation (Abelianization G) d) =
        Fintype.card (Abelianization G) := by
    simpa [d, Nat.card_eq_fintype_card] using
      natAbs_augmentation_foxMatrix_det φ hφ
  have hcprod :
      Int.natAbs c *
          Fintype.card (Abelianization G) =
        Fintype.card (Abelianization G) := by
    calc
      Int.natAbs c *
          Fintype.card (Abelianization G) =
          Int.natAbs
            (c * (Fintype.card
              (Abelianization G) : ℤ)) := by
                simpa only [Int.natAbs_natCast] using
                  (Int.natAbs_mul c
                    (Fintype.card
                      (Abelianization G) : ℤ)).symm
      _ = Int.natAbs
          (augmentation (Abelianization G) d) := by
            rw [haug]
      _ = Fintype.card (Abelianization G) :=
        hnat
  have hcard :
      0 < Fintype.card (Abelianization G) :=
    Fintype.card_pos
  have hcabs : Int.natAbs c = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hcard
    simpa using hcprod
  obtain ⟨u, hu⟩ :=
    (Int.isUnit_iff_natAbs_eq.mpr hcabs)
  refine ⟨u, ?_⟩
  simpa only [d, hu] using hd

/--
@isnad1 id=ex.1h3v.s8.4e29cf9b2a63 from=translated src=- shape=05b052ce vocab=83cd19c6
-/
theorem exists_unit_foxDeterminantLift_eq_smul_section_norm :
    ∃ u : ℤˣ,
      foxDeterminantLift φ hφ =
        (u : ℤ) •
          abelianizationRingSection
            (groupNormElement (Abelianization G)) := by
  obtain ⟨u, hu⟩ :=
    exists_unit_foxMatrix_det_eq_smul_norm φ hφ
  refine ⟨u, ?_⟩
  unfold foxDeterminantLift
  rw [hu, map_zsmul]

include hφ in
/--
@isnad1 id=mem.1h4v.s8.669ba620b633 from=translated src=- shape=578b882c vocab=8ccef027
-/
theorem generator_mul_section_norm_mem_mixed
    (k : X) :
    groupRingDelta (φ (FreeGroup.of k)) *
        abelianizationRingSection
          (groupNormElement (Abelianization G)) ∈
      mixedAugmentationProduct (commutator G) := by
  obtain ⟨u, hu⟩ :=
    exists_unit_foxDeterminantLift_eq_smul_section_norm
      φ hφ
  let S : IntegralGroupRing G :=
    abelianizationRingSection
      (groupNormElement (Abelianization G))
  change
    groupRingDelta (φ (FreeGroup.of k)) * S ∈
      mixedAugmentationProduct (commutator G)
  have hm :=
    generator_mul_foxDeterminantLift_mem_mixed
      φ hφ k
  have hrepl :
      groupRingDelta (φ (FreeGroup.of k)) *
          foxDeterminantLift φ hφ =
        (u : ℤ) •
          (groupRingDelta (φ (FreeGroup.of k)) * S) := by
    rw [hu]
    exact Algebra.mul_smul_comm
      (u : ℤ)
      (groupRingDelta (φ (FreeGroup.of k))) S
  have hmScalar :
      (u : ℤ) •
          (groupRingDelta (φ (FreeGroup.of k)) *
            S) ∈
        mixedAugmentationProduct (commutator G) := by
    rw [← hrepl]
    exact hm
  have hmTwice :=
    (mixedAugmentationProduct
      (commutator G)).zsmul_mem hmScalar (u : ℤ)
  have huu : (u : ℤ) * (u : ℤ) = 1 := by
    rw [← pow_two]
    exact Int.isUnit_sq u.isUnit
  have htwice :
      (u : ℤ) •
          ((u : ℤ) •
            (groupRingDelta (φ (FreeGroup.of k)) * S)) =
        groupRingDelta (φ (FreeGroup.of k)) * S := by
    rw [smul_smul, huu, one_smul]
  rw [← htwice]
  exact hmTwice

include hφ in
/--
@isnad1 id=mem.1h4v.s8.ec59e092797a from=translated src=- shape=0f60187e vocab=bdffb331
-/
theorem word_mul_section_norm_mem_mixed
    (w : FreeGroup X) :
    groupRingDelta (φ w) *
        abelianizationRingSection
          (groupNormElement (Abelianization G)) ∈
      mixedAugmentationProduct (commutator G) := by
  let S : IntegralGroupRing G :=
    abelianizationRingSection
      (groupNormElement (Abelianization G))
  change
    groupRingDelta (φ w) * S ∈
      mixedAugmentationProduct (commutator G)
  induction w using FreeGroup.induction_on with
  | one =>
      simp
  | of k =>
      exact generator_mul_section_norm_mem_mixed
        φ hφ k
  | inv_of k hk =>
      rw [map_inv, groupRingDelta_inv_left,
        mul_assoc]
      exact mul_mem_mixed (commutator G)
        (-MonoidAlgebra.single
          (φ (FreeGroup.of k))⁻¹ 1)
        (groupRingDelta (φ (FreeGroup.of k)) * S) hk
  | mul u v hu hv =>
      rw [map_mul, groupRingDelta_mul_left,
        add_mul, mul_assoc]
      exact
        (mixedAugmentationProduct
          (commutator G)).add_mem
            (mul_mem_mixed (commutator G)
              (MonoidAlgebra.single (φ u) 1)
              (groupRingDelta (φ v) * S) hv)
            hu

include hφ in
/--
@isnad1 id=mem.1h4v.s8.585530cf0adc from=translated src=- shape=e429f087 vocab=bdffb331
-/
theorem delta_mul_section_norm_mem_mixed
    (g : G) :
    groupRingDelta g *
        abelianizationRingSection
          (groupNormElement (Abelianization G)) ∈
      mixedAugmentationProduct (commutator G) := by
  obtain ⟨w, rfl⟩ := hφ g
  exact word_mul_section_norm_mem_mixed φ hφ w

include hφ in
/--
@isnad1 id=mem.1h5v.s7.d71c1c5c7a3c from=translated src=- shape=bb48c25c vocab=f72205ee
-/
theorem delta_mul_transversalNormElement_mem_mixed
    (T : (commutator G).LeftTransversal) (g : G) :
    groupRingDelta g *
        transversalNormElement (commutator G) T ∈
      mixedAugmentationProduct (commutator G) := by
  let S : IntegralGroupRing G :=
    abelianizationRingSection
      (groupNormElement (Abelianization G))
  let N : IntegralGroupRing G :=
    transversalNormElement (commutator G) T
  have hδ : groupRingDelta g ∈ ideal G := by
    rw [mem_ideal_iff]
    exact augmentation_groupRingDelta g
  have hker :
      abelianizationRingMap (N - S) = 0 := by
    simp only [map_sub, N, S,
      abelianizationRingMap_transversalNormElement,
      abelianizationRingMap_section, sub_self]
  have hdiff :
      groupRingDelta g * (N - S) ∈
        mixedAugmentationProduct (commutator G) :=
    ideal_mul_mem_mixed_of_abelianizationRingMap_eq_zero
      (groupRingDelta g) (N - S) hδ hker
  have hsection :
      groupRingDelta g * S ∈
        mixedAugmentationProduct (commutator G) :=
    delta_mul_section_norm_mem_mixed φ hφ g
  convert
    (mixedAugmentationProduct (commutator G)).add_mem
      hdiff hsection using 1
  noncomm_ring

end PresentationNorm

end Witt
end Transfer
end GroupTheory
