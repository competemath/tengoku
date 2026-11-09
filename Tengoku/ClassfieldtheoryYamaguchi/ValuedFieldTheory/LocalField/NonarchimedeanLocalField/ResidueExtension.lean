/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.Seed.FieldTheory.Finite.GaloisField
import Tengoku.Seed.LinearAlgebra.Dimension.DivisionRing
import Tengoku.Seed.NumberTheory.RamificationInertia.Inertia
import Tengoku.Seed.NumberTheory.RamificationInertia.Ramification
import Tengoku.Seed.RingTheory.Ideal.Norm.AbsNorm
import Tengoku.Seed.RingTheory.RamificationInertia.Basic
import Tengoku.Seed.RingTheory.SimpleModule.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.IntegralClosure
import Tengoku.Seed.RingTheory.Trace.Basic
import Tengoku.Seed.RingTheory.Valuation.Extension
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The local-ring homomorphism on valuation integer rings induced by an extension
of valuations.-/
def integerRingMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K] →+* 𝒪[L] :=
  algebraMap 𝒪[K] 𝒪[L]

/-- The map of valuation rings induced by a valued-field extension is a local ring homomorphism.
@isnad1 id=islocalh.0h2v.s10.455d95e29894 from=translated src=- shape=ab77e33c vocab=d53b29cc
-/
instance integerRingMapOfValuationExtension_isLocalHom (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IsLocalHom (integerRingMapOfValuationExtension K L) := by
  change IsLocalHom (algebraMap 𝒪[K] 𝒪[L])
  infer_instance

/-- The valuation-ring map of an extension is the ambient algebra map on underlying elements.
@isnad1 id=eq.0h3v.s11.f2f734e4a28a from=translated src=- shape=3120632f vocab=9b42aaf2
-/
@[simp]
theorem integerRingMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    integerRingMapOfValuationExtension K L x = algebraMap 𝒪[K] 𝒪[L] x :=
  rfl

/-- The residue-field map induced by a valuation extension.  This is the
canonical `algebraMap 𝓀[K] 𝓀[L]`, named so later
local class field theory files can use it without unfolding mathlib's valuation-extension instances.-/
def residueFieldMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[K] →+* 𝓀[L] :=
  IsLocalRing.ResidueField.map (integerRingMapOfValuationExtension K L)

/-- The map between residue fields induced by a valued extension agrees with the residue-field
algebra map.
@isnad1 id=eq.0h2v.s11.eac4fd88f6e4 from=translated src=- shape=448aaf62 vocab=efd6e210
-/
theorem residueFieldMapOfValuationExtension_eq_algebraMap (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    residueFieldMapOfValuationExtension K L = algebraMap 𝓀[K] 𝓀[L] :=
  rfl

/-- The residue-field map sends the residue of a base integer to the residue of its image in the
extension.
@isnad1 id=eq.0h3v.s13.dff186c41249 from=translated src=- shape=8cf5e260 vocab=666cb5fc
-/
@[simp]
theorem residueFieldMapOfValuationExtension_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (integerRingMapOfValuationExtension K L x) :=
  rfl

/-- The residue-field algebra map commutes with reduction of valuation-ring elements.
@isnad1 id=eq.0h3v.s13.c3a288445723 from=translated src=- shape=5f8b5429 vocab=6ba36b09
-/
@[simp]
theorem residueField_algebraMap_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) :=
  rfl

/-- The induced map on residue-field unit groups.-/
def residueUnitsMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[K]ˣ →* 𝓀[L]ˣ :=
  Units.map (residueFieldMapOfValuationExtension K L)

/-- The induced map on residue-field units applies the residue-field extension map to the underlying
residue.
@isnad1 id=eq.0h3v.s14.0437abc63c1f from=translated src=- shape=c4ec7c2b vocab=26539831
-/
@[simp]
theorem residueUnitsMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝓀[K]ˣ) :
    ((residueUnitsMapOfValuationExtension K L u : 𝓀[L]ˣ) : 𝓀[L]) =
      algebraMap 𝓀[K] 𝓀[L] (u : 𝓀[K]) :=
  rfl

/-- The induced map on residue-field unit groups is injective.
@isnad1 id=injectiv.0h2v.s13.d9f15d7440fc from=translated src=- shape=93d607ee vocab=578e06c6
-/
theorem residueUnitsMapOfValuationExtension_injective (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Injective (residueUnitsMapOfValuationExtension K L) :=
  Units.map_injective (RingHom.injective (residueFieldMapOfValuationExtension K L))

/-- Base integer units embedded into extension integer units.-/
def integerUnitsMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K]ˣ →* 𝒪[L]ˣ :=
  Units.map (integerRingMapOfValuationExtension K L).toMonoidHom

/-- The induced map on valuation-ring units applies the extension's integer-ring map to the
underlying unit.
@isnad1 id=eq.0h3v.s12.6817df4cc304 from=translated src=- shape=b49f73e8 vocab=a1669855
-/
@[simp]
theorem integerUnitsMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    ((integerUnitsMapOfValuationExtension K L u : 𝒪[L]ˣ) : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (u : 𝒪[K]) :=
  rfl

/-- Mapping an integer unit to the extension and then reducing agrees with reducing first and
mapping residue units.
@isnad1 id=eq.0h3v.s14.b64c241124b3 from=translated src=- shape=e09d6195 vocab=1064cff7
-/
@[simp]
theorem residueUnitsMap_integerUnitsToResidueUnits (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    residueUnitsMapOfValuationExtension K L (integerUnitsToResidueUnits K u) =
      integerUnitsToResidueUnits L (integerUnitsMapOfValuationExtension K L u) := by
  ext
  rfl

/-- A first principal unit remains a first principal unit after extension of valued fields.
@isnad1 id=mem.1h3v.s13.fee8f19e468a from=translated src=- shape=c0dfc6df vocab=ed199a2b
-/
theorem integerUnitsMapOfValuationExtension_mem_principalUnits_one (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K 1) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L 1 := by
  rw [← integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one L]
  rw [← residueUnitsMap_integerUnitsToResidueUnits K L u]
  rw [(integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K u).2 hu]
  exact map_one (residueUnitsMapOfValuationExtension K L)

/-- The map on integer-unit residue quotients induced by a valuation extension.-/
def integerUnitsModPrincipalUnitsMapOfValuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IntegerUnitsModPrincipalUnits K →* IntegerUnitsModPrincipalUnits L :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk L).comp
      (integerUnitsMapOfValuationExtension K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      exact integerUnitsMapOfValuationExtension_mem_principalUnits_one K L u hu)

/-- The map modulo first principal units sends a class to the class of the extended integer unit.
@isnad1 id=eq.0h3v.s13.3f846f195794 from=translated src=- shape=dfe46d7e vocab=4310fc36
-/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfValuationExtension_mk (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsMk K u) =
      integerUnitsModPrincipalUnitsMk L
        (integerUnitsMapOfValuationExtension K L u) :=
  rfl

/-- The residue-field norm transported to the integer-unit quotients
`𝒪[L]ˣ/U_L¹ → 𝒪[K]ˣ/U_K¹`.

This is not the local field norm on integer units; it is the quotient-level
residue norm model used before proving compatibility with `normIntegerUnits`.-/
def integerUnitsModPrincipalUnitsResidueNormOfValuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  (integerUnitsModPrincipalUnitsEquivResidueUnits K).symm.toMonoidHom.comp
    ((Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))).comp
      (integerUnitsModPrincipalUnitsEquivResidueUnits L).toMonoidHom)

/-- The residue norm on classes modulo first principal units agrees with the finite residue-field
norm.
@isnad1 id=eq.0h3v.s13.7b2e0f33a248 from=translated src=- shape=dc305e2e vocab=1dfcf3a6
-/
theorem integerUnitsModPrincipalUnitsResidueNorm_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : IntegerUnitsModPrincipalUnits L) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x) := by
  change
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        ((integerUnitsModPrincipalUnitsEquivResidueUnits K).symm
          (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x))) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x)
  exact (integerUnitsModPrincipalUnitsEquivResidueUnits K).apply_symm_apply _

/-- The finite-field residue norm, after base extension to `𝓀[L]`, is the
product over all residue-field automorphisms.
@isnad1 id=eq.0h3v.s15.ec6fa2bce626 from=translated src=- shape=f979e702 vocab=ce8bf745
-/
theorem residueUnitsMap_residueField_norm_eq_prod_algEquiv (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝓀[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])) u) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv u) := by
  ext
  change algebraMap 𝓀[K] 𝓀[L] (Algebra.norm 𝓀[K] (u : 𝓀[L])) =
    ↑(Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u))
  rw [Algebra.norm_eq_prod_automorphisms]
  simp

/-- Quotient-level form of
`residueUnitsMap_residueField_norm_eq_prod_algEquiv`.
@isnad1 id=eq.0h3v.s15.80cad6b30a78 from=translated src=- shape=08334bc7 vocab=11e73219
-/
theorem integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact residueUnitsMap_residueField_norm_eq_prod_algEquiv K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits L x)

/-- The residue-field automorphism group has order the finite residue-field
extension degree.
@isnad1 id=eq.0h2v.s11.4fef358afb7e from=translated src=- shape=3b65c57c vocab=842ead89
-/
theorem residueAlgEquiv_card_eq_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank 𝓀[K] 𝓀[L] :=
  IsGalois.card_aut_eq_finrank (F := 𝓀[K]) (E := 𝓀[L])

/-- The mathlib inertia degree of the maximal ideals agrees with the concrete
degree of the canonical residue-field extension supplied by a valuation
extension.
@isnad1 id=eq.0h2v.s11.c1413b5b46ab from=translated src=- shape=51a6e854 vocab=1065519a
-/
theorem maximalIdeal_inertiaDeg_eq_residue_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
      Module.finrank 𝓀[K] 𝓀[L] := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])]
  rfl

/-- Finite separable extensions whose valuation ring is the integral closure of
the base valuation ring give a finite module extension of valuation integer
rings.
@isnad1 id=finite.0h2v.s10.20c8b7c0a6b1 from=translated src=- shape=ce2b7731 vocab=0aa412ec
-/
theorem integerRing_moduleFinite_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Module.Finite 𝒪[K] 𝒪[L] :=
  IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]

/-- The actual ramification index and inertia degree of the valuation-integer
ring extension satisfy the local ramification identity.
@isnad1 id=eq.0h2v.s11.5dbbe02952bf from=translated src=- shape=1bd65c74 vocab=48d15afc
-/
theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
        Module.finrank K L := by
  classical
  have := FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  have hp := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hprimes := IsLocalRing.primesOver_eq (A := 𝒪[L]) hp
  have hq (q : (𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :
      (q : Ideal 𝒪[L]) = 𝓂[L] :=
    Set.mem_singleton_iff.mp (hprimes ▸ q.property)
  let : Unique ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :=
    { default := ⟨𝓂[L], hprimes ▸ Set.mem_singleton _⟩
      uniq := fun q => Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L]
  simpa only [Fintype.sum_unique, hq] using
    (Ideal.sum_ramification_inertia_eq_finrank (𝓂[K] : Ideal 𝒪[K]) 𝒪[L])

/-- The local ramification identity with the inertia degree rewritten as the
finite-dimensional degree of the canonical residue-field extension.
@isnad1 id=eq.0h2v.s11.c6b4b0626441 from=translated src=- shape=7b866c45 vocab=de4bbe6c
-/
theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L := by
  rw [← maximalIdeal_inertiaDeg_eq_residue_finrank K L]
  exact maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K L

/-- The residue-field extension supplied by a local-field valuation extension is separable.
@isnad1 id=issepara.0h2v.s10.53280ece66f5 from=translated src=- shape=ec9c7c35 vocab=999b903e
-/
theorem residueFieldAlgebra_isSeparable_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Algebra.IsSeparable 𝓀[K] 𝓀[L] := by
  infer_instance

/-- The trace map for the canonical residue-field extension supplied by a
valuation extension is surjective.
@isnad1 id=surjecti.0h2v.s13.497d58c7ee87 from=translated src=- shape=1a5fb673 vocab=fec60ae8
-/
theorem residueField_trace_surjective_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Algebra.trace 𝓀[K] 𝓀[L]) := by
  let : Algebra.IsSeparable 𝓀[K] 𝓀[L] :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  exact Algebra.trace_surjective 𝓀[K] 𝓀[L]

/-- The finite-field norm on residue-field units is surjective for the canonical
residue extension induced by a valuation extension.
@isnad1 id=surjecti.0h2v.s13.fc99882a0868 from=translated src=- shape=3f73df13 vocab=82301edc
-/
theorem residueField_units_norm_surjective_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))) := by
  let := Fintype.ofFinite 𝓀[K]
  exact FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L]

/-- The residue norm on integer units modulo first principal units is surjective.
@isnad1 id=surjecti.0h2v.s8.9f14802d76cc from=translated src=- shape=c1703e93 vocab=f7689c4e
-/
theorem integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L) := by
  intro y
  obtain ⟨v, hv⟩ := residueField_units_norm_surjective_of_valuationExtension K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits K y)
  refine ⟨(integerUnitsModPrincipalUnitsEquivResidueUnits L).symm v, ?_⟩
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact (congrArg (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])))
    ((integerUnitsModPrincipalUnitsEquivResidueUnits L).apply_symm_apply v)).trans hv

end
end LocalFieldTheory
