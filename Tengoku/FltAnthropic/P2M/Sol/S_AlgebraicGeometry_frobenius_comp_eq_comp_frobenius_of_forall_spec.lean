import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec

set_option autoImplicit false

namespace Ws23
namespace FrobNat

open AlgebraicGeometry CategoryTheory

universe u

/--
@isnad1 id=eq.3h10v.s9.6a8dc5bf3651 from=translated src=- shape=aae1f7cf vocab=5fe522c2
-/
theorem piece (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) {R : CommRingCat.{0}} (ι : Spec R ⟶ X) :
    ι ≫ (FX ≫ g) = ι ≫ (g ≫ FY) := by

  letI : Algebra (ZMod p) R := (Spec.preimage (ι ≫ fX)).hom.toAlgebra
  have hx : ι ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) R)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  by_cases hR : Nontrivial R
  · haveI : CharP R p := charP_of_injective_algebraMap (algebraMap (ZMod p) R).injective p
    have h1 := hFX R ι hx
    have h2 := hFY R (ι ≫ g) (by rw [Category.assoc, hg, hx])
    rw [← Category.assoc, ← h1, Category.assoc, h2, Category.assoc]
  ·
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    haveI : IsEmpty ↥(Spec R) := by
      show IsEmpty (PrimeSpectrum R)
      infer_instance
    exact (isInitialOfIsEmpty (X := Spec R)).hom_ext _ _

/--
@isnad1 id=eq.5h8v.s9.cf4e90f5ec6f from=translated src=- shape=adc41053 vocab=90839eb0
-/
theorem main (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (hFXb : FX ≫ fX = fX) (hFYb : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY :=
  Scheme.Cover.hom_ext X.affineCover _ _ fun j => piece p fX fY FX FY hFX hFY g hg (X.affineCover.f j)

end Ws23.FrobNat

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=eq.5h8v.s9.cf4e90f5ec6f from=translated src=- shape=adc41053 vocab=90839eb0
-/
theorem solution
    (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (hFXb : FX ≫ fX = fX) (hFYb : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY :=
  Ws23.FrobNat.main p fX fY FX FY hFXb hFYb hFX hFY g hg
