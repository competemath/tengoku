module

public import Tengoku.Seed.FieldTheory.IsAlgClosed.Classification
public import Tengoku.Seed.Analysis.Complex.Cardinality
public import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
public import Tengoku.Seed.RingTheory.AlgebraicIndependent.Adjoin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Countable fields of characteristic zero embed into `ℂ`
-/

@[expose] public section
namespace Tengoku.LanaPi1 end Tengoku.LanaPi1 open Tengoku.LanaPi1 
open Cardinal

namespace Tengoku.LanaPi1.AffOrbicurve

/-- **Every countable field of characteristic `0` embeds into `ℂ`.**
@isnad1 id=nonempty.0h1v.s5.58a6b128ff9d from=translated src=- shape=c1134c5c vocab=2db8b981
-/
theorem nonempty_ringHom_complex (L : Type) [Field L] [CharZero L] [Countable L] :
    Nonempty (L →+* ℂ) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ L
  obtain ⟨b, hb⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hC : #(b : Set ℂ) = 𝔠 := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' (R := ℚ)
      ((↑) : b → ℂ) hb (le_of_eq Cardinal.mkRat) (by rw [Cardinal.mk_complex]; exact
        Cardinal.aleph0_lt_continuum)
    rw [← this, Cardinal.mk_complex]
  have hs' : #s ≤ #b := by
    rw [hC]
    exact (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  obtain ⟨e⟩ := hs'
  set x : s → L := (↑)
  set w : s → ℂ := fun i => (e i : ℂ)
  have hw : AlgebraicIndependent ℚ w := hb.1.comp e e.injective
  let g : MvPolynomial s ℚ →+* ℂ := (MvPolynomial.aeval (R := ℚ) w).toRingHom
  have hinj : Function.Injective g := algebraicIndependent_iff_injective_aeval.mp hw
  let R := Algebra.adjoin ℚ (Set.range x)
  let φ : R →+* ℂ := g.comp hs.1.aevalEquiv.symm.toRingEquiv.toRingHom
  have hφ : Function.Injective φ := hinj.comp hs.1.aevalEquiv.symm.injective
  letI : Algebra R ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic R L := hs.isAlgebraic
  haveI : Module.IsTorsionFree R ℂ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hφ
  haveI : Module.IsTorsionFree R L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact Subtype.val_injective
  exact ⟨(IsAlgClosed.lift (M := ℂ) (R := R) (S := L)).toRingHom⟩

end Tengoku.LanaPi1.AffOrbicurve
-- Tengoku: root names of this library moved to Tengoku.LanaPi1 so they do not collide with other libraries (generated)
