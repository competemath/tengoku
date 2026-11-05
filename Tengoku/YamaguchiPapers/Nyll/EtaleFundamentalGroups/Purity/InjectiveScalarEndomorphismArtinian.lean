/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.InjectiveResidueFieldCogenerator
import Tengoku.Seed.Algebra.Module.Torsion.Basic
import Tengoku.Seed.Order.Hom.Basic
import Tengoku.Seed.RingTheory.Artinian.Defs
import Tengoku.Seed.RingTheory.Noetherian.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Double annihilators and the descending chain condition

For an injective module containing the residue field, maps to the module
separate every quotient.  If all its endomorphisms are scalar maps, this
separation gives the double-annihilator equality for every submodule.
Annihilators then embed its submodule lattice into the opposite ideal
lattice.  Over a Noetherian ring, the module is consequently Artinian.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing

variable {R E : Type u} [CommRing R] [IsLocalRing R]
variable [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- Scalar endomorphisms and injectivity recover each submodule from its
annihilator.
@isnad1 id=eq.2h4v.s9.2245daf5cf2e from=translated src=- shape=b0952603 vocab=bbfa0aa3
-/
theorem torsionBySet_annihilator_eq_of_scalar_endomorphisms
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hscalar : ∀ f : E →ₗ[R] E, ∃ r : R, ∀ z : E, f z = r • z)
    (N : Submodule R E) : Submodule.torsionBySet R E N.annihilator = N := by
  refine le_antisymm ?_ ?_
  · intro x hx
    by_contra hxN
    have hq : N.mkQ x ≠ 0 := by
      intro hzero
      exact hxN ((Submodule.Quotient.mk_eq_zero N).mp hzero)
    obtain ⟨g, hg⟩ :=
      exists_linearMap_apply_ne_zero_of_injective_residueField i hi (N.mkQ x) hq
    obtain ⟨r, hr⟩ := hscalar (g.comp N.mkQ)
    have hrN : r ∈ N.annihilator := by
      apply Submodule.mem_annihilator.mpr
      intro y hy
      rw [← hr y]
      change g (Submodule.Quotient.mk y) = 0
      rw [(Submodule.Quotient.mk_eq_zero N).mpr hy, map_zero]
    have hrx : r • x = 0 :=
      (Submodule.mem_torsionBySet_iff (N.annihilator : Set R) x).mp hx ⟨r, hrN⟩
    apply hg
    exact (hr x).trans hrx
  · intro x hx
    apply (Submodule.mem_torsionBySet_iff (N.annihilator : Set R) x).mpr
    intro r
    exact Submodule.mem_annihilator.mp r.property x hx

/-- If every endomorphism of an injective module containing the residue
field is scalar, Noetherianity of the ring implies Artinianness of the
module.  The complete-local hull supplies the scalar property separately.
@isnad1 id=isartini.2h3v.s9.21b98bd2ff6c from=translated src=- shape=45b330ea vocab=28e4acc3
-/
theorem isArtinian_of_injective_residueField_and_scalar_endomorphisms
    [IsNoetherianRing R]
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hscalar : ∀ f : E →ₗ[R] E, ∃ r : R, ∀ z : E, f z = r • z) :
    IsArtinian R E := by
  let e : Submodule R E ↪o (Ideal R)ᵒᵈ :=
    OrderEmbedding.ofMapLEIff (fun N => OrderDual.toDual N.annihilator) (by
      intro N P
      change P.annihilator ≤ N.annihilator ↔ N ≤ P
      constructor
      · intro hNP x hx
        rw [← torsionBySet_annihilator_eq_of_scalar_endomorphisms i hi hscalar P]
        apply (Submodule.mem_torsionBySet_iff (P.annihilator : Set R) x).mpr
        intro r
        exact Submodule.mem_annihilator.mp (hNP r.property) x hx
      · exact Submodule.annihilator_mono)
  exact e.wellFoundedLT

end EtaleFundamentalGroups.Purity
