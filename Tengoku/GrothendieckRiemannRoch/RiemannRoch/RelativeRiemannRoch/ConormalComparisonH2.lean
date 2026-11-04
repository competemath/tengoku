/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Smooth.Basic
import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conormal comparison for non-smooth closed subschemes

For a scalar tower `R → A → B`, suppose `R → B` is surjective and `A` is formally
smooth over `R`. The actual coefficient inclusion induces a short exact sequence

`0 → ker(R → B)/ker² → ker(A → B)/ker² → B ⊗_A Ω[A/R] → 0`.

The quotient `B` is neither assumed smooth nor assumed regular. Injectivity comes
from the invariance of first homology of the naive cotangent complex under a change
of formally smooth presentation. The source presentation is `R → B`, whose
relative differential module is zero. Surjectivity on the right follows from
`Ω[B/R] = 0`; the sequence splits since `Ω[A/R]` is projective.

This is the affine algebra needed to compare conormals on the common product of
two projective factorisations in GRR. Identifying these maps with the actual sheaf
conormal maps and proving global virtual-class independence are separate steps.
-/

set_option autoImplicit false

noncomputable section

open Algebra Algebra.Extension
open CategoryTheory
open scoped TensorProduct

universe u v w

namespace SchemeKTheory.ConormalComparisonH2

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
  (P Q : Extension.{w} R B)

/-- If the degree-zero differential module vanishes, every conormal class is a first homology
class.
@isnad1 id=surjecti.0h3v.s8.090247c2616b from=translated src=- shape=488471f0 vocab=fbeb5e10
-/
theorem h1Cotangentι_surjective [Subsingleton P.CotangentSpace] :
    Function.Surjective P.h1Cotangentι := by
  intro x
  exact ⟨⟨x, Subsingleton.elim _ _⟩, rfl⟩

variable [FormallySmooth R P.Ring] [FormallySmooth R Q.Ring]

/-- A map of formally smooth presentations is injective on conormals when the source
differential module vanishes.
@isnad1 id=injectiv.0h5v.s8.bbcb568679a2 from=translated src=- shape=d8708a45 vocab=b229ea12
-/
theorem cotangentMap_injective [Subsingleton P.CotangentSpace] (f : P.Hom Q) :
    Function.Injective (Extension.Cotangent.map f) := by
  intro x y h
  obtain ⟨x', rfl⟩ := h1Cotangentι_surjective P x
  obtain ⟨y', rfl⟩ := h1Cotangentι_surjective P y
  have hm : Extension.H1Cotangent.map f x' = Extension.H1Cotangent.map f y' :=
    Subtype.ext h
  have he : x' = y' := (Extension.H1Cotangent.equivOfFormallySmooth P Q).injective (by
    simpa only [Extension.H1Cotangent.equivOfFormallySmooth_apply f] using hm)
  exact congrArg P.h1Cotangentι he

/-- The image of the actual conormal map is the kernel of the target differential.
@isnad1 id=exact.0h5v.s10.da18c3d36d3d from=translated src=- shape=36459bdc vocab=2c3699b4
-/
theorem exact_cotangentMap_cotangentComplex [Subsingleton P.CotangentSpace]
    (f : P.Hom Q) : Function.Exact (Extension.Cotangent.map f) Q.cotangentComplex := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (Extension.H1Cotangent.equivOfFormallySmooth P Q).surjective ⟨x, hx⟩
    refine ⟨P.h1Cotangentι y, ?_⟩
    have hm : Extension.H1Cotangent.map f y = ⟨x, hx⟩ := by
      simpa only [Extension.H1Cotangent.equivOfFormallySmooth_apply f] using hy
    exact congrArg Q.h1Cotangentι hm
  · rintro ⟨y, rfl⟩
    have h := Extension.CotangentSpace.map_cotangentComplex f y
    rw [Subsingleton.elim (P.cotangentComplex y) 0, map_zero] at h
    exact h.symm

section Tower

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (hf : Function.Surjective (algebraMap R B))

/-- The quotient R → B, retaining the given ring and algebra structures.-/
def baseExtension : Extension R B where
  Ring := R
  σ := Function.surjInv hf
  algebraMap_σ := Function.surjInv_eq hf

include hf in
/-- Surjectivity of R → B implies surjectivity of A → B in the actual scalar tower.
@isnad1 id=surjecti.1h3v.s7.1acfe463d35a from=translated src=- shape=91651009 vocab=2eb9489d
-/
theorem ambient_surjective : Function.Surjective (algebraMap A B) := by
  intro b
  obtain ⟨r, hr⟩ := hf b
  exact ⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A B r).symm.trans hr⟩

/-- The quotient A → B, retaining the given ring and algebra structures.-/
def ambientExtension : Extension R B where
  Ring := A
  σ := Function.surjInv (ambient_surjective hf)
  algebraMap_σ := Function.surjInv_eq (ambient_surjective hf)

/-- The genuine coefficient inclusion R → A as a morphism of extensions of B.-/
def baseHom : (baseExtension hf).Hom (ambientExtension (A := A) hf) where
  toRingHom := algebraMap R A
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom x := (IsScalarTower.algebraMap_apply R A B x).symm

/-- The B-linear conormal comparison induced by the actual coefficient map R → A.-/
def conormalMap : (baseExtension hf).Cotangent →ₗ[B]
    (ambientExtension (A := A) hf).Cotangent :=
  Extension.Cotangent.map (baseHom (A := A) hf)

/-- The conormal comparison is injective for a formally smooth ambient A/R; B need not be
smooth.
@isnad1 id=injectiv.1h3v.s9.12c2554556ad from=translated src=- shape=87ba4997 vocab=5d34601c
-/
theorem conormalMap_injective [FormallySmooth R A] :
    Function.Injective (conormalMap (A := A) hf) := by
  haveI : FormallySmooth R (baseExtension hf).Ring :=
    inferInstanceAs (FormallySmooth R R)
  haveI : FormallySmooth R (ambientExtension (A := A) hf).Ring :=
    inferInstanceAs (FormallySmooth R A)
  haveI : Subsingleton (baseExtension hf).CotangentSpace :=
    inferInstanceAs (Subsingleton (B ⊗[R] Ω[R⁄R]))
  exact cotangentMap_injective _ _ (baseHom hf)

/-- The conormal comparison and the actual Kähler differential form an exact pair.
@isnad1 id=exact.1h3v.s11.b09882e3b42a from=translated src=- shape=4bb45594 vocab=8bb30626
-/
theorem conormalMap_exact [FormallySmooth R A] :
    Function.Exact (conormalMap (A := A) hf)
      (ambientExtension (A := A) hf).cotangentComplex := by
  haveI : FormallySmooth R (baseExtension hf).Ring :=
    inferInstanceAs (FormallySmooth R R)
  haveI : FormallySmooth R (ambientExtension (A := A) hf).Ring :=
    inferInstanceAs (FormallySmooth R A)
  haveI : Subsingleton (baseExtension hf).CotangentSpace :=
    inferInstanceAs (Subsingleton (B ⊗[R] Ω[R⁄R]))
  exact exact_cotangentMap_cotangentComplex _ _ (baseHom hf)

/-- On an ideal generator r, the actual comparison sends its class to the class of its image in
A.
@isnad1 id=eq.2h4v.s12.2cb52db05821 from=translated src=- shape=a1d3a2c9 vocab=6ffc1515
-/
theorem conormalMap_mk (r : R) (hr : algebraMap R B r = 0) :
    conormalMap (A := A) hf (Extension.Cotangent.mk ⟨r, hr⟩) =
      Extension.Cotangent.mk ⟨algebraMap R A r,
        (IsScalarTower.algebraMap_apply R A B r).symm.trans hr⟩ := by
  exact Extension.Cotangent.map_mk (baseHom hf) ⟨r, hr⟩

include hf in
/-- For r in ker(R → B), its image lies in ker(A → B)² exactly when r lies in ker(R → B)².
@isnad1 id=iff.2h4v.s9.65b924febfbf from=translated src=- shape=6055976a vocab=f538b44a
-/
theorem map_mem_square_iff [FormallySmooth R A] (r : R)
    (hr : algebraMap R B r = 0) :
    algebraMap R A r ∈ (RingHom.ker (algebraMap A B)) ^ 2 ↔
      r ∈ (RingHom.ker (algebraMap R B)) ^ 2 := by
  have hA := (Extension.Cotangent.mk_eq_zero_iff
    (P := ambientExtension (A := A) hf)
    ⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A B r).symm.trans hr⟩).symm
  have hR := Extension.Cotangent.mk_eq_zero_iff (P := baseExtension hf) ⟨r, hr⟩
  have he : conormalMap (A := A) hf (Extension.Cotangent.mk ⟨r, hr⟩) = 0 ↔
      Extension.Cotangent.mk (P := baseExtension hf) ⟨r, hr⟩ = 0 :=
    (conormalMap_injective hf).eq_iff' (map_zero _)
  rw [conormalMap_mk hf r hr] at he
  exact hA.trans (he.trans hR)

/-- The actual differential kills the image of the coefficient conormal comparison.
@isnad1 id=eq.1h3v.s12.d2dfebd619cd from=translated src=- shape=a4b56d0a vocab=03afaf60
-/
theorem conormalMap_comp [FormallySmooth R A] :
    (ambientExtension (A := A) hf).cotangentComplex.comp (conormalMap hf) = 0 := by
  ext x
  exact ((conormalMap_exact (A := A) hf) (conormalMap hf x)).mpr ⟨x, rfl⟩

/-- The genuine affine comparison sequence ker(R → B)/ker² → ker(A → B)/ker² → B ⊗_A Ω[A/R].-/
def conormalSequence [FormallySmooth R A] : ShortComplex (ModuleCat B) :=
  ShortComplex.mk (ModuleCat.ofHom (conormalMap (A := A) hf))
    (ModuleCat.ofHom (ambientExtension (A := A) hf).cotangentComplex)
    (ModuleCat.hom_ext (conormalMap_comp hf))

end Tower

end SchemeKTheory.ConormalComparisonH2
