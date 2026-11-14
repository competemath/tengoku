import Tengoku.TdaLib.TDA.Persistence.FinitePresentationHookKernel
import Tengoku.TdaLib.TDA.Persistence.FinitePresentationFiniteDimensional
import Tengoku.TdaLib.TDA.Persistence.FinitePresentationKanExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Consumers and boundary cases for finite-hook cover kernel presentations

The examples apply the actual-cover kernel theorem to a nonzero quotient in
characteristic zero and characteristic two, and exercise empty/zero input
families separately.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FinitePresentationHookKernel.Examples

open CategoryTheory CategoryTheory.Limits GradedFree
open scoped TDA.Persistence ZeroObject

/-- The actual finite-hook cover kernel of the nonzero rational presentation
with its repeated birth and nonzero relation is finitely presented.
@isnad1 id=ex.0h0v.s13.af3a13889beb from=translated src=- shape=925269ee vocab=5552bfd4
-/
theorem rational_presentation_actual_cover_kernel_finitelyPresented :
    ∃ (G : CoordinateGrid 2) (A : PModule ℚ G.Point)
      (hA : ∀ p, FiniteDimensional ℚ (A.obj p))
      (e : G.lan.obj A ≅ (FinitePresentationKanExamples.presentation ℚ 2).presented),
      IsRankExact
        (G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫
          (G.finiteHookDeflationLanIso A).hom)
        ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom) ∧
      IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) ∧
      FinitelyPresented.{0,0,0}
        (kernel ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom)) := by
  obtain ⟨G, A, hA, e, hrank, hprojective, hkernel⟩ :=
    GradedFree.finitelyPresented_exists_finiteHookRankExactCoverKernel
      ((FinitePresentationKanExamples.presentation ℚ 2).finitelyPresented
        (FinitePresentationKanExamples.presentation_finite ℚ 2))
  exact ⟨G, A, hA, e, hrank, hprojective, hkernel⟩

/-- The same nonzero presentation has a finitely presented actual cover
kernel over the field of two elements.
@isnad1 id=ex.0h0v.s14.a79bf5ed1dfc from=translated src=- shape=c2106917 vocab=597b33ff
-/
theorem characteristic_two_presentation_actual_cover_kernel_finitelyPresented :
    ∃ (G : CoordinateGrid 2) (A : PModule (ZMod 2) G.Point)
      (hA : ∀ p, FiniteDimensional (ZMod 2) (A.obj p))
      (e : G.lan.obj A ≅ (FinitePresentationKanExamples.presentation (ZMod 2) 2).presented),
      IsRankExact
        (G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫
          (G.finiteHookDeflationLanIso A).hom)
        ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom) ∧
      IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) ∧
      FinitelyPresented.{0,0,0}
        (kernel ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom)) := by
  obtain ⟨G, A, hA, e, hrank, hprojective, hkernel⟩ :=
    GradedFree.finitelyPresented_exists_finiteHookRankExactCoverKernel
      ((FinitePresentationKanExamples.presentation (ZMod 2) 2).finitelyPresented
        (FinitePresentationKanExamples.presentation_finite (ZMod 2) 2))
  exact ⟨G, A, hA, e, hrank, hprojective, hkernel⟩

/-- Left Kan extension preserves finite presentation for the empty free
family, including an empty occurrence index.
@isnad1 id=finitely.0h3v.s8.f19d00acdf96 from=translated src=- shape=23df402f vocab=960ec06a
-/
theorem empty_family_lan_finitelyPresented
    {k : Type} [Field k] {n : ℕ} (G : CoordinateGrid n) :
    FinitelyPresented.{0,0,0}
      (G.lan.obj (GradedFree.module (R := k)
        (⟨Empty, Empty.elim⟩ : GradedFree.GradedGenerators.{0,0} G.Point))) := by
  let W : GradedFree.GradedGenerators.{0,0} G.Point := ⟨Empty, Empty.elim⟩
  exact GradedFree.finitelyPresented_lan_of_finiteGrid G
    (GradedFree.free_finitelyPresented W)

/-- The zero module on the zero-dimensional ambient coordinate poset is a
finite-hook cover kernel with a finite presentation. The source presentation
has no generator or relation occurrences.
@isnad1 id=ex.0h1v.s12.dd31492c7023 from=translated src=- shape=9a42c3aa vocab=455116a6
-/
theorem zero_empty_index_actual_cover_kernel_finitelyPresented
    (k : Type) [Field k] :
    ∃ (G : CoordinateGrid 0) (A : PModule k G.Point)
      (hA : ∀ p, FiniteDimensional k (A.obj p))
      (e : G.lan.obj A ≅ (0 : PModule k (Fin 0 → ℝ))),
      FinitelyPresented.{0,0,0}
        (kernel ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom)) := by
  let W : GradedFree.GradedGenerators.{0,0} (Fin 0 → ℝ) := ⟨Empty, Empty.elim⟩
  have hzero : IsZero (GradedFree.module (R := k) W) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth W
    intro g
    exact g.elim
  have hfp : FinitelyPresented.{0,0,0}
      (0 : PModule k (Fin 0 → ℝ)) :=
    GradedFree.finitelyPresented_of_iso (GradedFree.free_finitelyPresented W)
      hzero.isoZero
  obtain ⟨G, A, hA, e, _, _, hkernel⟩ :=
    GradedFree.finitelyPresented_exists_finiteHookRankExactCoverKernel hfp
  exact ⟨G, A, hA, e, hkernel⟩

/-- The actual finite-hook cover kernel supplied for a finitely presented
real-coordinate module has finite-dimensional fibers. The only input about
the original module is its finite presentation.
@isnad1 id=ex.1h3v.s13.effb5175f6e8 from=translated src=- shape=9753621f vocab=9e90cdaf
-/
theorem finitelyPresented_actual_cover_kernel_finiteDimensional
    {k : Type u} [Field k] {n : ℕ}
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (hM : FinitelyPresented (R := k) (P := Fin n → ℝ) M) :
    ∃ (G : CoordinateGrid n) (A : PModule.{u,0,u} k G.Point)
      (hA : ∀ p, FiniteDimensional k (A.obj p))
      (e : G.lan.obj A ≅ M),
      IsRankExact
        (G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫
          (G.finiteHookDeflationLanIso A).hom)
        ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom) ∧
      IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) ∧
      ∀ p, FiniteDimensional k
        ((kernel ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom)).obj p) := by
  obtain ⟨G, A, hA, e, hrank, hprojective, hkernel⟩ :=
    GradedFree.finitelyPresented_exists_finiteHookRankExactCoverKernel hM
  refine ⟨G, A, hA, e, hrank, hprojective, ?_⟩
  intro p
  exact GradedFree.finitelyPresented_finiteDimensional _ hkernel p

end TDA.Persistence.FinitePresentationHookKernel.Examples
