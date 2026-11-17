import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open _root_.NumberField.InfiniteAdeleRing open _root_.AutomorphicForm open _root_.Topology
open scoped Classical

noncomputable section

namespace M4aP3B
namespace Rows
namespace TestFnTop

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
/--
@isnad1 id=continuo.0h1v.s9.de50f2ae7932 from=translated src=- shape=1251ce30 vocab=7bdfd003
-/
theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
/--
@isnad1 id=continuo.0h1v.s8.987bfeda062a from=translated src=- shape=9bf764d2 vocab=24bd3d02
-/
theorem continuous_archEntries : Continuous (archEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

/--
@isnad1 id=continuo.1h2v.s7.a859b6e73050 from=translated src=- shape=1e4f9775 vocab=6585679a
-/
theorem continuous_of_isArchTestFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (h : IsArchTestFactor F fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  rw [show fa = Φ ∘ archEntries F from funext hfa]
  exact hΦ.continuous.comp (continuous_archEntries F)

/--
@isnad1 id=continuo.1h2v.s8.4c60fd579384 from=translated src=- shape=eeca7f6d vocab=ee0b7024
-/
theorem continuous_of_isFactorizableTestFn {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hf : IsFactorizableTestFn F f) : Continuous f := by
  obtain ⟨fa, ff, hfa, hff, hfg⟩ := hf
  rw [show f = fun g => fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g)
    from funext hfg]
  exact ((continuous_of_isArchTestFactor F hfa).comp (AdelicLevel.continuous_glArch (𝓞 F) F)).mul
    (hff.1.continuous.comp (AdelicLevel.continuous_glFin (𝓞 F) F))

def zip (p : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => (p.1 i j, p.2 i j)

/--
@isnad1 id=continuo.0h1v.s7.89a3b0c57458 from=translated src=- shape=3f12e97e vocab=112a1d9d
-/
theorem continuous_zip : Continuous (zip F) :=
  continuous_matrix fun i j => (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)

/--
@isnad1 id=eq.0h2v.s11.8157e667682a from=translated src=- shape=9a8eba1b vocab=800bc8a5
-/
theorem zip_glArch_glFin (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    zip F ((AdelicLevel.glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
      (AdelicLevel.glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
      = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  Matrix.ext fun _ _ => rfl

/--
@isnad1 id=iscompac.4h3v.s11.f1f48ba5c804 from=translated src=- shape=1e04116f vocab=1a52e62d
-/
theorem isCompact_preimage_glArch_inter_preimage_glFin
    {Ka : Set (GL (Fin 2) (InfiniteAdeleRing F))} {Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))}
    (hKa : IsCompact Ka) (hKa' : IsClosed Ka) (hKf : IsCompact Kf) (hKf' : IsClosed Kf) :
    IsCompact (AdelicLevel.glArch (𝓞 F) F ⁻¹' Ka ∩ AdelicLevel.glFin (𝓞 F) F ⁻¹' Kf) := by
  set K := AdelicLevel.glArch (𝓞 F) F ⁻¹' Ka ∩ AdelicLevel.glFin (𝓞 F) F ⁻¹' Kf with hK
  have he : IsClosedEmbedding (Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) :=
    Units.isClosedEmbedding_embedProduct
  have hKclosed : IsClosed K :=
    (hKa'.preimage (AdelicLevel.continuous_glArch (𝓞 F) F)).inter
      (hKf'.preimage (AdelicLevel.continuous_glFin (𝓞 F) F))

  let Ψ : (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ×
      (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) →
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) × (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    fun q => (zip F q.1, MulOpposite.op (zip F q.2))
  have hΨ : Continuous Ψ :=
    ((continuous_zip F).comp continuous_fst).prodMk
      (MulOpposite.continuous_op.comp ((continuous_zip F).comp continuous_snd))
  have hC : IsCompact (Ψ '' (((Units.val '' Ka) ×ˢ (Units.val '' Kf)) ×ˢ
      (((fun u => ((u⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) '' Ka) ×ˢ
       ((fun u => ((u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) '' Kf)))) :=
    (((hKa.image Units.continuous_val).prod (hKf.image Units.continuous_val)).prod
      ((hKa.image Units.continuous_coe_inv).prod (hKf.image Units.continuous_coe_inv))).image hΨ
  have hsub : Units.embedProduct _ '' K ⊆ Ψ '' (((Units.val '' Ka) ×ˢ (Units.val '' Kf)) ×ˢ
      (((fun u => ((u⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) '' Ka) ×ˢ
       ((fun u => ((u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) '' Kf))) := by
    rintro _ ⟨g, ⟨hga, hgf⟩, rfl⟩
    refine ⟨(((AdelicLevel.glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
        (AdelicLevel.glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))),
        (((AdelicLevel.glArch (𝓞 F) F g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)),
         (((AdelicLevel.glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))),
      ⟨⟨⟨_, hga, rfl⟩, ⟨_, hgf, rfl⟩⟩, ⟨⟨_, hga, rfl⟩, ⟨_, hgf, rfl⟩⟩⟩, ?_⟩
    show (zip F _, MulOpposite.op (zip F _)) = _
    rw [Units.embedProduct_apply, zip_glArch_glFin, ← map_inv, ← map_inv, zip_glArch_glFin]
  exact he.isInducing.isCompact_iff.mpr (hC.of_isClosed_subset (he.isClosedMap K hKclosed) hsub)

/--
@isnad1 id=hascompa.1h2v.s8.c68de1181edc from=translated src=- shape=eeca7f6d vocab=a3b003fa
-/
theorem hasCompactSupport_of_isFactorizableTestFn {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hf : IsFactorizableTestFn F f) : HasCompactSupport f := by
  obtain ⟨fa, ff, hfa, hff, hfg⟩ := hf
  refine HasCompactSupport.intro'
    (isCompact_preimage_glArch_inter_preimage_glFin F hfa.2.isCompact (isClosed_tsupport fa)
      hff.2.isCompact (isClosed_tsupport ff))
    (((isClosed_tsupport fa).preimage (AdelicLevel.continuous_glArch (𝓞 F) F)).inter
      ((isClosed_tsupport ff).preimage (AdelicLevel.continuous_glFin (𝓞 F) F))) fun g hg => ?_
  rw [hfg]
  rcases not_and_or.mp hg with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

/--
@isnad1 id=and.1h2v.s9.b15a77901ecf from=translated src=- shape=d3d5a35d vocab=527249ae
-/
theorem continuous_and_hasCompactSupport_of_isFactorizableTestFn_impl (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f :=
  ⟨continuous_of_isFactorizableTestFn F hf, hasCompactSupport_of_isFactorizableTestFn F hf⟩

end M4aP3B.Rows.TestFnTop

end

open _root_.NumberField open _root_.NumberField.InfinitePlace.NumberField open _root_.IsDedekindDomain

/--
@isnad1 id=and.1h2v.s9.b15a77901ecf from=translated src=- shape=d3d5a35d vocab=527249ae
-/
theorem solution (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f := by
  exact M4aP3B.Rows.TestFnTop.continuous_and_hasCompactSupport_of_isFactorizableTestFn_impl F f hf
