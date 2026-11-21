import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_ArchimedeanIdeleModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp

namespace P2mS26A1
open NumberField.InfPlaceDecomp

/--
@isnad1 id=isconj.1h4v.s10.12089faa4240 from=translated src=- shape=79c7f6f3 vocab=f0bbbb59
-/
theorem isConj_embedding_of_ne_one {E K : Type*} [Field E] [Field K] [Algebra E K] {w : InfinitePlace K}
    (σ : decomp E K w) (hσ : σ ≠ 1) : ComplexEmbedding.IsConj w.embedding (σ : K ≃ₐ[E] K) := by
  have h : (σ : K ≃ₐ[E] K) ∈ MulAction.stabilizer (K ≃ₐ[E] K) (InfinitePlace.mk w.embedding) := by
    rw [InfinitePlace.mk_embedding]; exact σ.2
  rcases (InfinitePlace.mem_stabilizer_mk_iff w.embedding (σ : K ≃ₐ[E] K)).1 h with h1 | h2
  · exact absurd (Subtype.ext h1) hσ
  · exact h2

/--
@isnad1 id=eq.1h5v.s12.25ce84056db4 from=translated src=- shape=839fe152 vocab=2c8a12ef
-/
theorem extensionEmbedding_smul_coe {E K : Type*} [Field E] [Field K] [Algebra E K] {w : InfinitePlace K}
    (σ : decomp E K w) (hσ : σ ≠ 1) (y : WithAbs w.1) :
    InfinitePlace.Completion.extensionEmbedding w (σ • (y : w.Completion)) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (y : w.Completion)) := by
  rw [smul_def, actRingEquiv_coe, InfinitePlace.Completion.extensionEmbedding_coe,
    InfinitePlace.Completion.extensionEmbedding_coe, WithAbs.congr_apply, WithAbs.equiv_apply, WithAbs.equiv_apply]
  change w.embedding ((σ : K ≃ₐ[E] K) y.ofAbs) = _
  exact (isConj_embedding_of_ne_one σ hσ).eq y.ofAbs

end P2mS26A1

open P2mS26A1 NumberField.InfPlaceDecomp in

/--
@isnad1 id=eq.1h5v.s11.c7b9b78acd32 from=translated src=- shape=3bdae7f0 vocab=a65b0501
-/
theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (hσ : σ ≠ 1) (x : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w (σ • x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w x) := by
  refine InfinitePlace.Completion.induction_on _ x ?_ (fun y => extensionEmbedding_smul_coe σ hσ y)
  exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (NumberField.InfPlaceDecomp.continuous_actRingEquiv σ))
    (Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous)
