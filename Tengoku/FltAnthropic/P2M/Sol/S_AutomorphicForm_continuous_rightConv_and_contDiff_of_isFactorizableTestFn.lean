import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RightConvolution
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicLsXi
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_continuous_unipotentGL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn

open NumberField IsDedekindDomain AutomorphicForm MeasureTheory Topology Filter
open scoped Classical

noncomputable section

namespace RightConvRegularity

universe u

section Shape

end Shape

section Slice

variable (K : Type) [Field K] [NumberField K]

private abbrev instNG : NormedAddCommGroup (mixedEmbedding.mixedSpace K) := inferInstance
attribute [local instance] instNG
private abbrev instNS : NormedSpace ℝ (mixedEmbedding.mixedSpace K) := inferInstance
attribute [local instance] instNS

private abbrev Par : Type :=
  (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ×
    ((Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) × mixedEmbedding.mixedSpace K)

private def sliceL : mixedEmbedding.mixedSpace K →L[ℝ] Par K :=
  (ContinuousLinearMap.inr ℝ (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)
      ((Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) × mixedEmbedding.mixedSpace K)).comp
    (ContinuousLinearMap.inr ℝ (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)
      (mixedEmbedding.mixedSpace K))

private def slicePsi (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (q : Par K) : ℂ :=
  Φ fun i j => q.1 i j + q.2.2 * q.2.1 i j

private def nz (z : mixedEmbedding.mixedSpace K) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0)

private def sliceCD (g y : AdelicGL2 (𝓞 K) K) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) × (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
  (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K
      (((((AdelicLevel.glArch (𝓞 K) K g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (AdelicLevel.glArch (𝓞 K) K y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) i j),
   fun i j => - InfiniteAdeleRing.ringEquiv_mixedSpace K
      (((((AdelicLevel.glArch (𝓞 K) K g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (AdelicLevel.glArch (𝓞 K) K y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) i j))

end Slice

end RightConvRegularity

end
