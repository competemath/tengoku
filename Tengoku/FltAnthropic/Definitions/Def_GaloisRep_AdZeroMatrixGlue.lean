import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_AdZero
import Tengoku.FltAnthropic.Definitions.Def_Deformations_TaylorWilesLocal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

namespace Tengoku.FltAnthropic.ResidualGaloisRep

variable {k : Type} [Field k]

/--
@isnad1 id=eq.0h3v.s10.e0d7f0e2ed03 from=translated src=- shape=a89e87a2 vocab=b53b8f99
-/
theorem ker_trace_eq_comap_traceZero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    LinearMap.ker (LinearMap.trace k ρbar.V)
      = (TaylorWiles.traceZero k).comap (LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k).toLinearMap := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, TaylorWiles.mem_traceZero_iff, LinearEquiv.coe_coe,
    LinearMap.trace_eq_matrix_trace k b f, Matrix.trace, Matrix.traceLinearMap_apply, Matrix.diag]

noncomputable def adZeroEquivTraceZero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    LinearMap.ker (LinearMap.trace k ρbar.V) ≃ₗ[k] TaylorWiles.traceZero k :=
  LinearEquiv.ofSubmodules (LinearMap.toMatrix b b) _ _ (by
    rw [ker_trace_eq_comap_traceZero ρbar b, Submodule.map_comap_eq_of_surjective]
    exact (LinearMap.toMatrix b b).surjective)

/--
@isnad1 id=eq.0h4v.s13.73429b0602b4 from=translated src=- shape=d699931f vocab=7911168f
-/
@[simp]
theorem adZeroEquivTraceZero_apply_coe (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρbar.adZeroEquivTraceZero b f : TaylorWiles.traceZero k) : Matrix (Fin 2) (Fin 2) k) = LinearMap.toMatrix b b (f : Module.End k ρbar.V) :=
  rfl

end Tengoku.FltAnthropic.ResidualGaloisRep
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
