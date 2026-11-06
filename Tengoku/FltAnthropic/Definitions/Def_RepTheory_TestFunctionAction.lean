import Tengoku.Seed.MeasureTheory.Group.Measure
import Tengoku.Seed.MeasureTheory.Measure.Haar.Basic
import Tengoku.Seed.Topology.LocallyConstant.Basic
import Tengoku.Seed.Topology.Algebra.Support
import Tengoku.Seed.Topology.Algebra.OpenSubgroup
import Tengoku.Seed.Algebra.Module.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace TestFunctionAction

section OpenStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}

abbrev HasOpenStabilizer (G : Type*) {M : Type*} [Group G] [TopologicalSpace G] [MulAction G M]
    (v : M) : Prop :=
  IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G)

variable [MulAction G M]

/--
@isnad1 id=hasopens.1h5v.s6.6e17c4b9bff4 from=translated src=- shape=d519dcee vocab=34dcd173
-/
theorem HasOpenStabilizer.const_smul [ContinuousMul G] {R : Type*} [SMul R M] [SMulCommClass G R M]
    {v : M} (hv : HasOpenStabilizer G v) (r : R) : HasOpenStabilizer G (r • v) := by
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G v) (fun g hg => ?_) hv
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [smul_comm, hg]

end OpenStabilizer

section Witness

end Witness

section MeasureCoeff

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]

end MeasureCoeff

section FiniteRangeIntegral

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

end FiniteRangeIntegral

section Integrand

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

end Integrand

section HeckeSmul

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

variable [TopologicalSpace G] [ContinuousMul G]

end HeckeSmul

section Idempotent

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {G : Type*}

variable {𝕜}
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [Group G] [MeasurableSpace G] [DistribMulAction G V] [SMulCommClass G 𝕜 V]

variable [TopologicalSpace G] [ContinuousMul G]

end Idempotent

section Projection

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

end Projection

end TestFunctionAction
