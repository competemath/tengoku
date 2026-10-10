import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.CoefficientBounds

namespace OAI

universe uE uF

section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

noncomputable section

open scoped Pointwise

noncomputable section

open scoped ComplexOrder

noncomputable section

open scoped ComplexOrder

namespace NuclearTrace

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

def coefficientSelfAdjMap (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (k : Fin n → K) (a : Fin n → A) : selfAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun x := ⟨coefficientMap α k a x,coefficientMap_selfAdjoint α k a _ x.property⟩
  map_add' left right := Subtype.ext ((coefficientMap α k a).map_add left right)
  map_smul' scalar value :=
    Subtype.ext ((coefficientMap α k a).map_smul_of_tower scalar (value : A))

def coefficientCone (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) :=
  ConvexCone.hull ℝ {L | ∃ (n : ℕ) (k : Fin n → K) (a : Fin n → A),
    L = coefficientSelfAdjMap α k a}

def evalTuple (x : I → selfAdjoint A) :
    (selfAdjoint A →ₗ[ℝ] selfAdjoint A) →ₗ[ℝ] (I → selfAdjoint A) where
  toFun L i := L (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tracialTupleSeminorm (τ : Pureness.TracialState A) :
    Seminorm ℝ (I → selfAdjoint A) :=
  ∑ i, (CurrentMain.tracialOneSeminorm τ).comp (LinearMap.proj i)

@[simp] lemma tracialTupleSeminorm_apply (τ : Pureness.TracialState A)
    (x : I → selfAdjoint A) :
    tracialTupleSeminorm τ x = ∑ i, CurrentMain.traceOneNorm τ (x i) := by
  simp [tracialTupleSeminorm]

lemma tracialTupleSeminorm_continuous (τ : Pureness.TracialState A) :
    Continuous (tracialTupleSeminorm (I := I) τ) := by
  simp only [funext (tracialTupleSeminorm_apply (I := I) τ)]
  apply continuous_finsetSum
  intro i _
  exact (CurrentMain.tracialOneSeminorm_continuous τ).comp (continuous_apply i)

end NuclearTrace

noncomputable section

namespace NuclearTrace

open Set

variable {E : Type uE} {F : Type uF}

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

end NuclearTrace

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
