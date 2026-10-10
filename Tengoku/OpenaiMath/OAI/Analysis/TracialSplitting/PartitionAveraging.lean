import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.KrausApproximation

namespace OAI

section

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace NuclearTrace

open Pureness CurrentMain

section ComplexApproximation

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype I]

end ComplexApproximation

section Synthesis

variable {A N : Type} [CStarAlgebra A] [Fintype N] [DecidableEq N]

lemma matrixSynthesis_scalarMatrixUnit (a : N → A) (i j : N) :
    matrixSynthesis a (scalarMatrixUnit i j) = star (a i)*a j := by
  change (∑ k, ∑ l, scalarMatrixUnit i j k l • (star (a k)*a l)) = _
  simp [scalarMatrixUnit,Matrix.single_apply,ite_and]

omit [DecidableEq N] in
lemma matrixSynthesis_map {D : Type} [CStarAlgebra D]
    (ι : A →⋆ₐ[ℂ] D) (a : N → A) (T : CStarMatrix N N ℂ) :
    matrixSynthesis (fun i => ι (a i)) T = ι (matrixSynthesis a T) := by
  change (∑ i, ∑ j, T i j • (star (ι (a i))*ι (a j))) =
    ι (∑ i, ∑ j, T i j • (star (a i)*a j))
  simp only [map_sum,map_smul,map_mul,map_star]

end Synthesis

section NuclearGlobalAveraging

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end NuclearGlobalAveraging

end NuclearTrace

end

end

end OAI
