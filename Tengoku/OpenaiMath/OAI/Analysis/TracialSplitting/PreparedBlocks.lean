import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.BlockSampling

namespace OAI

section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

namespace BistochasticTest

variable {A D N : Type} [CStarAlgebra A] [CStarAlgebra D] [Fintype N]

def ofFamily (v : N → A) (hcol : ∑ i, star (v i)*v i = 1)
    (hrow : ∑ i, v i*star (v i) = 1) : BistochasticTest A where
  size := Fintype.card N
  coeff := fun i => v ((Fintype.equivFin N).symm i)
  col := by rw [(Fintype.equivFin N).symm.sum_comp (fun i => star (v i)*v i)]; exact hcol
  row := by rw [(Fintype.equivFin N).symm.sum_comp (fun i => v i*star (v i))]; exact hrow

lemma ofFamily_average (ι : A →⋆ₐ[ℂ] D) (v : N → A)
    (hcol : ∑ i, star (v i)*v i = 1) (hrow : ∑ i, v i*star (v i) = 1) (r : D) :
    weightedAverage (fun _ => (1 : ℝ)) ((ofFamily v hcol hrow).map ι).coeff r =
      weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) r := by
  simp only [weightedAverage,one_smul,map,ofFamily]
  exact (Fintype.equivFin N).symm.sum_comp (fun i => ι (v i)*r*star (ι (v i)))

variable [PartialOrder D] [StarOrderedRing D]

lemma average_le_one (V : BistochasticTest D) {r : D} (hr : IsStarProjection r) :
    weightedAverage (fun _ => (1 : ℝ)) V.coeff r ≤ 1 := by
  have h (i : Fin V.size) : V.coeff i*r*star (V.coeff i) ≤ V.coeff i*star (V.coeff i) := by
    simpa only [mul_one] using star_right_conjugate_le_conjugate hr.le_one (V.coeff i)
  simpa only [weightedAverage,one_smul,V.row] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

end BistochasticTest

section Prepared

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end Prepared

end CurrentMain

end

end

end OAI
