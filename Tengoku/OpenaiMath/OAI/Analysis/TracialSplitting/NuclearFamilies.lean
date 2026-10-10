import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.BlockAveraging

namespace OAI

section

noncomputable section

open Pureness NuclearTrace

open scoped ComplexOrder

namespace CurrentMain

section NuclearWeightedBlocks

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma global_partition_bound_corner {N : Type} [Fintype N]
    (v : N → D) (x : unitary D) {r : D} (hr : IsStarProjection r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (q j) -
        (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (q j)*star (x : D)))^2 < δ^2)
    (P : ProjectionPartition r) (τ : TracialState D) :
    (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j) -
      (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D))) ≤ δ := by
  classical
  let q : Option P.Index → D := Option.elim' (1-r) P.piece
  have hq : ∀ j, IsStarProjection (q j) := by
    intro j
    cases j with
    | none => exact hr.one_sub
    | some j => exact P.isProjection j
  have hs : ∑ j, q j = 1 := by
    rw [Fintype.sum_option]
    change (1-r)+(∑ j, P.piece j) = 1
    rw [P.sum_eq]
    abel
  have hb := h (Option P.Index) q hq hs τ
  rw [Fintype.sum_option] at hb
  change (traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)*star (x : D))+
    (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D))))^2 < δ^2 at hb
  have hnon := traceOneNorm_nonneg τ
    (weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)*star (x : D))
  have hsum : 0 ≤ ∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)-
      (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D)) :=
    Finset.sum_nonneg fun j _ => traceOneNorm_nonneg τ _
  nlinarith

end NuclearWeightedBlocks

end CurrentMain

end

end

end OAI
