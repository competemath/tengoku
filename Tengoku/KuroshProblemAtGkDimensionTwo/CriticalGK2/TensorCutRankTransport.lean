import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.TensorCutRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Thin composed interfaces for actual fixed-factor cut rank transport -/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z A : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]
  [AddCommGroup A] [Module F A]

/--
@isnad1 id=eq.1h8v.s11.17493fdf60b8 from=translated src=- shape=26dfa82e vocab=4bd16dd8
-/
theorem tensorCutRank_append_transport (e : Y ⊗[F] Z ≃ₗ[F] A)
    (t : X ⊗[F] Y) (z : Z) (hz : z ≠ 0) :
    tensorCutRank (e.lTensor X (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z))) =
      tensorCutRank t :=
  (tensorCutRank_rightEquiv (F := F) (X := X) (Y := Y ⊗[F] Z) (A := A) e
    (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z))).trans
      (tensorCutRank_append (F := F) (X := X) (Y := Y) (Z := Z) t z hz)

/--
@isnad1 id=eq.1h8v.s11.813b7d7a20e8 from=translated src=- shape=9a730eb5 vocab=1c5696b6
-/
theorem tensorCutRank_prepend_transport (e : Z ⊗[F] X ≃ₗ[F] A)
    (z : Z) (hz : z ≠ 0) (t : X ⊗[F] Y) :
    tensorCutRank (e.rTensor Y ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t))) =
      tensorCutRank t :=
  (tensorCutRank_leftEquiv (F := F) (X := Z ⊗[F] X) (Y := Y) (A := A) e
    ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t))).trans
      (tensorCutRank_prepend (F := F) (X := X) (Y := Y) (Z := Z) z hz t)

end

end CriticalGK2.ContractionBudget
