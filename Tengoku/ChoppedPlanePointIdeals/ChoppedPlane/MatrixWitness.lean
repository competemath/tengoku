module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Toeplitz
public import Tengoku.Seed.Data.Matrix.Block
public import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section

namespace ChoppedPlane

variable {K : Type*} [Field K]

/-- The direct sum of two matrices of linear forms.-/
def linearMatrixBlock {a₁ a₂ c₁ c₂ : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂) :
    LinearMatrix K (a₁ + a₂) (c₁ + c₂) :=
  (Matrix.fromBlocks L₁ 0 0 L₂).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

@[simp] theorem linearMatrixBlock_left {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (v : MatrixSource K (c₁+c₂) t) (i : Fin a₁) :
    linearMatrixMap (linearMatrixBlock L₁ L₂) t v (Fin.castAdd a₂ i) =
      linearMatrixMap L₁ t (fun j => v (Fin.castAdd c₂ j)) i := by
  apply Subtype.ext
  simp [linearMatrixMap_val, linearMatrixBlock, Fin.sum_univ_add]

@[simp] theorem linearMatrixBlock_right {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (v : MatrixSource K (c₁+c₂) t) (i : Fin a₂) :
    linearMatrixMap (linearMatrixBlock L₁ L₂) t v (Fin.natAdd a₁ i) =
      linearMatrixMap L₂ t (fun j => v (Fin.natAdd c₁ j)) i := by
  apply Subtype.ext
  simp [linearMatrixMap_val, linearMatrixBlock, Fin.sum_univ_add]

theorem linearMatrixBlock_injective {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (h₁ : Function.Injective (linearMatrixMap L₁ t))
    (h₂ : Function.Injective (linearMatrixMap L₂ t)) :
    Function.Injective (linearMatrixMap (linearMatrixBlock L₁ L₂) t) := by
  intro v w h
  have hleft : (fun j : Fin c₁ => v (Fin.castAdd c₂ j)) =
      (fun j : Fin c₁ => w (Fin.castAdd c₂ j)) := by
    apply h₁
    funext i
    simpa only [linearMatrixBlock_left] using congrFun h (Fin.castAdd a₂ i)
  have hright : (fun j : Fin c₂ => v (Fin.natAdd c₁ j)) =
      (fun j : Fin c₂ => w (Fin.natAdd c₁ j)) := by
    apply h₂
    funext i
    simpa only [linearMatrixBlock_right] using congrFun h (Fin.natAdd a₁ i)
  funext j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j => simpa using congrFun hleft j
  | inr j => simpa using congrFun hright j

theorem linearMatrixBlock_surjective {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (h₁ : Function.Surjective (linearMatrixMap L₁ t))
    (h₂ : Function.Surjective (linearMatrixMap L₂ t)) :
    Function.Surjective (linearMatrixMap (linearMatrixBlock L₁ L₂) t) := by
  intro y
  obtain ⟨v₁, hv₁⟩ := h₁ (fun i => y (Fin.castAdd a₂ i))
  obtain ⟨v₂, hv₂⟩ := h₂ (fun i => y (Fin.natAdd a₁ i))
  let v : MatrixSource K (c₁+c₂) t :=
    fun j => Sum.elim v₁ v₂ (finSumFinEquiv.symm j)
  refine ⟨v, ?_⟩
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => simpa [v] using congrFun hv₁ i
  | inr i => simpa [v] using congrFun hv₂ i

end ChoppedPlane
