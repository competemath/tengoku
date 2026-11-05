module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.MatrixWitness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Balanced sums reduce arbitrary column excess to excess two and three. -/
noncomputable section
namespace ChoppedPlane
variable {K : Type*} [Field K]

/-- The row budget can be split into one excess-three block and balanced
excess-two blocks with common rank thresholds.
@isnad1 id=ex.2h3v.s7.71abc975989d from=translated src=- shape=d7230443 vocab=923b6325
-/
theorem odd_block_row_budget (a k m : ℕ)
    (hlow : (2*k+3)*m ≤ 2*a) (hhigh : 2*a < (2*k+3)*(m+1)) :
    ∃ A r : ℕ, r ≤ k ∧ a = A + (k*m+r) ∧
      3*m ≤ 2*A ∧ 2*A ≤ 3*(m+1) := by
  let lo := (3*m+1)/2
  let hi := 3*(m+1)/2
  have halow : k*m+lo ≤ a := by
    have h : 2*(k*m)+3*m ≤ 2*a := by nlinarith [hlow]
    dsimp [lo]
    omega
  have hahigh : a ≤ k*m+k+hi := by
    have h : 2*a < 2*(k*m)+2*k+3*m+3 := by nlinarith [hhigh]
    dsimp [hi]
    omega
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; omega
  let A := max lo (a-(k*m+k))
  have hAlo : lo ≤ A := le_max_left _ _
  have hAhi : A ≤ hi := by dsimp [A]; omega
  have hAa : k*m+A ≤ a := by dsimp [A]; omega
  let r := a-(k*m+A)
  refine ⟨A, r, ?_, ?_, ?_, ?_⟩
  · dsimp [r, A]
    omega
  · dsimp [r]
    omega
  · dsimp [lo] at hAlo
    omega
  · dsimp [hi] at hAhi
    omega

end ChoppedPlane
