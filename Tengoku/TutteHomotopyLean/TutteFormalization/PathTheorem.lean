import Tengoku.TutteHomotopyLean.TutteFormalization.Definitions
import Tengoku.TutteHomotopyLean.TutteFormalization.PathInduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Tutte's path theorem, with its approved statement and checked corank induction.

The authoritative source is `source/paper.tex`, label `thm:path-theorem`.
All vocabulary is implemented in `TutteFormalization.Definitions`.
Structural dependencies are proved in the imported project modules.
-/

namespace TutteFormalization

/-- `thm:path-theorem`, the two-endpoints-off-cut BJL formulation.
The public type is unchanged from the approved independent specification.-/
theorem path_theorem {α : Type*} (M : Matroid α) [M.Finite]
    (hM : Connected M) (Γ : Set (Set α)) (hΓ : ModularCut M Γ)
    (F : Set α) (hF : Indecomposable M F) (hFproper : F ≠ M.E)
    (X Y : Set α) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  exact path_theorem_induction M hM Γ hΓ F hF hFproper X Y hX hY hFX hFY hXoff hYoff

end TutteFormalization
