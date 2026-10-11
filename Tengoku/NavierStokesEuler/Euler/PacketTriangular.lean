import Tengoku.NavierStokesEuler.Euler.PacketPointJets
import Tengoku.NavierStokesEuler.Euler.FiniteGradeTriangular

/-! The actual nonlinear packet operators have the triangular dependence claimed in (14). -/

noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerFiniteGrades InnerProductSpace

theorem fastAdvection_tangent_left (m : Space) (J K : VectorJet)
    (hJ : ⟪m, J.1⟫_ℝ=0) : fastAdvection m J K=0 := by
  simp [fastAdvection, hJ]

theorem fastAdvection_angleConstant_right (m : Space) (J K : VectorJet)
    (hK : K.2 angleDirection=0) : fastAdvection m J K=0 := by
  simp [fastAdvection, hK]

def nonlinearGrade (M p : ℕ) (FInv : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → VectorJet) : Space :=
  convolution M (slowAdvection FInv) u u p + convolution M (fastAdvection m) u u (p+1)

end EulerPacketPointJets
