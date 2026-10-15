import Tengoku.NavierStokesEuler.Euler.TransverseGramInverse

/-! Compatible spatial maps commute with the genuine positive Gram inverse. -/

noncomputable section

namespace EulerGramNaturality

open ContinuousLinearMap InnerProductSpace EulerTransverseGramInverse

variable {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
@isnad1 id=eq.1h9v.s13.fa982b7dbcbb from=translated src=- shape=ac2e599f vocab=4f2552a1
-/
theorem adjoint_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : U →L[ℝ] E) (R : V →L[ℝ] F)
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (f : E) :
    R.adjoint (B f) = A (Q.adjoint f) := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left,← adjoint_inner_right,← hback,
    ← adjoint_inner_left,adjoint_inner_right]

/--
@isnad1 id=eq.2h9v.s12.3cec17a582e4 from=translated src=- shape=cbeb4ede vocab=daf56dcc
-/
theorem gram_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : U →L[ℝ] E) (R : V →L[ℝ] F)
    (hforward : ∀ u, R (A u) = B (Q u))
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (u : U) :
    gram R (A u) = A (gram Q u) := by
  change R.adjoint (R (A u)) = _
  rw [hforward,adjoint_intertwines A B Q R hback]
  rfl

/--
@isnad1 id=eq.6h11v.s12.2c8dead91e41 from=translated src=- shape=294f44f5 vocab=01e8d6dc
-/
theorem gramInverse_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : U →L[ℝ] E) (R : V →L[ℝ] F)
    (c : ℝ) (hc : 0 < c) (hQ : ∀ u, c*‖u‖^2 ≤ ‖Q u‖^2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ v, d*‖v‖^2 ≤ ‖R v‖^2)
    (hforward : ∀ u, R (A u) = B (Q u))
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (f : U) :
    gramInverse R d hd hR (A f) = A (gramInverse Q c hc hQ f) := by
  have he := gram_intertwines A B Q R hforward hback (gramInverse Q c hc hQ f)
  rw [gram_inverse_apply] at he
  have hi := congrArg (gramInverse R d hd hR) he
  rw [inverse_gram_apply] at hi
  exact hi.symm

/-- In particular the actual acceleration formula respects a compatible
coordinate map and physical map.
@isnad1 id=eq.7h14v.s13.94df78c6feb1 from=translated src=- shape=957c472d vocab=4824b6cc
-/
theorem acceleration_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : U →L[ℝ] E) (R R₁ : V →L[ℝ] F)
    (c : ℝ) (hc : 0 < c) (hQ : ∀ u, c*‖u‖^2 ≤ ‖Q u‖^2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ v, d*‖v‖^2 ≤ ‖R v‖^2)
    (hforward : ∀ u, R (A u) = B (Q u))
    (hforward₁ : ∀ u, R₁ (A u) = B (Q₁ u))
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (f : E) (v : U) :
    gramInverse R d hd hR (R.adjoint (B f-(2 : ℝ) • R₁ (A v))) =
      A (gramInverse Q c hc hQ (Q.adjoint (f-(2 : ℝ) • Q₁ v))) := by
  rw [hforward₁,← map_smul,← map_sub,adjoint_intertwines A B Q R hback,
    gramInverse_intertwines A B Q R c hc hQ d hd hR hforward hback]

end EulerGramNaturality
