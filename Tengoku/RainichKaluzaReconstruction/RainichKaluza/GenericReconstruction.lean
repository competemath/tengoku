import Tengoku.RainichKaluzaReconstruction.RainichKaluza.AlgebraicFingerprint
import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generic eigenbasis reconstruction

This file formalizes the scalar algebra that appears after diagonalizing the
Ricci endomorphism on the proposed generic branch. It is not yet a theorem
that every Lorentzian Ricci endomorphism admits the required real eigenbasis.

If the non-protected eigenvalues are `a` and `b`, their sum is the Ricci trace.
The diagonal entries of a solution to

`R V + V R - tr(R) V = R² - q² I`

are forced to be the quantities below whenever `a ≠ b`. The off-diagonal
`a,b` entry is resonant because `a + b = tr(R)` and is subsequently fixed by
the rank-one condition.
-/

namespace RainichKaluza

/-- Forced diagonal entry in the `a` eigendirection.-/
noncomputable def reconstructedDiagonalA (a b qSq : ℝ) : ℝ :=
  (a ^ 2 - qSq) / (a - b)

/-- Forced diagonal entry in the `b` eigendirection.-/
noncomputable def reconstructedDiagonalB (a b qSq : ℝ) : ℝ :=
  (b ^ 2 - qSq) / (b - a)

/-- The reconstructed `a` diagonal solves its Sylvester component equation.
@isnad1 id=eq.1h3v.s6.91d2b209c970 from=translated src=- shape=89f30c21 vocab=2b59317b
-/
theorem reconstructedDiagonalA_solves
    (a b qSq : ℝ) (hab : a ≠ b) :
    (2 * a - (a + b)) * reconstructedDiagonalA a b qSq =
      a ^ 2 - qSq := by
  simp [reconstructedDiagonalA]
  field_simp [sub_ne_zero.mpr hab]
  ring

/-- The reconstructed `b` diagonal solves its Sylvester component equation.
@isnad1 id=eq.1h3v.s6.bfe1863ad7ca from=translated src=- shape=a1c8b165 vocab=84c1bbed
-/
theorem reconstructedDiagonalB_solves
    (a b qSq : ℝ) (hab : a ≠ b) :
    (2 * b - (a + b)) * reconstructedDiagonalB a b qSq =
      b ^ 2 - qSq := by
  simp [reconstructedDiagonalB]
  field_simp [sub_ne_zero.mpr hab]
  ring

/-- **Trace compatibility.** The two forced diagonal entries automatically
sum to the Ricci trace `a + b`; it is not an additional assumption.
@isnad1 id=eq.1h3v.s5.3886b6d23f20 from=translated src=- shape=1228fdd9 vocab=5fede352
-/
theorem reconstructedDiagonal_sum
    (a b qSq : ℝ) (hab : a ≠ b) :
    reconstructedDiagonalA a b qSq +
      reconstructedDiagonalB a b qSq = a + b := by
  simp [reconstructedDiagonalA, reconstructedDiagonalB]
  field_simp [sub_ne_zero.mpr hab]
  ring

/-- Product identity controlling real rank-one completion of the unprotected
two-dimensional block.
@isnad1 id=eq.1h3v.s6.5d7152560cdb from=translated src=- shape=ddbe5ee8 vocab=f58d3192
-/
theorem reconstructedDiagonal_product
    (a b qSq : ℝ) (hab : a ≠ b) :
    reconstructedDiagonalA a b qSq *
      reconstructedDiagonalB a b qSq =
        -((a ^ 2 - qSq) * (b ^ 2 - qSq)) / (a - b) ^ 2 := by
  simp [reconstructedDiagonalA, reconstructedDiagonalB]
  field_simp [sub_ne_zero.mpr hab]
  ring

/-- A symmetric two-by-two block has a real rank-one completion with prescribed
diagonal entries exactly when their product is nonnegative.
@isnad1 id=iff.0h2v.s5.1bab0a907d58 from=translated src=- shape=49838cbd vocab=150e4428
-/
theorem exists_real_rankOne_completion_iff (u v : ℝ) :
    (∃ x : ℝ, x ^ 2 = u * v) ↔ 0 ≤ u * v := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact sq_nonneg x
  · intro huv
    exact ⟨Real.sqrt (u * v), Real.sq_sqrt huv⟩

/-- **Generic real-completion criterion.** A real symmetric rank-one completion
of the forced block exists exactly when `qSq` lies between `a²` and `b²` in
the product-order sense. This is an algebraic admissibility condition, before
Lorentzian causal-sign restrictions are imposed.
@isnad1 id=iff.1h3v.s6.99bcfb1af853 from=translated src=- shape=e437493a vocab=b133609f
-/
theorem exists_reconstructed_rankOne_completion_iff
    (a b qSq : ℝ) (hab : a ≠ b) :
    (∃ x : ℝ, x ^ 2 =
      reconstructedDiagonalA a b qSq *
        reconstructedDiagonalB a b qSq) ↔
      (a ^ 2 - qSq) * (b ^ 2 - qSq) ≤ 0 := by
  rw [exists_real_rankOne_completion_iff]
  rw [reconstructedDiagonal_product a b qSq hab]
  have hgap : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  rw [div_nonneg_iff]
  constructor
  · rintro (⟨hnum, _⟩ | ⟨_, hden⟩)
    · linarith
    · exact (not_le_of_gt hgap hden).elim
  · intro hproduct
    exact Or.inl ⟨by linarith, le_of_lt hgap⟩

/-- Off-diagonal Sylvester components vanish away from the complementary
eigenvalue resonance.
@isnad1 id=eq.2h4v.s6.630bd62f6aa2 from=translated src=- shape=dabb0d28 vocab=b5c6e8b6
-/
theorem offDiagonal_eq_zero_of_nonresonant
    (trace lambda mu entry : ℝ)
    (hnonresonant : lambda + mu - trace ≠ 0)
    (heq : (lambda + mu - trace) * entry = 0) :
    entry = 0 := by
  exact (mul_eq_zero.mp heq).resolve_left hnonresonant

/-- The `a,b` off-diagonal component is algebraically unconstrained by the
Sylvester equation because the two eigenvalues sum to the trace.
@isnad1 id=eq.0h3v.s5.cf366162ae24 from=translated src=- shape=5b9fae27 vocab=b5c6e8b6
-/
theorem complementary_offDiagonal_is_resonant
    (a b entry : ℝ) :
    (a + b - (a + b)) * entry = 0 := by
  ring

/-- A protected diagonal component is forced to vanish when its Sylvester
coefficient is nonzero.
@isnad1 id=eq.3h4v.s7.00613af14a32 from=translated src=- shape=7f18c1b2 vocab=e8d9ab0e
-/
theorem protectedDiagonal_eq_zero
    (trace q qSq entry : ℝ)
    (hq : q ^ 2 = qSq)
    (hnonresonant : 2 * q - trace ≠ 0)
    (heq : (2 * q - trace) * entry = q ^ 2 - qSq) :
    entry = 0 := by
  rw [hq, sub_self] at heq
  exact (mul_eq_zero.mp heq).resolve_left hnonresonant

end RainichKaluza
