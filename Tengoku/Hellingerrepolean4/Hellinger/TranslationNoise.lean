import Tengoku.Hellingerrepolean4.Hellinger.FiniteChannel
import Tengoku.Seed.Algebra.Group.Units.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms convolution_preserves_mean` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms convolution_objective_le` (it only prints; the queue checks the axioms of every declaration). -/

/-! Additional convolution noise as a uniform-measure-preserving channel.
This supplies the Jensen step in the linear-quotient argument; the identification
of a quotient posterior with this convolution is a separate remaining step. -/

set_option autoImplicit false
open scoped BigOperators

namespace Hellinger

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def convolution (p f : G → ℝ) (x : G) : ℝ :=
  ∑ e, p e * f (x + e)

noncomputable def translationChannel (p : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1) : UniformChannel G where
  weight x y := p (y - x)
  nonneg x y := hp (y - x)
  row_sum x := by
    calc
      (∑ y, p (y - x)) = ∑ e, p e := (Equiv.subRight x).sum_comp p
      _ = 1 := hs
  column_sum y := by
    calc
      (∑ x, p (y - x)) = ∑ e, p e := (Equiv.subLeft y).sum_comp p
      _ = 1 := hs

/--
@isnad1 id=eq.2h4v.s6.30568484eccd from=translated src=- shape=d12026f7 vocab=7f52ee13
-/
theorem translationChannel_apply (p f : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1) (x : G) :
    (translationChannel p hp hs).apply f x = convolution p f x := by
  unfold UniformChannel.apply translationChannel convolution
  symm
  apply Fintype.sum_equiv (Equiv.addLeft x)
  intro e
  simp

/--
@isnad1 id=eq.2h3v.s6.b3e1fcb4d0a1 from=translated src=- shape=f06f3676 vocab=7e64f518
-/
theorem convolution_preserves_mean (p f : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1) :
    mean (convolution p f) = mean f := by
  have hfun : (translationChannel p hp hs).apply f = convolution p f := by
    funext x
    exact translationChannel_apply p f hp hs x
  rw [← hfun]
  exact UniformChannel.mean_apply _ _

/--
@isnad1 id=le.3h3v.s6.e32b296d2cbd from=translated src=- shape=7bb96498 vocab=1ffeb528
-/
theorem convolution_objective_le (p f : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    objective (convolution p f) ≤ objective f := by
  have hfun : (translationChannel p hp hs).apply f = convolution p f := by
    funext x
    exact translationChannel_apply p f hp hs x
  rw [← hfun]
  exact objective_channel_le _ _ hf

end Hellinger
