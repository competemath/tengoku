import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PolynomialPullback
import Tengoku.Seed.Analysis.Calculus.Deriv.Star

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set
open scoped ComplexConjugate

namespace Erdos1133

def bernsteinAffine (f : ℂ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  f ((a : ℂ) * z + b)

theorem IsBernsteinFunction.affine {σ H : ℝ} {f : ℂ → ℂ}
    (hf : IsBernsteinFunction σ H f) (a b : ℝ) :
    IsBernsteinFunction (σ * |a|) H (bernsteinAffine f a b) := by
  rcases hf with ⟨hd, hr, K, hK, hbound⟩
  refine ⟨?_, ?_, K, hK, ?_⟩
  · unfold bernsteinAffine
    exact hd.comp (by fun_prop)
  · intro t
    simpa [bernsteinAffine, ← Complex.ofReal_mul, ← Complex.ofReal_add] using hr (a * t + b)
  · intro z
    simpa [bernsteinAffine, Complex.mul_im, abs_mul, mul_assoc] using
      hbound ((a : ℂ) * z + b)

def bernsteinReflection (f : ℂ → ℂ) (z : ℂ) : ℂ := conj (f (conj z))

theorem bernsteinReflection_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (bernsteinReflection f) := by
  intro z
  exact differentiableAt_conj_conj_iff.mpr (hf (conj z))

theorem IsBernsteinFunction.reflection {σ H : ℝ} {f : ℂ → ℂ}
    (hf : IsBernsteinFunction σ H f) :
    IsBernsteinFunction σ H (bernsteinReflection f) := by
  rcases hf with ⟨hd, hr, K, hK, hbound⟩
  refine ⟨bernsteinReflection_entire hd, ?_, K, hK, ?_⟩
  · intro t
    simpa [bernsteinReflection] using hr t
  · intro z
    simpa [bernsteinReflection] using hbound (conj z)

def bernsteinRealification (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (f z + bernsteinReflection f z) / 2

theorem bernsteinRealification_real (f : ℂ → ℂ) (t : ℝ) :
    bernsteinRealification f t = ((f t).re : ℂ) := by
  apply Complex.ext <;>
    simp [bernsteinRealification, bernsteinReflection, Complex.div_re, Complex.div_im] <;> ring

theorem bernsteinRealification_real_value {f : ℂ → ℂ} {t y : ℝ}
    (h : f t = (y : ℂ)) : bernsteinRealification f t = (y : ℂ) := by
  rw [bernsteinRealification_real, h]
  simp

theorem bernsteinRealification_im (f : ℂ → ℂ) (t : ℝ) :
    (bernsteinRealification f t).im = 0 := by
  rw [bernsteinRealification_real]
  simp

theorem IsBernsteinFunction.realification {σ H : ℝ} {f : ℂ → ℂ}
    (hf : IsBernsteinFunction σ H f) :
    IsBernsteinFunction σ H (bernsteinRealification f) := by
  obtain ⟨hd, hr, K, hK, hb⟩ := hf
  refine ⟨?_, ?_, K, hK, ?_⟩
  · exact (hd.add (bernsteinReflection_entire hd)).div_const 2
  · intro t
    rw [bernsteinRealification_real, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hr t)
  · intro z
    have href : ‖bernsteinReflection f z‖ ≤ K * Real.exp (σ * |z.im|) := by
      simpa [bernsteinReflection] using hb (conj z)
    calc
      ‖bernsteinRealification f z‖ = ‖f z + bernsteinReflection f z‖ / 2 := by
        simp [bernsteinRealification, norm_div]
      _ ≤ (‖f z‖ + ‖bernsteinReflection f z‖) / 2 := by
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ ≤ K * Real.exp (σ * |z.im|) := by linarith [hb z]

end Erdos1133
