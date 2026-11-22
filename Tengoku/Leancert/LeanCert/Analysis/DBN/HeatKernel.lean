import Tengoku.Leancert.LeanCert.Analysis.PolynomialDecay
import Tengoku.Leancert.LeanCert.Analysis.GaussianTail
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Complex
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic
import Tengoku.Seed.Analysis.Real.Pi.Bounds
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The de Bruijn–Newman kernel, with the n+1 indexing and normalization
used by the downstream definition. No downstream analytic assertions are imported. -/
namespace LeanCert.Analysis.DBN

noncomputable def kernelTerm (u : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi^2 * ((n : ℝ)+1)^4 * Real.exp (9*u) -
    3 * Real.pi * ((n : ℝ)+1)^2 * Real.exp (5*u)) *
    Real.exp (-Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u))

noncomputable def Phi (u : ℝ) : ℝ := ∑' n, kernelTerm u n

/-- Dimensionless Gaussian variable for an individual kernel summand. -/
noncomputable def kernelScale (u : ℝ) : ℝ := Real.pi * Real.exp (4*u) / 2

/--
@isnad1 id=lt.0h1v.s3.7c8b75f5cf4e from=translated src=- shape=8a62b088 vocab=12c00342
-/
theorem kernelScale_pos (u : ℝ) : 0 < kernelScale u := by
  unfold kernelScale
  positivity

private theorem term_rewrite (u : ℝ) (n : ℕ) :
    kernelTerm u n =
      (2*(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))^2 -
        3*(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))) * Real.exp u *
        Real.exp (-(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))) := by
  have h9 : Real.exp (9*u) = Real.exp (4*u)^2 * Real.exp u := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have h5 : Real.exp (5*u) = Real.exp (4*u) * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold kernelTerm
  rw [h9, h5]
  simp only [neg_mul]
  ring

/-- The actual signed summand is bounded by a Gaussian, for every real u.
@isnad1 id=le.0h2v.s6.9e1cd7652a28 from=translated src=- shape=53cfd665 vocab=3ee868fe
-/
theorem kernelTerm_bound (u : ℝ) (n : ℕ) :
    ‖kernelTerm u n‖ ≤ 22 * Real.exp u *
      Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
  let x := Real.pi*((n : ℝ)+1)^2*Real.exp (4*u)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h1 := pow_mul_exp_neg_le x hx 1
  have h2 := pow_mul_exp_neg_le x hx 2
  norm_num at h1 h2
  have hab : |2*x^2-3*x| ≤ 2*x^2+3*x := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x]
  have hh : |2*x^2-3*x| * Real.exp (-x) ≤ 22*Real.exp (-x/2) := by
    have h := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-x)).le
    nlinarith
  rw [term_rewrite]
  change ‖(2*x^2-3*x)*Real.exp u*Real.exp (-x)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos u),
    abs_of_pos (Real.exp_pos (-x))]
  have he : -x/2 = -kernelScale u * ((n : ℝ)+1)^2 := by dsimp [x, kernelScale]; ring
  have h := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [he] at h
  nlinarith

/-- Summability and a cutoff-explicit remainder for the actual Phi series.
The first omitted summand has positive index N+1.
@isnad1 id=and.0h2v.s7.c0a5ea133989 from=translated src=- shape=edf565db vocab=17a3c27b
-/
theorem kernel_tail (u : ℝ) (N : ℕ) :
    Summable (kernelTerm u) ∧
      ‖Phi u - ∑ n ∈ Finset.range N, kernelTerm u n‖ ≤
        22 * Real.exp u * Real.exp (-kernelScale u * ((N : ℝ)+1)^2) /
          (1 - Real.exp (-kernelScale u * (2*((N : ℝ)+1)+1))) := by
  apply SeriesTail.of_geometric
  · exact (Real.exp_pos _).le
  · rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (kernelScale_pos u)) (by positivity)
  · intro k
    have h := kernelTerm_bound u (k+N)
    have hg := SeriesTail.gaussian_le_geometric (kernelScale u) (kernelScale_pos u).le (N+1) k
    push_cast at h hg ⊢
    have he : (k : ℝ)+(N : ℝ)+1 = (k : ℝ)+((N : ℝ)+1) := by ring
    rw [he] at h
    exact h.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg
        (show 0 ≤ 22*Real.exp u by positivity))

/--
@isnad1 id=summable.0h1v.s3.9891d65609d2 from=translated src=- shape=07cc7679 vocab=c3deb77c
-/
theorem kernel_summable (u : ℝ) : Summable (kernelTerm u) := (kernel_tail u 0).1

/--
@isnad1 id=summable.0h1v.s4.e952d41c8b54 from=translated src=- shape=7ebc25e0 vocab=5db80df5
-/
theorem kernel_norm_summable (u : ℝ) : Summable (fun n => ‖kernelTerm u n‖) :=
  (kernel_summable u).norm

/-- Explicit envelope of Phi on the whole real line, decaying
super-exponentially as u tends to positive infinity.
@isnad1 id=le.0h1v.s6.97d9ebaf0992 from=translated src=- shape=df6043c8 vocab=1a2c72c4
-/
theorem Phi_bound (u : ℝ) :
    ‖Phi u‖ ≤ 22 * Real.exp u * Real.exp (-kernelScale u) /
      (1 - Real.exp (-3*kernelScale u)) := by
  have h := (kernel_tail u 0).2
  norm_num at h
  simpa only [Real.norm_eq_abs, neg_mul, mul_comm] using h

/--
@isnad1 id=le.0h1v.s4.8289279455e6 from=translated src=- shape=1d386cdc vocab=1dee6963
-/
theorem kernelScale_ge_exp {u : ℝ} : Real.exp (4*u) ≤ kernelScale u := by
  have hp := Real.pi_gt_three
  have he := Real.exp_pos (4*u)
  unfold kernelScale
  nlinarith

/--
@isnad1 id=le.1h1v.s4.b0ba6d0521af from=translated src=- shape=35bd48ee vocab=7dd3e9e2
-/
theorem kernelScale_ge_one {u : ℝ} (hu : 0 ≤ u) : 1 ≤ kernelScale u :=
  (Real.one_le_exp (by positivity)).trans kernelScale_ge_exp

/-- On the integration half-line the denominator in the series envelope is
uniformly bounded away from zero.
@isnad1 id=le.1h1v.s5.3a04177633c4 from=translated src=- shape=9fa28730 vocab=f72419b9
-/
theorem Phi_bound_nonneg {u : ℝ} (hu : 0 ≤ u) :
    ‖Phi u‖ ≤ 44 * Real.exp (u - kernelScale u) := by
  have ha := kernelScale_ge_one hu
  have hr : Real.exp (-3*kernelScale u) ≤ 1/2 := by
    rw [neg_mul, Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Real.add_one_le_exp (3*kernelScale u)]
  have hd : 0 < 1 - Real.exp (-3*kernelScale u) := by linarith
  apply (Phi_bound u).trans
  apply (div_le_iff₀ hd).mpr
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
  have hn : 0 ≤ Real.exp u * Real.exp (-kernelScale u) := by positivity
  nlinarith [mul_nonneg hn (show 0 ≤ 1/2 - Real.exp (-3*kernelScale u) by linarith)]

/-- Measurability of the actual series, not an assumed kernel regularity fact.
@isnad1 id=measurab.0h0v.s2.8e550e161dc1 from=translated src=- shape=e3d48bcb vocab=0e14750c
-/
theorem measurable_Phi : Measurable Phi := by
  apply Measurable.tsum
  intro n
  unfold kernelTerm
  fun_prop

/-- Every summand of the actual kernel is positive on the integration domain.
@isnad1 id=lt.1h2v.s4.ac2a5b6e81dc from=translated src=- shape=902071bf vocab=b5b41441
-/
theorem kernelTerm_pos {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 < kernelTerm u n := by
  rw [term_rewrite]
  have hn : 1 ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by positivity)
  have hx : 3 < Real.pi*((n : ℝ)+1)^2*Real.exp (4*u) := by
    have h := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
    have h' := mul_le_mul_of_nonneg_left he
      (show 0 ≤ Real.pi*((n : ℝ)+1)^2 by positivity)
    nlinarith [Real.pi_gt_three]
  apply mul_pos (mul_pos ?_ (Real.exp_pos _)) (Real.exp_pos _)
  nlinarith

/-- In particular, the defining series cannot cancel on the positive half-line.
@isnad1 id=lt.1h1v.s4.ab59064901bc from=translated src=- shape=a8dc2df9 vocab=ca2e6374
-/
theorem Phi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < Phi u := by
  exact (kernel_summable u).tsum_pos (fun n => (kernelTerm_pos hu n).le) 0 (kernelTerm_pos hu 0)

end LeanCert.Analysis.DBN
