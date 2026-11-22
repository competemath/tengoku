import Tengoku.Leancert.LeanCert.Analysis.DBN.Theta
import Tengoku.Seed.Analysis.Calculus.SmoothSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Twice differentiating the actual theta series, with local summable bounds. -/
namespace LeanCert.Analysis.DBN
open Set

noncomputable def thetaTermDeriv (u : ℝ) (n : ℕ) : ℝ :=
  (1 - 4 * (Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u))) * thetaTerm u n

/--
@isnad1 id=hasderiv.0h2v.s5.b78c87e06441 from=translated src=- shape=901746d8 vocab=e4322729
-/
theorem hasDerivAt_thetaTerm (u : ℝ) (n : ℕ) :
    HasDerivAt (fun v => thetaTerm v n) (thetaTermDeriv u n) u := by
  have he := (((hasDerivAt_id u).const_mul 4).exp.const_mul
    (-Real.pi * ((n : ℝ)+1)^2)).exp
  convert! (Real.hasDerivAt_exp u).mul he using 1
  simp only [thetaTerm, thetaTermDeriv, id_eq]
  ring

/--
@isnad1 id=hasderiv.0h2v.s6.dd217614b774 from=translated src=- shape=0ff630ea vocab=40e90858
-/
theorem hasDerivAt_thetaTermDeriv (u : ℝ) (n : ℕ) :
    HasDerivAt (fun v => thetaTermDeriv v n)
      (8 * kernelTerm u n + thetaTerm u n) u := by
  have he := (((hasDerivAt_id u).const_mul 4).exp.const_mul
    (4 * (Real.pi * ((n : ℝ)+1)^2))).const_sub 1
  have h9 : Real.exp (9*u) = Real.exp u * Real.exp (4*u)^2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (5*u) = Real.exp u * Real.exp (4*u) := by
    rw [← Real.exp_add]; congr 1; ring
  convert! he.mul (hasDerivAt_thetaTerm u n) using 1
  · funext v
    simp only [thetaTermDeriv, thetaTerm, Pi.mul_apply, id_eq]
    ring
  · simp only [thetaTermDeriv, thetaTerm, kernelTerm, id_eq, h9, h5]
    ring

/--
@isnad1 id=le.0h2v.s6.5e8bef5b0192 from=translated src=- shape=bf8232c0 vocab=de607326
-/
theorem thetaTerm_bound (u : ℝ) (n : ℕ) :
    ‖thetaTerm u n‖ ≤ Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
  rw [thetaTerm, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos u).le
  apply Real.exp_le_exp.mpr
  dsimp [kernelScale]
  have h : 0 ≤ Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u) := by positivity
  nlinarith

/--
@isnad1 id=le.0h2v.s6.22484ccfcca6 from=translated src=- shape=53cfd665 vocab=dcd040f0
-/
theorem thetaTermDeriv_bound (u : ℝ) (n : ℕ) :
    ‖thetaTermDeriv u n‖ ≤ 9 * Real.exp u *
      Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
  let x := Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h1 := pow_mul_exp_neg_le x hx 1
  norm_num at h1
  have h0 : Real.exp (-x) ≤ Real.exp (-x/2) := by gcongr; linarith
  have hab : |1-4*x| ≤ 1+4*x := by rw [abs_le]; constructor <;> linarith
  have hh := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-x)).le
  have he : -x/2 = -kernelScale u * ((n : ℝ)+1)^2 := by dsimp [x, kernelScale]; ring
  have hb : |1-4*x| * Real.exp (-x) ≤ 9 * Real.exp (-x/2) := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (Real.exp_pos u).le
  rw [he] at hb'
  have hex : -Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u) = -x := by
    dsimp [x]; ring
  simp only [thetaTermDeriv, thetaTerm, hex]
  change ‖(1-4*x) * (Real.exp u * Real.exp (-x))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  nlinarith

/-- A common envelope on a bounded real interval; the lower endpoint controls Gaussian decay. -/
noncomputable def thetaEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  Real.exp b * Real.exp (-kernelScale a * ((n : ℝ)+1)^2)

/--
@isnad1 id=summable.0h2v.s4.e4cc01b1ae8b from=translated src=- shape=ddf3513c vocab=3dbcba12
-/
theorem summable_thetaEnvelope (a b : ℝ) : Summable (thetaEnvelope a b) := by
  apply (SeriesTail.of_gaussian (thetaEnvelope a b) 0 (Real.exp b) (kernelScale a)
    (Real.exp_pos _).le (kernelScale_pos a) ?_).1
  intro n
  simp only [Nat.add_zero, thetaEnvelope]
  rw [Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos b).le
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (n : ℝ) := by positivity
  nlinarith [kernelScale_pos a]

/--
@isnad1 id=le.2h4v.s6.082c50a4d382 from=translated src=- shape=4161cec8 vocab=4c315722
-/
theorem thetaEnvelope_mono {a b u : ℝ} (ha : a ≤ u) (hb : u ≤ b) (n : ℕ) :
    Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2) ≤ thetaEnvelope a b n := by
  unfold thetaEnvelope kernelScale
  gcongr

private theorem second_bound (u : ℝ) (n : ℕ) :
    ‖8 * kernelTerm u n + thetaTerm u n‖ ≤
      177 * (Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2)) := by
  calc
    _ ≤ ‖8 * kernelTerm u n‖ + ‖thetaTerm u n‖ := norm_add_le _ _
    _ ≤ 8 * (22 * Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2)) +
        Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
      gcongr
      · exact kernelTerm_bound u n
      · exact thetaTerm_bound u n
    _ = _ := by ring

/--
@isnad1 id=summable.0h1v.s3.88952d267543 from=translated src=- shape=07cc7679 vocab=8c45e500
-/
theorem summable_thetaTermDeriv (u : ℝ) : Summable (thetaTermDeriv u) := by
  apply ((summable_thetaEnvelope u u).mul_left 9).of_norm_bounded
  intro n
  simpa [thetaEnvelope, mul_assoc] using thetaTermDeriv_bound u n

/--
@isnad1 id=hasderiv.0h1v.s5.aba155e9af39 from=translated src=- shape=e81bc03f vocab=b033d86f
-/
theorem hasDerivAt_thetaPrimitive (u : ℝ) :
    HasDerivAt thetaPrimitive (∑' n, thetaTermDeriv u n) u := by
  have hm : u ∈ Ioo (u-1) (u+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_thetaEnvelope (u-1) (u+1)).mul_left 9) isOpen_Ioo
    (convex_Ioo (u-1) (u+1)).isPreconnected
    (fun n v (_ : v ∈ Ioo (u-1) (u+1)) => hasDerivAt_thetaTerm v n)
    (fun n v (hv : v ∈ Ioo (u-1) (u+1)) =>
      (thetaTermDeriv_bound v n).trans (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (thetaEnvelope_mono hv.1.le hv.2.le n) (by norm_num : (0 : ℝ) ≤ 9)))
    hm (hasSum_thetaTerm u).summable hm
  simpa only [← thetaPrimitive_eq_tsum] using h

/--
@isnad1 id=eq.0h1v.s5.503ba8a969c5 from=translated src=- shape=d14c5276 vocab=7676aef6
-/
theorem deriv_thetaPrimitive (u : ℝ) : deriv thetaPrimitive u = ∑' n, thetaTermDeriv u n :=
  (hasDerivAt_thetaPrimitive u).deriv

/-- The second derivative is the actual, convergent DBN kernel series plus the primitive.
@isnad1 id=hasderiv.0h1v.s6.a752405227ca from=translated src=- shape=b9e5357c vocab=ed033e2d
-/
theorem hasDerivAt_deriv_thetaPrimitive (u : ℝ) :
    HasDerivAt (deriv thetaPrimitive) (8 * Phi u + thetaPrimitive u) u := by
  have hm : u ∈ Ioo (u-1) (u+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_thetaEnvelope (u-1) (u+1)).mul_left 177) isOpen_Ioo
    (convex_Ioo (u-1) (u+1)).isPreconnected
    (fun n v (_ : v ∈ Ioo (u-1) (u+1)) => hasDerivAt_thetaTermDeriv v n)
    (fun n v (hv : v ∈ Ioo (u-1) (u+1)) =>
      (second_bound v n).trans (mul_le_mul_of_nonneg_left
        (thetaEnvelope_mono hv.1.le hv.2.le n) (by norm_num)))
    hm (summable_thetaTermDeriv u) hm
  have he : deriv thetaPrimitive = fun v => ∑' n, thetaTermDeriv v n :=
    funext deriv_thetaPrimitive
  rw [he]
  convert! h using 1
  rw [((kernel_summable u).mul_left 8).tsum_add (hasSum_thetaTerm u).summable,
    tsum_mul_left, (hasSum_thetaTerm u).tsum_eq]
  rfl

/-- Exact differential identity needed for the twice-integrated cosine transform.
@isnad1 id=eq.0h1v.s6.3046d3fa14ce from=translated src=- shape=400b28f2 vocab=a679f1d9
-/
theorem Phi_eq_thetaPrimitive_deriv2 (u : ℝ) :
    Phi u = (deriv (deriv thetaPrimitive) u - thetaPrimitive u) / 8 := by
  rw [(hasDerivAt_deriv_thetaPrimitive u).deriv]
  ring

end LeanCert.Analysis.DBN
