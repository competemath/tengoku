import Tengoku.RainichKaluzaReconstruction.RainichKaluza.FullSpectralProjector
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential identities for spectral projectors

This file isolates the algebra obeyed by a covariant derivative of a smooth
spectral projector.  The symbols `dR`, `dp`, and `da` represent evaluation of
`∇R`, `∇p`, and `da` on one tangent direction.  The theorems do not yet build
those geometric objects; they prove the basis-free identities that every such
evaluation must satisfy.

For a target projector `p` with root `a` and a complementary projector `q`
with root `b`, differentiating `Rp=ap` and projecting gives

`(a-b) q(dp) = q(dR)p`.

Thus all off-diagonal components of `∇p` are determined by `∇R` and the
spectral gaps.  Derivatives of the eigenvalues cancel from these components.
-/

namespace RainichKaluza

variable {A : Type*} [Ring A] [Algebra ℝ A]

omit [Algebra ℝ A] in
/-- Differentiating `p²=p` forces the derivative to have no target-to-target
block.
@isnad1 id=eq.2h3v.s6.578e42e3ca1e from=translated src=- shape=00962635 vocab=309b5614
-/
theorem projectorDerivative_target_block_zero
    (p dp : A) (hp : p * p = p)
    (hdiff : dp * p + p * dp = dp) :
    p * dp * p = 0 := by
  have hleft := congrArg (fun z : A => p * z) hdiff
  simpa only [mul_add, ← mul_assoc, hp, add_eq_right] using hleft

/-- Left off-diagonal derivative identity obtained by differentiating
`Rp=ap` and projecting with a complementary left eigenspace projector.
@isnad1 id=eq.3h9v.s8.fb5fc81f3ffd from=translated src=- shape=f6226e3c vocab=dc89dc06
-/
theorem spectralProjectorDerivative_left_scaled
    (R dR p dp q : A) (a b da : ℝ)
    (hqR : q * R = b • q) (hqp : q * p = 0)
    (hdiff : dR * p + R * dp = da • p + a • dp) :
    (a - b) • (q * dp) = q * dR * p := by
  have hleft := congrArg (fun z : A => q * z) hdiff
  have hcore : q * dR * p + b • (q * dp) = a • (q * dp) := by
    rw [mul_add, mul_add] at hleft
    rw [← mul_assoc q R dp, hqR, smul_mul_assoc] at hleft
    rw [mul_smul_comm, hqp, smul_zero, zero_add, mul_smul_comm] at hleft
    simpa only [mul_assoc] using hleft
  calc
    (a - b) • (q * dp) = a • (q * dp) - b • (q * dp) := by module
    _ = (q * dR * p + b • (q * dp)) - b • (q * dp) := by rw [← hcore]
    _ = q * dR * p := by abel

/-- Right off-diagonal derivative identity obtained by differentiating
`pR=ap` and projecting with a complementary right eigenspace projector.
@isnad1 id=eq.3h9v.s8.ab0833632412 from=translated src=- shape=c3086e48 vocab=dc89dc06
-/
theorem spectralProjectorDerivative_right_scaled
    (R dR p dp q : A) (a b da : ℝ)
    (hRq : R * q = b • q) (hpq : p * q = 0)
    (hdiff : dp * R + p * dR = da • p + a • dp) :
    (a - b) • (dp * q) = p * dR * q := by
  have hright := congrArg (fun z : A => z * q) hdiff
  have hcore : b • (dp * q) + p * dR * q = a • (dp * q) := by
    simpa only [add_mul, mul_assoc, hRq, hpq, smul_zero, zero_add,
      smul_mul_assoc, mul_smul_comm] using hright
  calc
    (a - b) • (dp * q) = a • (dp * q) - b • (dp * q) := by module
    _ = (b • (dp * q) + p * dR * q) - b • (dp * q) := by rw [← hcore]
    _ = p * dR * q := by abel

/-- Division by a nonzero spectral gap explicitly reconstructs the left
off-diagonal component of the projector derivative.
@isnad1 id=eq.4h9v.s8.ea5d8d90a43c from=translated src=- shape=65893d09 vocab=3d5934f5
-/
theorem spectralProjectorDerivative_left
    (R dR p dp q : A) (a b da : ℝ) (hab : a ≠ b)
    (hqR : q * R = b • q) (hqp : q * p = 0)
    (hdiff : dR * p + R * dp = da • p + a • dp) :
    q * dp = (a - b)⁻¹ • (q * dR * p) := by
  have hgap : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hscaled := spectralProjectorDerivative_left_scaled
    R dR p dp q a b da hqR hqp hdiff
  calc
    q * dp = 1 • (q * dp) := (one_smul ℝ _).symm
    _ = ((a - b)⁻¹ * (a - b)) • (q * dp) := by
      congr 1
      exact (inv_mul_cancel₀ hgap).symm
    _ = (a - b)⁻¹ • ((a - b) • (q * dp)) := by rw [smul_smul]
    _ = (a - b)⁻¹ • (q * dR * p) := by rw [hscaled]

/-- Division by a nonzero spectral gap explicitly reconstructs the right
off-diagonal component of the projector derivative.
@isnad1 id=eq.4h9v.s8.b217f0889e0b from=translated src=- shape=09c10753 vocab=3d5934f5
-/
theorem spectralProjectorDerivative_right
    (R dR p dp q : A) (a b da : ℝ) (hab : a ≠ b)
    (hRq : R * q = b • q) (hpq : p * q = 0)
    (hdiff : dp * R + p * dR = da • p + a • dp) :
    dp * q = (a - b)⁻¹ • (p * dR * q) := by
  have hgap : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hscaled := spectralProjectorDerivative_right_scaled
    R dR p dp q a b da hRq hpq hdiff
  calc
    dp * q = 1 • (dp * q) := (one_smul ℝ _).symm
    _ = ((a - b)⁻¹ * (a - b)) • (dp * q) := by
      congr 1
      exact (inv_mul_cancel₀ hgap).symm
    _ = (a - b)⁻¹ • ((a - b) • (dp * q)) := by rw [smul_smul]
    _ = (a - b)⁻¹ • (p * dR * q) := by rw [hscaled]

omit [Algebra ℝ A] in
/-- The derivative of an idempotent has only off-diagonal blocks relative to
the splitting `p + (1-p)`.
@isnad1 id=eq.2h3v.s7.d5c9b0468840 from=translated src=- shape=cb1087b5 vocab=6f4456c2
-/
theorem projectorDerivative_eq_complement_blocks
    (p dp : A) (hp : p * p = p)
    (hdiff : dp * p + p * dp = dp) :
    dp = (1 - p) * dp * p + p * dp * (1 - p) := by
  have hzero := projectorDerivative_target_block_zero p dp hp hdiff
  calc
    dp = dp * p + p * dp := hdiff.symm
    _ = (1 - p) * dp * p + p * dp * (1 - p) := by
      simp only [sub_mul, one_mul, mul_sub, mul_one, hzero, sub_zero]

omit [Algebra ℝ A] in
/-- If three complementary projectors resolve the identity with `p`, the
derivative of `p` is the sum of its six target/complement off-diagonal
blocks.
@isnad1 id=eq.3h6v.s8.7a5354550c03 from=translated src=- shape=4fb76f10 vocab=309b5614
-/
theorem projectorDerivative_eq_three_complement_blocks
    (p dp q r s : A) (hp : p * p = p)
    (hsum : p + q + r + s = 1)
    (hdiff : dp * p + p * dp = dp) :
    dp = q * dp * p + r * dp * p + s * dp * p +
      p * dp * q + p * dp * r + p * dp * s := by
  have hcomp : 1 - p = q + r + s := by
    calc
      1 - p = (p + q + r + s) - p := by rw [hsum]
      _ = q + r + s := by noncomm_ring
  calc
    dp = (1 - p) * dp * p + p * dp * (1 - p) :=
      projectorDerivative_eq_complement_blocks p dp hp hdiff
    _ = q * dp * p + r * dp * p + s * dp * p +
        p * dp * q + p * dp * r + p * dp * s := by
      rw [hcomp]
      noncomm_ring

/-- Sandwiched left derivative block, in the form used by the complete
spectral derivative formula.
@isnad1 id=eq.5h9v.s8.a25beb73ccde from=translated src=- shape=b58d3d9f vocab=3d5934f5
-/
theorem spectralProjectorDerivative_left_block
    (R dR p dp q : A) (a b da : ℝ) (hab : a ≠ b)
    (hp : p * p = p)
    (hqR : q * R = b • q) (hqp : q * p = 0)
    (hdiff : dR * p + R * dp = da • p + a • dp) :
    q * dp * p = (a - b)⁻¹ • (q * dR * p) := by
  rw [spectralProjectorDerivative_left R dR p dp q a b da hab hqR hqp hdiff]
  rw [smul_mul_assoc, mul_assoc (q * dR) p p, hp]

/-- Sandwiched right derivative block, in the form used by the complete
spectral derivative formula.
@isnad1 id=eq.5h9v.s8.1d40a52ea5c1 from=translated src=- shape=9c368046 vocab=3d5934f5
-/
theorem spectralProjectorDerivative_right_block
    (R dR p dp q : A) (a b da : ℝ) (hab : a ≠ b)
    (hp : p * p = p)
    (hRq : R * q = b • q) (hpq : p * q = 0)
    (hdiff : dp * R + p * dR = da • p + a • dp) :
    p * dp * q = (a - b)⁻¹ • (p * dR * q) := by
  rw [mul_assoc p dp q]
  rw [spectralProjectorDerivative_right R dR p dp q a b da hab hRq hpq hdiff]
  rw [mul_smul_comm, mul_assoc p dR q, ← mul_assoc p p (dR * q), hp]

/-- **Complete four-block spectral derivative formula.** Once `p,q,r,s`
resolve the identity, the target projector derivative is completely
reconstructed from `dR` and the three spectral gaps.  The scalar `da` occurs
in the differentiated eigen-equations but cancels from the result.
@isnad1 id=eq.20h13v.s10.15f0199efdce from=translated src=- shape=99da9a27 vocab=3d5934f5
-/
theorem spectralProjectorDerivative_fourBlock
    (R dR p dp q r s : A) (a b c d da : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hp : p * p = p) (hsum : p + q + r + s = 1)
    (hqp : q * p = 0) (hrp : r * p = 0) (hsp : s * p = 0)
    (hpq : p * q = 0) (hpr : p * r = 0) (hps : p * s = 0)
    (hqR : q * R = b • q) (hrR : r * R = c • r)
    (hsR : s * R = d • s)
    (hRq : R * q = b • q) (hRr : R * r = c • r)
    (hRs : R * s = d • s)
    (hid : dp * p + p * dp = dp)
    (hleft : dR * p + R * dp = da • p + a • dp)
    (hright : dp * R + p * dR = da • p + a • dp) :
    dp =
      (a - b)⁻¹ • (q * dR * p) +
      (a - c)⁻¹ • (r * dR * p) +
      (a - d)⁻¹ • (s * dR * p) +
      (a - b)⁻¹ • (p * dR * q) +
      (a - c)⁻¹ • (p * dR * r) +
      (a - d)⁻¹ • (p * dR * s) := by
  rw [projectorDerivative_eq_three_complement_blocks p dp q r s hp hsum hid]
  rw [spectralProjectorDerivative_left_block R dR p dp q a b da hab
    hp hqR hqp hleft]
  rw [spectralProjectorDerivative_left_block R dR p dp r a c da hac
    hp hrR hrp hleft]
  rw [spectralProjectorDerivative_left_block R dR p dp s a d da had
    hp hsR hsp hleft]
  rw [spectralProjectorDerivative_right_block R dR p dp q a b da hab
    hp hRq hpq hright]
  rw [spectralProjectorDerivative_right_block R dR p dp r a c da hac
    hp hRr hpr hright]
  rw [spectralProjectorDerivative_right_block R dR p dp s a d da had
    hp hRs hps hright]

end RainichKaluza
