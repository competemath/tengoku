import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Support
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Möbius group and its action on the circle

This file constructs `SU(1,1)` in the coordinates used in [T26], its fractional-linear action on
the circle, the rotation and boost one-parameter subgroups, and the quotient
`Möb = PSU(1,1)`.
-/

namespace MobiusCPT

open scoped ComplexConjugate

noncomputable section

/-- [T26], §3: `SU(1,1)` as the pair `(α, β)` of the matrix
`(α β; conj β, conj α)`.-/
structure SU11 where
  /-- [T26], §3: the upper-left matrix entry.-/
  α : ℂ
  /-- [T26], §3: the upper-right matrix entry.-/
  β : ℂ
  /-- [T26], §3: the determinant-one relation `|α|² - |β|² = 1`.-/
  normSq_sub_normSq : Complex.normSq α - Complex.normSq β = 1

namespace SU11

/-- [T26], §3: two elements of `SU(1,1)` agree when their two matrix coordinates agree.
@isnad1 id=eq.2h2v.s4.f3306816f0e5 from=translated src=- shape=04c0b690 vocab=0ba0d72b
-/
@[ext]
theorem ext {g h : SU11} (hα : g.α = h.α) (hβ : g.β = h.β) : g = h := by
  cases g
  cases h
  simp_all

/-- [T26], §3: the identity element of `SU(1,1)`.-/
instance instOne : One SU11 where
  one := ⟨1, 0, by simp⟩

/-- [T26], §3: multiplication in `SU(1,1)`, written in the coordinates `(α, β)`.-/
instance instMul : Mul SU11 where
  mul g h :=
    ⟨g.α * h.α + g.β * conj h.β,
      g.α * h.β + g.β * conj h.α,
      by
        calc
          Complex.normSq (g.α * h.α + g.β * conj h.β) -
                Complex.normSq (g.α * h.β + g.β * conj h.α) =
              (Complex.normSq g.α - Complex.normSq g.β) *
                (Complex.normSq h.α - Complex.normSq h.β) := by
            simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
              Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
            ring
          _ = 1 := by rw [g.normSq_sub_normSq, h.normSq_sub_normSq, one_mul]⟩

/-- [T26], §3: inversion in `SU(1,1)`, written in the coordinates `(α, β)`.-/
instance instInv : Inv SU11 where
  inv g :=
    ⟨conj g.α, -g.β, by
      simpa only [Complex.normSq_conj, Complex.normSq_neg] using g.normSq_sub_normSq⟩

/-- [T26], §3: simultaneous sign change of the two coordinates of an `SU(1,1)` element.-/
def neg (g : SU11) : SU11 :=
  ⟨-g.α, -g.β, by
    simpa only [Complex.normSq_neg] using g.normSq_sub_normSq⟩

/-- The `α` coordinate of the identity element is one.
@isnad1 id=eq.0h0v.s3.47e2da68a58a from=translated src=- shape=1ac31801 vocab=005b5788
-/
@[simp]
theorem one_alpha : (1 : SU11).α = 1 := rfl

/-- The `β` coordinate of the identity element is zero.
@isnad1 id=eq.0h0v.s3.1a344496ee01 from=translated src=- shape=1ac31801 vocab=31e6f15a
-/
@[simp]
theorem one_beta : (1 : SU11).β = 0 := rfl

/-- The `α` coordinate of a product in `SU(1,1)`.
@isnad1 id=eq.0h2v.s6.54fef0f79962 from=translated src=- shape=ca3592a9 vocab=1ffdc830
-/
@[simp]
theorem mul_alpha (g h : SU11) : (g * h).α = g.α * h.α + g.β * conj h.β := rfl

/-- The `β` coordinate of a product in `SU(1,1)`.
@isnad1 id=eq.0h2v.s6.d50556666778 from=translated src=- shape=fa3530c8 vocab=1ffdc830
-/
@[simp]
theorem mul_beta (g h : SU11) : (g * h).β = g.α * h.β + g.β * conj h.α := rfl

/-- The `α` coordinate of an inverse in `SU(1,1)`.
@isnad1 id=eq.0h1v.s5.1b3afcfb6cd0 from=translated src=- shape=40757b00 vocab=8f08247a
-/
@[simp]
theorem inv_alpha (g : SU11) : (g⁻¹).α = conj g.α := rfl

/-- The `β` coordinate of an inverse in `SU(1,1)`.
@isnad1 id=eq.0h1v.s3.48b471fd5d84 from=translated src=- shape=5a02da31 vocab=36c2f5fd
-/
@[simp]
theorem inv_beta (g : SU11) : (g⁻¹).β = -g.β := rfl

/-- The `α` coordinate after simultaneous sign change.
@isnad1 id=eq.0h1v.s3.916e4d8353fb from=translated src=- shape=d2189a58 vocab=ba8deed5
-/
@[simp]
theorem neg_alpha (g : SU11) : (neg g).α = -g.α := rfl

/-- The `β` coordinate after simultaneous sign change.
@isnad1 id=eq.0h1v.s3.133880b14d77 from=translated src=- shape=d2189a58 vocab=ac350457
-/
@[simp]
theorem neg_beta (g : SU11) : (neg g).β = -g.β := rfl

/-- [T26], §3: simultaneous sign change is an involution.
@isnad1 id=eq.0h1v.s3.f850ab99e8de from=translated src=- shape=47dcad53 vocab=ccb98178
-/
@[simp]
theorem neg_neg (g : SU11) : neg (neg g) = g := by
  ext <;> simp [neg]

/-- [T26], §3: simultaneous sign change commutes with multiplication on the left.
@isnad1 id=eq.0h2v.s4.8e631abbaf91 from=translated src=- shape=8639c4b5 vocab=4bede6d2
-/
@[simp]
theorem neg_mul (g h : SU11) : neg g * h = neg (g * h) := by
  apply SU11.ext
  · change (-g.α) * h.α + (-g.β) * conj h.β =
      -(g.α * h.α + g.β * conj h.β)
    ring
  · change (-g.α) * h.β + (-g.β) * conj h.α =
      -(g.α * h.β + g.β * conj h.α)
    ring

/-- [T26], §3: simultaneous sign change commutes with multiplication on the right.
@isnad1 id=eq.0h2v.s4.0290c9b1ba8a from=translated src=- shape=91b7ceb5 vocab=4bede6d2
-/
@[simp]
theorem mul_neg (g h : SU11) : g * neg h = neg (g * h) := by
  apply SU11.ext
  · change g.α * (-h.α) + g.β * conj (-h.β) =
      -(g.α * h.α + g.β * conj h.β)
    simp only [map_neg]
    ring
  · change g.α * (-h.β) + g.β * conj (-h.α) =
      -(g.α * h.β + g.β * conj h.α)
    simp only [map_neg]
    ring

/-- [T26], §3: multiplication and inversion make `SU(1,1)` a group.-/
instance instGroup : Group SU11 where
  mul_assoc g h k := by
    apply SU11.ext
    · change
        (g.α * h.α + g.β * conj h.β) * k.α +
            (g.α * h.β + g.β * conj h.α) * conj k.β =
          g.α * (h.α * k.α + h.β * conj k.β) +
            g.β * conj (h.α * k.β + h.β * conj k.α)
      simp only [map_add, map_mul, Complex.conj_conj]
      ring
    · change
        (g.α * h.α + g.β * conj h.β) * k.β +
            (g.α * h.β + g.β * conj h.α) * conj k.α =
          g.α * (h.α * k.β + h.β * conj k.α) +
            g.β * conj (h.α * k.α + h.β * conj k.β)
      simp only [map_add, map_mul, Complex.conj_conj]
      ring
  one_mul g := by
    apply SU11.ext
    · change (1 : ℂ) * g.α + 0 * conj g.β = g.α
      simp
    · change (1 : ℂ) * g.β + 0 * conj g.α = g.β
      simp
  mul_one g := by
    apply SU11.ext
    · change g.α * (1 : ℂ) + g.β * conj 0 = g.α
      simp
    · change g.α * 0 + g.β * conj (1 : ℂ) = g.β
      simp
  inv_mul_cancel g := by
    apply SU11.ext
    · change conj g.α * g.α + (-g.β) * conj g.β = 1
      have hg :
          ((Complex.normSq g.α - Complex.normSq g.β : ℝ) : ℂ) = 1 := by
        simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) g.normSq_sub_normSq
      calc
        conj g.α * g.α + (-g.β) * conj g.β =
            conj g.α * g.α - g.β * conj g.β := by ring
        _ = (Complex.normSq g.α : ℂ) - Complex.normSq g.β := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.mul_conj]
        _ = ((Complex.normSq g.α - Complex.normSq g.β : ℝ) : ℂ) := by
          exact (Complex.ofReal_sub _ _).symm
        _ = 1 := hg
    · simp only [mul_beta, inv_alpha, inv_beta, one_beta, Complex.conj_conj]
      ring

/-- [T26], §3: the negative identity acts by simultaneous sign change on the left.
@isnad1 id=eq.0h1v.s4.68da860da652 from=translated src=- shape=4bd51e04 vocab=4bede6d2
-/
@[simp]
theorem neg_one_mul (g : SU11) : neg 1 * g = neg g := by
  rw [neg_mul, one_mul]

/-- [T26], §3: the negative identity acts by simultaneous sign change on the right.
@isnad1 id=eq.0h1v.s4.f78d641c5bbc from=translated src=- shape=dd9de19d vocab=4bede6d2
-/
@[simp]
theorem mul_neg_one (g : SU11) : g * neg 1 = neg g := by
  rw [mul_neg, mul_one]

end SU11

/-- [T26], §2.2: the automorphy factor `j(γ, z) = conj(β) z + conj(α)`, the
denominator of `γ · z`.-/
def j (g : SU11) (z : Circle) : ℂ := conj g.β * (z : ℂ) + conj g.α

/-- [T26], §2.2: the automorphy factor does not vanish on the circle.
@isnad1 id=ne.0h2v.s3.5fa574a0abe3 from=translated src=- shape=90ed236d vocab=ed148e52
-/
theorem j_ne_zero (g : SU11) (z : Circle) : j g z ≠ 0 := by
  intro hj
  have hα : conj g.α = -(conj g.β * (z : ℂ)) := by
    calc
      conj g.α = j g z - conj g.β * (z : ℂ) := by simp [j]
      _ = -(conj g.β * (z : ℂ)) := by rw [hj]; ring
  have hnorm := congrArg Complex.normSq hα
  have heq : Complex.normSq g.α = Complex.normSq g.β := by
    simpa only [Complex.normSq_conj, Complex.normSq_neg, Complex.normSq_mul,
      Circle.normSq_coe, mul_one] using hnorm
  linarith [g.normSq_sub_normSq]

/-- [T26], §2.2: on the circle the numerator is `z` times the conjugate automorphy factor.
@isnad1 id=eq.0h2v.s7.b1e2dce0da5d from=translated src=- shape=0d595b8b vocab=f6c46348
-/
theorem num_eq (g : SU11) (z : Circle) :
    g.α * (z : ℂ) + g.β = (z : ℂ) * conj (j g z) := by
  have hz : (z : ℂ) * conj (z : ℂ) = 1 := by
    simpa using Complex.mul_conj (z : ℂ)
  rw [show conj (j g z) = g.β * conj (z : ℂ) + g.α by
    simp [j, map_add, map_mul, Complex.conj_conj]]
  calc
    g.α * (z : ℂ) + g.β =
        g.β * ((z : ℂ) * conj (z : ℂ)) + (z : ℂ) * g.α := by
      rw [hz]
      ring
    _ = (z : ℂ) * (g.β * conj (z : ℂ)) + (z : ℂ) * g.α := by ring
    _ = (z : ℂ) * (g.β * conj (z : ℂ) + g.α) := by ring

/-- [T26], §2.2: on the circle the numerator and automorphy factor have equal norm.
@isnad1 id=eq.0h2v.s6.fd37509b5905 from=translated src=- shape=c6512aa7 vocab=2f9ccaf3
-/
theorem norm_num_eq_norm_j (g : SU11) (z : Circle) :
    ‖g.α * (z : ℂ) + g.β‖ = ‖j g z‖ := by
  rw [num_eq, norm_mul, Circle.norm_coe, one_mul]
  exact Complex.norm_conj _

/-- [T26], §1: the fractional-linear scalar action of `SU(1,1)` on `S¹`.-/
instance instSMulSU11Circle : SMul SU11 Circle where
  smul g z :=
    ⟨(g.α * (z : ℂ) + g.β) / j g z, by
      change (g.α * (z : ℂ) + g.β) / j g z ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, norm_div, norm_num_eq_norm_j]
      exact div_self (norm_ne_zero_iff.mpr (j_ne_zero g z))⟩

/-- [T26], §1: coercion of the fractional-linear action to a complex number.
@isnad1 id=eq.0h2v.s7.06534c210d74 from=translated src=- shape=e6a73bb6 vocab=fb479841
-/
@[simp]
theorem coe_smul (g : SU11) (z : Circle) :
    ((g • z : Circle) : ℂ) = (g.α * (z : ℂ) + g.β) / j g z := rfl

/-- [T26], §2.2: the identity automorphy factor is one.
@isnad1 id=eq.0h1v.s4.9bc734308ade from=translated src=- shape=fcc0db09 vocab=ed148e52
-/
@[simp]
theorem j_one (z : Circle) : j 1 z = 1 := by
  change conj (0 : ℂ) * (z : ℂ) + conj (1 : ℂ) = 1
  simp

/-- [T26], §2.2: the automorphy factor satisfies its multiplicative cocycle identity.
@isnad1 id=eq.0h3v.s5.a5e4b2f9439b from=translated src=- shape=cd871d23 vocab=ff54ee0d
-/
theorem j_mul (g h : SU11) (z : Circle) : j (g * h) z = j g (h • z) * j h z := by
  have hj : conj h.β * (z : ℂ) + conj h.α ≠ 0 := by
    simpa only [j] using (j_ne_zero h z)
  simp only [j, SU11.mul_alpha, SU11.mul_beta, map_add, map_mul, Complex.conj_conj, coe_smul]
  field_simp [hj]
  ring

/-- [T26], §1: the fractional-linear formula is a group action of `SU(1,1)` on `S¹`.-/
instance instMulActionSU11Circle : MulAction SU11 Circle where
  one_smul z := by
    apply Circle.ext
    rw [coe_smul]
    simp [j]
  mul_smul g h z := by
    apply Circle.ext
    rw [coe_smul, coe_smul, coe_smul, j_mul]
    change
      ((g.α * h.α + g.β * conj h.β) * (z : ℂ) +
          (g.α * h.β + g.β * conj h.α)) /
          (j g (h • z) * j h z) =
        (g.α * ((h.α * (z : ℂ) + h.β) / j h z) + g.β) /
          j g (h • z)
    field_simp [j_ne_zero]
    simp only [j]
    ring

/-- [T26], §1: simultaneous sign change leaves the circle action unchanged.
@isnad1 id=eq.0h2v.s4.e82a33a3d58f from=translated src=- shape=bff88b4c vocab=20fefaf6
-/
@[simp]
theorem smul_neg_eq (g : SU11) (z : Circle) : SU11.neg g • z = g • z := by
  apply Circle.ext
  rw [coe_smul, coe_smul]
  change ((-g.α) * (z : ℂ) + (-g.β)) / j (SU11.neg g) z =
    (g.α * (z : ℂ) + g.β) / j g z
  have hnum : (-g.α) * (z : ℂ) + (-g.β) =
      -(g.α * (z : ℂ) + g.β) := by ring
  have hden : j (SU11.neg g) z = -j g z := by
    simp [j, SU11.neg]
    ring
  rw [hnum, hden, neg_div_neg_eq]

/-- [T26], §2.2: simultaneous sign change negates the automorphy factor.
@isnad1 id=eq.0h2v.s4.8fc30aec43c5 from=translated src=- shape=6f752268 vocab=6ff4b0bf
-/
@[simp]
theorem j_neg (g : SU11) (z : Circle) : j (SU11.neg g) z = -j g z := by
  simp [j, SU11.neg]
  ring

/-- [T26], §2.2: the rotation `r_θ = diag(e^{iθ/2}, e^{-iθ/2})`.-/
def rotMat (θ : ℝ) : SU11 :=
  ⟨Complex.exp (Complex.I * (θ / 2 : ℝ)), 0, by
    have hnorm : ‖Complex.exp (Complex.I * (θ / 2 : ℝ))‖ = 1 := by
      simpa only [Circle.coe_exp, mul_comm] using Circle.norm_coe (Circle.exp (θ / 2))
    calc
      Complex.normSq (Complex.exp (Complex.I * (θ / 2 : ℝ))) - Complex.normSq 0 =
          ‖Complex.exp (Complex.I * (θ / 2 : ℝ))‖ ^ 2 - Complex.normSq 0 := by
            rw [Complex.normSq_eq_norm_sq]
      _ = 1 := by rw [hnorm]; simp⟩

/-- [T26], §2.2: the rotation matrix at angle zero is the identity.
@isnad1 id=eq.0h0v.s3.9c3d939920c0 from=translated src=- shape=1ac31801 vocab=f58ac985
-/
@[simp]
theorem rotMat_zero : rotMat 0 = 1 := by
  apply SU11.ext
  · change Complex.exp (Complex.I * ((0 : ℝ) / 2 : ℝ)) = (1 : ℂ)
    simp
  · change (0 : ℂ) = 0
    rfl

/-- [T26], §2.2: rotation matrices form a one-parameter subgroup of `SU(1,1)`.
@isnad1 id=eq.0h2v.s4.e0b0c8180258 from=translated src=- shape=0438c7a3 vocab=0e44bbdb
-/
theorem rotMat_add (θ ψ : ℝ) : rotMat (θ + ψ) = rotMat θ * rotMat ψ := by
  apply SU11.ext
  · change Complex.exp (Complex.I * ((θ + ψ) / 2 : ℝ)) =
      Complex.exp (Complex.I * (θ / 2 : ℝ)) *
          Complex.exp (Complex.I * (ψ / 2 : ℝ)) + 0 * conj (0 : ℂ)
    simp only [zero_mul, add_zero]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · change (0 : ℂ) =
      Complex.exp (Complex.I * (θ / 2 : ℝ)) * 0 +
        0 * conj (Complex.exp (Complex.I * (ψ / 2 : ℝ)))
    simp

/-- [T26], §1: a full `2π` rotation is the negative identity in `SU(1,1)`.
@isnad1 id=eq.0h0v.s4.dd11fbb28da2 from=translated src=- shape=630abf2c vocab=d33f655a
-/
theorem rotMat_two_pi : rotMat (2 * Real.pi) = SU11.neg 1 := by
  apply SU11.ext
  · change Complex.exp (Complex.I * ((2 * Real.pi) / 2 : ℝ)) = -1
    rw [show (2 * Real.pi) / 2 = Real.pi by ring]
    rw [mul_comm, Complex.exp_pi_mul_I]
  · change (0 : ℂ) = -(0 : ℂ)
    simp

/-- [T26], §2.2: the fractional-linear rotation is multiplication by `e^{iθ}`.
@isnad1 id=eq.0h2v.s5.521808664c72 from=translated src=- shape=d9aad215 vocab=075de6d3
-/
theorem rotMat_smul (θ : ℝ) (z : Circle) : rotMat θ • z = Circle.exp θ * z := by
  apply Circle.ext
  rw [coe_smul, Circle.coe_mul, Circle.coe_exp]
  have hconj :
      conj (Complex.exp (Complex.I * (θ / 2 : ℝ))) =
        Complex.exp (-(Complex.I * (θ / 2 : ℝ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofNat]
  simp only [rotMat, j, map_zero, zero_mul, mul_zero, zero_add, add_zero, hconj]
  calc
    Complex.exp (Complex.I * (θ / 2 : ℝ)) * (z : ℂ) /
          Complex.exp (-(Complex.I * (θ / 2 : ℝ))) =
        (Complex.exp (Complex.I * (θ / 2 : ℝ)) /
          Complex.exp (-(Complex.I * (θ / 2 : ℝ)))) * (z : ℂ) := by ring
    _ = Complex.exp
          (Complex.I * (θ / 2 : ℝ) - (-(Complex.I * (θ / 2 : ℝ)))) * (z : ℂ) := by
      rw [Complex.exp_sub]
    _ = Complex.exp ((θ : ℂ) * Complex.I) * (z : ℂ) := by
      congr 2
      push_cast
      ring

/-- [T26], §3: the boost
`v_t = (cosh(t/2), -sinh(t/2); -sinh(t/2), cosh(t/2))`.-/
def boostMat (t : ℝ) : SU11 :=
  ⟨(Real.cosh (t / 2) : ℂ), (-(Real.sinh (t / 2)) : ℂ), by
    simpa only [Complex.normSq_ofReal, Complex.normSq_neg, pow_two] using
      Real.cosh_sq_sub_sinh_sq (t / 2)⟩

/-- [T26], §3: the first coordinate of the boost matrix.
@isnad1 id=eq.0h1v.s4.2e229bb700a3 from=translated src=- shape=039a0139 vocab=cf4f46e9
-/
theorem boostMat_alpha (t : ℝ) : (boostMat t).α = ((Real.cosh (t / 2) : ℝ) : ℂ) := rfl

/-- [T26], §3: the second coordinate of the boost matrix.
@isnad1 id=eq.0h1v.s4.828c96cd6c26 from=translated src=- shape=4464abe3 vocab=7e12919f
-/
theorem boostMat_beta (t : ℝ) : (boostMat t).β = -((Real.sinh (t / 2) : ℝ) : ℂ) := rfl

/-- [T26], §3: the boost matrix at parameter zero is the identity.
@isnad1 id=eq.0h0v.s3.862809a597b3 from=translated src=- shape=1ac31801 vocab=32d3bc98
-/
@[simp]
theorem boostMat_zero : boostMat 0 = 1 := by
  apply SU11.ext
  · change (Real.cosh ((0 : ℝ) / 2) : ℂ) = (1 : ℂ)
    simp
  · change (-(Real.sinh ((0 : ℝ) / 2)) : ℂ) = 0
    simp

/-- [T26], §3: boost matrices form a one-parameter subgroup of `SU(1,1)`.
@isnad1 id=eq.0h2v.s4.1d2dfb9e3274 from=translated src=- shape=0438c7a3 vocab=334c1880
-/
theorem boostMat_add (s t : ℝ) : boostMat (s + t) = boostMat s * boostMat t := by
  have hhalf : (s + t) / 2 = s / 2 + t / 2 := by ring
  apply SU11.ext
  · change (Real.cosh ((s + t) / 2) : ℂ) =
      (Real.cosh (s / 2) : ℂ) * (Real.cosh (t / 2) : ℂ) +
        (-(Real.sinh (s / 2)) : ℂ) *
          conj (-(Real.sinh (t / 2)) : ℂ)
    rw [hhalf, Real.cosh_add]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, map_neg,
      Complex.conj_ofReal]
    ring
  · change (-(Real.sinh ((s + t) / 2)) : ℂ) =
      (Real.cosh (s / 2) : ℂ) * (-(Real.sinh (t / 2)) : ℂ) +
        (-(Real.sinh (s / 2)) : ℂ) *
          conj (Real.cosh (t / 2) : ℂ)
    rw [hhalf, Real.sinh_add]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, map_neg,
      Complex.conj_ofReal]
    ring

/-- [T26], §2.2: the automorphy factor of a boost.
@isnad1 id=eq.0h2v.s7.8403940da185 from=translated src=- shape=317614b2 vocab=475df966
-/
@[simp]
theorem j_boostMat (t : ℝ) (z : Circle) :
    j (boostMat t) z =
      -(Real.sinh (t / 2) : ℂ) * (z : ℂ) + (Real.cosh (t / 2) : ℂ) := by
  have hconj_sinh :
      conj (Complex.sinh ((t : ℂ) / 2)) = Complex.sinh ((t : ℂ) / 2) := by
    rw [← Complex.sinh_conj]
    congr 1
    simp [Complex.conj_ofNat]
  have hconj_cosh :
      conj (Complex.cosh ((t : ℂ) / 2)) = Complex.cosh ((t : ℂ) / 2) := by
    rw [← Complex.cosh_conj]
    congr 1
    simp [Complex.conj_ofNat]
  simp [j, boostMat, Complex.conj_ofReal, hconj_sinh, hconj_cosh]

/-- [T26], §2.2: the source denominator `sinh(t/2) z + cosh(t/2)` is the automorphy factor
of `v_{-t}`.
@isnad1 id=eq.0h2v.s7.23bee4796fa5 from=translated src=- shape=f73b9afc vocab=475df966
-/
theorem j_boostMat_neg (t : ℝ) (z : Circle) :
    j (boostMat (-t)) z =
      (Real.sinh (t / 2) : ℂ) * (z : ℂ) + (Real.cosh (t / 2) : ℂ) := by
  rw [j_boostMat]
  simp only [neg_div, Real.sinh_neg, Real.cosh_neg, Complex.ofReal_neg, neg_neg]

/-- [T26], §3: a boost rescales the imaginary part by the positive squared norm of its
automorphy factor.
@isnad1 id=eq.0h2v.s7.38a7b8d58e9f from=translated src=- shape=84e257d3 vocab=08687137
-/
theorem im_boostMat_smul (t : ℝ) (z : Circle) :
    ((boostMat t • z : Circle) : ℂ).im =
      (z : ℂ).im / Complex.normSq (j (boostMat t) z) := by
  rw [coe_smul, Complex.div_im]
  rw [j_boostMat]
  simp only [boostMat, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im, zero_mul, mul_zero, add_zero, sub_zero, neg_zero,
    ← sub_eq_add_neg]
  rw [← sub_div]
  congr 1
  have hdet : Real.cosh (t / 2) * Real.cosh (t / 2) -
      Real.sinh (t / 2) * Real.sinh (t / 2) = 1 := by
    simpa only [pow_two] using Real.cosh_sq_sub_sinh_sq (t / 2)
  calc
    Real.cosh (t / 2) * (z : ℂ).im *
          (-(Real.sinh (t / 2)) * (z : ℂ).re + Real.cosh (t / 2)) -
        (Real.cosh (t / 2) * (z : ℂ).re - Real.sinh (t / 2)) *
          (-(Real.sinh (t / 2)) * (z : ℂ).im) =
        (Real.cosh (t / 2) * Real.cosh (t / 2) -
          Real.sinh (t / 2) * Real.sinh (t / 2)) * (z : ℂ).im := by ring
    _ = (z : ℂ).im := by rw [hdet, one_mul]

/-- [T26], §3: boosts preserve the open upper semicircle.
@isnad1 id=mem.1h2v.s4.8e31de261fb3 from=translated src=- shape=5d1bf102 vocab=76fdf177
-/
theorem boostMat_smul_mem_upperArc (t : ℝ) {z : Circle} (hz : z ∈ upperArc) :
    boostMat t • z ∈ upperArc := by
  change 0 < ((boostMat t • z : Circle) : ℂ).im
  rw [im_boostMat_smul]
  exact div_pos hz (Complex.normSq_pos.mpr (j_ne_zero (boostMat t) z))

/-- [T26], §3: boosts preserve the open lower semicircle.
@isnad1 id=mem.1h2v.s4.456bb4f05535 from=translated src=- shape=5d1bf102 vocab=4ce08fd7
-/
theorem boostMat_smul_mem_lowerArc (t : ℝ) {z : Circle} (hz : z ∈ lowerArc) :
    boostMat t • z ∈ lowerArc := by
  change ((boostMat t • z : Circle) : ℂ).im < 0
  rw [im_boostMat_smul]
  exact div_neg_of_neg_of_pos hz (Complex.normSq_pos.mpr (j_ne_zero (boostMat t) z))

/-- [T26], §1: the subgroup `{±1} ⊆ SU(1,1)` that is quotiented out to form
`Möb = PSU(1,1)`. Its two elements act trivially on `S¹` (`smul_neg_eq`), which is what makes
the action descend to the quotient; that it is the *whole* kernel of the action is not claimed
here and is not needed, since [T26] §1 defines `Möb` as `SU(1,1)/{±1}`.-/
def signSubgroup : Subgroup SU11 where
  carrier := {1, SU11.neg 1}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh ⊢
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;> simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl
    · simp
    · right
      apply SU11.ext
      · change conj (-(1 : ℂ)) = -(1 : ℂ)
        simp
      · change -(-(0 : ℂ)) = -(0 : ℂ)
        simp

/-- [T26], §1: the sign subgroup is normal because the negative identity is central.
@isnad1 id=normal.0h0v.s2.a96dbd26f39b from=translated src=- shape=25b03439 vocab=3f865c56
-/
instance signSubgroupNormal : signSubgroup.Normal where
  conj_mem n hn g := by
    simp only [signSubgroup, Set.mem_insert_iff, Set.mem_singleton_iff] at hn ⊢
    rcases hn with rfl | rfl
    · left
      simp
    · right
      simp

/-- [T26], §1: the Möbius group `Möb = PSU(1,1) = SU(1,1)/{\pm 1}`.-/
def Mob : Type := SU11 ⧸ signSubgroup

/-- [T26], §1: the quotient `PSU(1,1)` inherits its group structure.-/
instance instGroupMob : Group Mob := inferInstanceAs (Group (SU11 ⧸ signSubgroup))

namespace Mob

/-- [T26], §1: the quotient map from `SU(1,1)` to `PSU(1,1)`.-/
def mk (g : SU11) : Mob := QuotientGroup.mk g

/-- [T26], §1: the quotient map preserves multiplication.
@isnad1 id=eq.0h2v.s5.a7656b1cde56 from=translated src=- shape=0438c7a3 vocab=84e90d99
-/
@[simp]
theorem mk_mul (g h : SU11) : mk (g * h) = mk g * mk h := by
  change QuotientGroup.mk' signSubgroup (g * h) =
    QuotientGroup.mk' signSubgroup g * QuotientGroup.mk' signSubgroup h
  exact (QuotientGroup.mk' signSubgroup).map_mul g h

/-- [T26], §1: the quotient map preserves the identity.
@isnad1 id=eq.0h0v.s4.e246e1fcd9e3 from=translated src=- shape=1ac31801 vocab=2b89b18c
-/
@[simp]
theorem mk_one : mk 1 = 1 := by
  change QuotientGroup.mk' signSubgroup 1 = 1
  exact (QuotientGroup.mk' signSubgroup).map_one

/-- [T26], §1: quotient classes are exactly equal up to simultaneous sign change.
@isnad1 id=iff.0h2v.s4.a7c16ee7553c from=translated src=- shape=ce511acb vocab=3c58af30
-/
theorem mk_eq_mk {g h : SU11} : mk g = mk h ↔ (h = g ∨ h = SU11.neg g) := by
  change QuotientGroup.mk' signSubgroup g = QuotientGroup.mk' signSubgroup h ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨s, hs, hgs⟩
    simp only [signSubgroup, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Or.inl (by simpa using hgs.symm)
    · exact Or.inr (by simpa using hgs.symm)
  · rintro (rfl | rfl)
    · exact ⟨1, by simp [signSubgroup], by simp⟩
    · exact ⟨SU11.neg 1, by simp [signSubgroup], by simp⟩

/-- [T26], §1: simultaneous sign change represents the same element of `PSU(1,1)`.
@isnad1 id=eq.0h1v.s3.dc54e0fd5209 from=translated src=- shape=8d4cac31 vocab=3c58af30
-/
@[simp]
theorem mk_neg (g : SU11) : mk (SU11.neg g) = mk g :=
  mk_eq_mk.mpr (Or.inr (SU11.neg_neg g).symm)

/-- [T26], §1: every element of `PSU(1,1)` has an `SU(1,1)` representative.
@isnad1 id=surjecti.0h0v.s2.5c48be2e413d from=translated src=- shape=54c8eceb vocab=6bfa485d
-/
theorem mk_surjective : Function.Surjective mk := by
  intro γ
  change ∃ g : SU11, QuotientGroup.mk g = γ
  exact QuotientGroup.mk_surjective γ

/-- [T26], §1: the fractional-linear action descends from `SU(1,1)` to `PSU(1,1)`.-/
instance instSMulCircle : SMul Mob Circle where
  smul γ z :=
    Quotient.liftOn' (show SU11 ⧸ signSubgroup from γ) (fun g : SU11 ↦ g • z) (by
      intro g h hrel
      have hmk : mk g = mk h := by
        change QuotientGroup.mk g = QuotientGroup.mk h
        exact Quotient.sound' hrel
      rcases mk_eq_mk.mp hmk with rfl | rfl
      · rfl
      · exact (smul_neg_eq g z).symm)

/-- [T26], §1: a quotient representative acts by its fractional-linear action.
@isnad1 id=eq.0h2v.s4.a88af960156a from=translated src=- shape=6ee36c65 vocab=5bcdca33
-/
@[simp]
theorem mk_smul (g : SU11) (z : Circle) : mk g • z = g • z := rfl

/-- [T26], §1: the descended fractional-linear formula is a group action of `PSU(1,1)`.-/
instance instMulActionCircle : MulAction Mob Circle where
  one_smul z := by
    rw [← mk_one]
    rw [mk_smul]
    exact one_smul SU11 z
  mul_smul γ δ z := by
    obtain ⟨g, rfl⟩ := mk_surjective γ
    obtain ⟨h, rfl⟩ := mk_surjective δ
    simpa only [← mk_mul, mk_smul] using (mul_smul g h z)

/-- [T26], §2.2: the rotation subgroup in `PSU(1,1)`.-/
def rot (θ : ℝ) : Mob := mk (rotMat θ)

/-- [T26], §3: the boost subgroup in `PSU(1,1)`.-/
def boost (t : ℝ) : Mob := mk (boostMat t)

/-- [T26], §2.2: the rotation subgroup at zero is the identity.
@isnad1 id=eq.0h0v.s4.a869c174eb03 from=translated src=- shape=1ac31801 vocab=1ab2a880
-/
@[simp]
theorem rot_zero : rot 0 = 1 := by simp [rot]

/-- [T26], §2.2: rotations form a one-parameter subgroup of `PSU(1,1)`.
@isnad1 id=eq.0h2v.s5.bc1dc47e436a from=translated src=- shape=0438c7a3 vocab=de27ed74
-/
theorem rot_add (θ ψ : ℝ) : rot (θ + ψ) = rot θ * rot ψ := by
  simp [rot, rotMat_add]

/-- [T26], §2.2: a rotation acts on the circle by multiplication by `e^{iθ}`.
@isnad1 id=eq.0h2v.s5.b33fc6327fe3 from=translated src=- shape=d9aad215 vocab=569ccf57
-/
theorem rot_smul (θ : ℝ) (z : Circle) : rot θ • z = Circle.exp θ * z := by
  rw [rot, mk_smul, rotMat_smul]

/-- [T26], §3: the boost subgroup at zero is the identity.
@isnad1 id=eq.0h0v.s4.9944a51c5abf from=translated src=- shape=1ac31801 vocab=fa8f5dd2
-/
@[simp]
theorem boost_zero : boost 0 = 1 := by simp [boost]

/-- [T26], §3: boosts form a one-parameter subgroup of `PSU(1,1)`.
@isnad1 id=eq.0h2v.s5.6f1e8b52aa8a from=translated src=- shape=0438c7a3 vocab=5afe32d1
-/
theorem boost_add (s t : ℝ) : boost (s + t) = boost s * boost t := by
  simp [boost, boostMat_add]

/-- [T26], §1: the rotation subgroup is `2π`-periodic in `Möb = PSU(1,1)`.
@isnad1 id=eq.0h0v.s5.6409f202bbb7 from=translated src=- shape=ad454fee vocab=7b49f259
-/
theorem rot_two_pi : rot (2 * Real.pi) = 1 := by
  rw [rot, rotMat_two_pi, mk_neg, mk_one]

/-- [T26], §1: the rotation subgroup is not trivial — `r_π` moves the point `1` to `-1`.
This rules out a degenerate model in which `Möb` collapses to the trivial group, so that
`rot_two_pi` has content.
@isnad1 id=ne.0h0v.s4.441c22c01610 from=translated src=- shape=b0ae1d2b vocab=7ee0c8ed
-/
theorem rot_pi_ne_one : rot Real.pi ≠ 1 := by
  intro h
  have h1 : rot Real.pi • (1 : Circle) = (1 : Circle) := by
    rw [h, one_smul]
  rw [rot_smul, mul_one] at h1
  have h2 : ((Circle.exp Real.pi : Circle) : ℂ) = ((1 : Circle) : ℂ) :=
    congrArg (fun w : Circle => (w : ℂ)) h1
  rw [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h2
  exact (by norm_num : (-1 : ℂ) ≠ 1) h2

/-- [T26], §1: the kernel of the rotation subgroup is contained in `2πℤ`. Since the kernel is a
subgroup of `ℝ` (by `rot_zero` and `rot_add`) and contains `2π` (by `rot_two_pi`), the two
together pin the period of `θ ↦ r_θ` at exactly `2π`.
@isnad1 id=ex.1h1v.s5.33dc1b33f870 from=translated src=- shape=93b31754 vocab=f8f9904e
-/
theorem exists_int_of_rot_eq_one {θ : ℝ} (h : rot θ = 1) :
    ∃ n : ℤ, θ = n * (2 * Real.pi) := by
  have h1 : rot θ • (1 : Circle) = (1 : Circle) := by
    rw [h, one_smul]
  rw [rot_smul, mul_one] at h1
  exact Circle.exp_eq_one.mp h1

/-- [T26], §3: the boost subgroup is faithful — `v_t` is the identity of `Möb` only at `t = 0`.
With `boost_add` this makes `t ↦ v_t` a genuine one-parameter flow rather than a collapsed
family, which is what the continued-boost argument of [T26] §3 relies on.
@isnad1 id=ne.1h1v.s4.e6d4459af91a from=translated src=- shape=20a1293d vocab=fa8f5dd2
-/
theorem boost_ne_one {t : ℝ} (ht : t ≠ 0) : boost t ≠ 1 := by
  intro h
  rw [boost, ← mk_one, mk_eq_mk] at h
  rcases h with h | h
  · have hβ : ((1 : SU11).β) = (boostMat t).β := congrArg SU11.β h
    rw [SU11.one_beta, boostMat_beta] at hβ
    have hs : ((Real.sinh (t / 2) : ℝ) : ℂ) = 0 := neg_eq_zero.mp hβ.symm
    have ht2 : Real.sinh (t / 2) = 0 := Complex.ofReal_eq_zero.mp hs
    exact ht (by have := Real.sinh_eq_zero.mp ht2; linarith)
  · have hα : ((1 : SU11).α) = (SU11.neg (boostMat t)).α := congrArg SU11.α h
    rw [SU11.one_alpha, SU11.neg_alpha, boostMat_alpha] at hα
    have hc : (1 : ℝ) = -Real.cosh (t / 2) := by
      have h1 := congrArg Complex.re hα
      simpa only [Complex.one_re, Complex.neg_re, Complex.ofReal_re] using h1
    have := Real.one_le_cosh (t / 2)
    linarith

end Mob

end

end MobiusCPT
