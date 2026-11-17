import Tengoku.Seed.Analysis.Calculus.ContDiff.Bounds
import Tengoku.Seed.Analysis.Calculus.ContDiff.Deriv
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.WithinZpow
import Tengoku.Seed.Analysis.Complex.Trigonometric
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Deriv
import Tengoku.MobiusCpt.MobiusCPT.Mobius.BoostAngle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derivative bounds for the boost angle

This file records exponential-in-`|t|` bounds for the angle derivatives of the elementary
boost factor `boostP` and its antiderivative `boostAngle`.
-/

namespace MobiusCPT

noncomputable section

open Set
open scoped ContDiff

/-! ### The elementary boost factor -/

/-- The iterated derivatives of cosine are its successive quarter-period translates.
@isnad1 id=eq.0h2v.s6.4c4cc60eada0 from=translated src=- shape=3c10f207 vocab=be723ab2
-/
theorem iteratedDeriv_cos_eq (m : ℕ) (θ : ℝ) :
    iteratedDeriv m Real.cos θ = Real.cos (θ + m * (Real.pi / 2)) := by
  induction m generalizing θ with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv m Real.cos =
          fun x : ℝ => Real.cos (x + m * (Real.pi / 2)) := by
        funext x
        exact ih x
      rw [hfun]
      have hderiv :
          deriv (fun x : ℝ => Real.cos (x + m * (Real.pi / 2))) θ =
            -Real.sin (θ + m * (Real.pi / 2)) := by
        simpa using
          ((Real.hasDerivAt_cos (θ + m * (Real.pi / 2))).comp θ
            ((hasDerivAt_id θ).add_const (m * (Real.pi / 2)))).deriv
      rw [hderiv, ← Real.cos_add_pi_div_two]
      congr 1
      push_cast
      ring

/-- Every iterated derivative of cosine has norm at most one.
@isnad1 id=le.0h2v.s5.1aecd434984d from=translated src=- shape=bfa24a32 vocab=1f24f10b
-/
theorem norm_iteratedDeriv_cos_le (m : ℕ) (θ : ℝ) :
    ‖iteratedDeriv m Real.cos θ‖ ≤ 1 := by
  rw [iteratedDeriv_cos_eq, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- `boostP` in ordinary trigonometric coordinates.
@isnad1 id=eq.0h2v.s4.9ffbb3ba13ee from=translated src=- shape=89470412 vocab=a2b514f5
-/
theorem boostP_eq (t θ : ℝ) :
    boostP t θ = Real.cosh t + Real.sinh t * Real.cos θ := by
  show Real.cosh t + (Circle.exp θ : ℂ).re * Real.sinh t = Real.cosh t + Real.sinh t * Real.cos θ
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  ring

/-- Derivatives of positive order of `boostP` are the corresponding cosine derivatives,
multiplied by `sinh t`.
@isnad1 id=eq.0h3v.s6.7c3a7455dec9 from=translated src=- shape=0bf17777 vocab=0cf5356d
-/
theorem iteratedDeriv_boostP_succ_eq (t : ℝ) (m : ℕ) (θ : ℝ) :
    iteratedDeriv (m + 1) (boostP t) θ =
      Real.sinh t * iteratedDeriv (m + 1) Real.cos θ := by
  rw [show boostP t = fun x : ℝ => Real.cosh t + Real.sinh t * Real.cos x by
    funext x
    exact boostP_eq t x]
  rw [iteratedDeriv_const_add (Nat.zero_lt_succ m) (Real.cosh t)]
  simpa using
    (iteratedDeriv_const_mul_field (n := m + 1) (x := θ) (Real.sinh t) Real.cos)

/-- The elementary hyperbolic coefficient grows at most exponentially in `|t|`.
@isnad1 id=le.0h1v.s4.9f8068e35aa9 from=translated src=- shape=d62e2955 vocab=1a2aa37f
-/
theorem abs_sinh_le_exp_abs (t : ℝ) : |Real.sinh t| ≤ Real.exp |t| := by
  rw [Real.abs_sinh]
  nlinarith [Real.sinh_add_cosh |t|, Real.cosh_pos |t|]

/-- Uniform-in-angle exponential growth of every positive-order derivative of `boostP`.
@isnad1 id=le.0h3v.s5.d2a6d5898153 from=translated src=- shape=7913e67f vocab=c5c865bb
-/
theorem norm_iteratedDeriv_boostP_le (t : ℝ) (m : ℕ) (θ : ℝ) :
    ‖iteratedDeriv (m + 1) (boostP t) θ‖ ≤ Real.exp |t| := by
  rw [iteratedDeriv_boostP_succ_eq, norm_mul, Real.norm_eq_abs]
  calc
    |Real.sinh t| * ‖iteratedDeriv (m + 1) Real.cos θ‖
        ≤ |Real.sinh t| * 1 :=
          mul_le_mul_of_nonneg_left (norm_iteratedDeriv_cos_le (m + 1) θ) (abs_nonneg _)
    _ = |Real.sinh t| := mul_one _
    _ ≤ Real.exp |t| := abs_sinh_le_exp_abs t

/-- The boost factor is smooth in the angle variable.
@isnad1 id=contdiff.0h1v.s5.e64aa3d1afc0 from=translated src=- shape=0fc4d29f vocab=5f2be532
-/
theorem contDiff_boostP (t : ℝ) : ContDiff ℝ ∞ (boostP t) := by
  rw [show boostP t = fun x : ℝ => Real.cosh t + Real.sinh t * Real.cos x by
    funext x
    exact boostP_eq t x]
  exact contDiff_const.add (contDiff_const.mul Real.contDiff_cos)

/-- The quantitative version of `boostP_pos` used to keep reciprocal derivatives away from
their singularity.
@isnad1 id=le.0h2v.s4.8b097d120506 from=translated src=- shape=03306bd5 vocab=b4c8839b
-/
theorem exp_neg_abs_le_boostP (t θ : ℝ) :
    Real.exp (-|t|) ≤ boostP t θ := by
  have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hbound : Real.cosh t - |Real.sinh t| ≤ boostP t θ := by
    rcases abs_le.mp hcos with ⟨hlo, hhi⟩
    rcases le_or_gt 0 (Real.sinh t) with hs | hs
    · rw [abs_of_nonneg hs, boostP_eq]
      nlinarith [mul_le_mul_of_nonneg_left hlo hs]
    · rw [abs_of_neg hs, boostP_eq]
      nlinarith [mul_le_mul_of_nonpos_left hhi hs.le]
  have heq : Real.cosh t - |Real.sinh t| = Real.exp (-|t|) := by
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht, abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht)]
      rw [Real.cosh_eq, Real.sinh_eq]
      ring_nf
    · rw [abs_of_neg ht, abs_of_neg (Real.sinh_neg_iff.mpr ht)]
      rw [Real.cosh_eq, Real.sinh_eq]
      ring_nf
  rwa [← heq]

/-! ### Reciprocal derivatives -/

/-- Closed form for the iterated derivatives of the reciprocal map.
@isnad1 id=eq.0h2v.s6.9733d1ea9988 from=translated src=- shape=686d23d4 vocab=54bcba0d
-/
theorem iteratedDeriv_inv_eq (m : ℕ) (y : ℝ) :
    iteratedDeriv m (Inv.inv : ℝ → ℝ) y =
      (-1) ^ m * (Nat.factorial m : ℝ) * y ^ (-1 - m : ℤ) := by
  rw [iteratedDeriv_eq_iterate]
  exact iter_deriv_inv m y

/-- On `[c, ∞)`, the `m`-th reciprocal derivative is bounded by `m! / c^(m+1)`.
@isnad1 id=le.2h3v.s6.bbf25ecf548a from=translated src=- shape=6e602c05 vocab=04171403
-/
theorem norm_iteratedDeriv_inv_le_of_ge (m : ℕ) {c y : ℝ}
    (hc : 0 < c) (hcy : c ≤ y) :
    ‖iteratedDeriv m (Inv.inv : ℝ → ℝ) y‖ ≤ (Nat.factorial m : ℝ) / c ^ (m + 1) := by
  have hy : 0 < y := hc.trans_le hcy
  have hpow (x : ℝ) (hx : x ≠ 0) :
      x ^ (-1 - m : ℤ) = (x ^ (m + 1))⁻¹ := by
    rw [show (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring]
    rw [zpow_neg, zpow_natCast]
  have hcast : (0 : ℝ) ≤ (Nat.factorial m : ℝ) := Nat.cast_nonneg (Nat.factorial m)
  have hnorm :
      ‖iteratedDeriv m (Inv.inv : ℝ → ℝ) y‖ = (Nat.factorial m : ℝ) / y ^ (m + 1) := by
    rw [iteratedDeriv_inv_eq, Real.norm_eq_abs, hpow y hy.ne']
    simp [abs_mul, abs_of_nonneg hcast, abs_of_pos hy, div_eq_mul_inv]
  rw [hnorm]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hc _)
    (pow_le_pow_left₀ hc.le hcy _)

/-- Specialization of the reciprocal bound to the lower bound for `boostP`.
@isnad1 id=le.1h3v.s6.278eb0c5ee36 from=translated src=- shape=bd64daa3 vocab=939b68b6
-/
theorem norm_iteratedDeriv_inv_le_exp (t : ℝ) (m : ℕ) {y : ℝ}
    (hy : Real.exp (-|t|) ≤ y) :
    ‖iteratedDeriv m (Inv.inv : ℝ → ℝ) y‖ ≤
      (Nat.factorial m : ℝ) * Real.exp ((m + 1 : ℕ) * |t|) := by
  calc
    ‖iteratedDeriv m (Inv.inv : ℝ → ℝ) y‖
        ≤ (Nat.factorial m : ℝ) / Real.exp (-|t|) ^ (m + 1) :=
          norm_iteratedDeriv_inv_le_of_ge m (Real.exp_pos _) hy
    _ = (Nat.factorial m : ℝ) * Real.exp ((m + 1 : ℕ) * |t|) := by
      rw [div_eq_mul_inv, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 2
      push_cast
      ring

/-! ### The boost angle -/

/-- The boost angle is smooth because its derivative is the smooth reciprocal of `boostP`.
@isnad1 id=contdiff.0h1v.s5.78f42cf3ec08 from=translated src=- shape=0fc4d29f vocab=da7f6935
-/
theorem contDiff_boostAngle (t : ℝ) : ContDiff ℝ ∞ (boostAngle t) := by
  have hderiv : deriv (boostAngle t) = (boostP t)⁻¹ := by
    funext θ
    exact (hasDerivAt_boostAngle t θ).deriv
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun θ => (hasDerivAt_boostAngle t θ).differentiableAt, ?_⟩
  rw [hderiv]
  exact (contDiff_boostP t).inv (fun θ => (boostP_pos t θ).ne')

/-- Every positive-order angle derivative of `boostAngle` has exponential growth in `|t|`.
The deliberately crude coefficient is convenient for later composition estimates.
@isnad1 id=le.0h3v.s6.9d2b1156008e from=translated src=- shape=8fe972bd vocab=85d57a5a
-/
theorem norm_iteratedDeriv_boostAngle_le (t : ℝ) (m : ℕ) (θ : ℝ) :
    ‖iteratedDeriv (m + 1) (boostAngle t) θ‖ ≤
      (Nat.factorial m : ℝ) ^ 2 *
        Real.exp (((m + 1 : ℕ) : ℝ) * |t| + (m : ℝ) * |t|) := by
  let c : ℝ := Real.exp (-|t|)
  have hc : 0 < c := Real.exp_pos _
  have hrange : Set.range (boostP t) ⊆ Set.Ici c := by
    rintro y ⟨x, rfl⟩
    exact exp_neg_abs_le_boostP t x
  have hinv : ContDiffOn ℝ ∞ (Inv.inv : ℝ → ℝ) (Set.Ici c) := by
    intro y hy
    exact (contDiffAt_inv ℝ (hc.trans_le hy).ne').contDiffWithinAt
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) (Set.Ici c) (boostP t θ)‖ ≤
        (Nat.factorial m : ℝ) * Real.exp ((m + 1 : ℕ) * |t|) := by
    intro i hi
    have hmem : boostP t θ ∈ Set.Ici c := hrange ⟨θ, rfl⟩
    have hnonzero : boostP t θ ≠ 0 := (boostP_pos t θ).ne'
    have hcd : ContDiffAt ℝ i (Inv.inv : ℝ → ℝ) (boostP t θ) :=
      contDiffAt_inv ℝ hnonzero
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici c) hcd hmem,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    calc
      ‖iteratedDeriv i (Inv.inv : ℝ → ℝ) (boostP t θ)‖
          ≤ (Nat.factorial i : ℝ) * Real.exp ((i + 1 : ℕ) * |t|) :=
            norm_iteratedDeriv_inv_le_exp t i (exp_neg_abs_le_boostP t θ)
      _ ≤ (Nat.factorial m : ℝ) * Real.exp ((m + 1 : ℕ) * |t|) := by
        have hfac : (Nat.factorial i : ℝ) ≤ (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_le hi
        have hexp : Real.exp ((i + 1 : ℕ) * |t|) ≤
            Real.exp ((m + 1 : ℕ) * |t|) := by
          apply Real.exp_le_exp_of_le
          have him : (i : ℝ) ≤ m := by exact_mod_cast hi
          push_cast
          nlinarith [abs_nonneg t]
        exact mul_le_mul hfac hexp (Real.exp_nonneg _) (Nat.cast_nonneg _)
  have hD : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i (boostP t) θ‖ ≤ Real.exp |t| ^ i := by
    intro i hi _
    have hi_eq : i = (i - 1) + 1 := by omega
    calc
      ‖iteratedFDeriv ℝ i (boostP t) θ‖
          = ‖iteratedDeriv i (boostP t) θ‖ :=
            norm_iteratedFDeriv_eq_norm_iteratedDeriv
      _ ≤ Real.exp |t| := by
        rw [hi_eq]
        exact norm_iteratedDeriv_boostP_le t (i - 1) θ
      _ ≤ Real.exp |t| ^ i :=
        le_self_pow₀ (Real.one_le_exp (abs_nonneg t)) (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le'
    (𝕜 := ℝ) (g := Inv.inv) (f := boostP t) (n := m) (N := ∞)
    hrange (uniqueDiffOn_Ici c) hinv (contDiff_boostP t) (WithTop.coe_le_coe.mpr le_top) θ hC hD
  have hderiv : deriv (boostAngle t) = (boostP t)⁻¹ := by
    funext x
    exact (hasDerivAt_boostAngle t x).deriv
  rw [iteratedDeriv_succ', hderiv]
  calc
    ‖iteratedDeriv m (boostP t)⁻¹ θ‖
        = ‖iteratedFDeriv ℝ m (Inv.inv ∘ boostP t) θ‖ := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          rfl
    _ ≤ (Nat.factorial m : ℝ) * ((Nat.factorial m : ℝ) * Real.exp ((m + 1 : ℕ) * |t|)) *
          Real.exp |t| ^ m := hcomp
    _ = (Nat.factorial m : ℝ) ^ 2 *
          Real.exp (((m + 1 : ℕ) : ℝ) * |t| + (m : ℝ) * |t|) := by
      rw [← Real.exp_nat_mul]
      calc
        (Nat.factorial m : ℝ) * ((Nat.factorial m : ℝ) * Real.exp ((m + 1 : ℕ) * |t|)) *
              Real.exp ((m : ℝ) * |t|) =
            (Nat.factorial m : ℝ) ^ 2 *
              (Real.exp ((m + 1 : ℕ) * |t|) * Real.exp ((m : ℝ) * |t|)) := by ring
        _ = (Nat.factorial m : ℝ) ^ 2 *
              Real.exp (((m + 1 : ℕ) : ℝ) * |t| + (m : ℝ) * |t|) := by
          rw [← Real.exp_add]

end

end MobiusCPT
