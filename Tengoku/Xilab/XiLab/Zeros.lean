import Tengoku
import Tengoku.Xilab.XiLab.Kernel
import Tengoku.Xilab.XiLab.Growth
import Tengoku.Xilab.XiLab.FGrowth
import Tengoku.Xilab.XiLab.OrderOneGen
import Tengoku.Xilab.XiLab.Symmetry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms F_zeros_infinite` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms theorem_3_3` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_poly_sq_of_finite_zeros` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_pos_lower_bound_Phi_Icc` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lower_bound_setIntegral` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms norm_eval_le_pow` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.Zeros — infinitude of the zero set, and the packaged Theorem 3.3

Consumes `XiLab/Kernel.lean`
(`Phi`, `Phi_pos`, `continuous_Phi`, `integrableOn_Phi_mul_rsinh`, `F`,
`differentiable_F`), `XiLab/FGrowth.lean` (`hasOrderLeOne_F`, `F_neg`),
`XiLab/OrderOneGen.lean` (`exists_poly_mul_exp_of_finite_zeros_of_hasOrderLeOne`)
and `XiLab/Symmetry.lean` (`F_ofReal`, `zero_quartet`,
`re_ne_zero_and_im_ne_zero_of_zero`).

## Main results

* `XiLab.exists_poly_sq_of_finite_zeros` — if `F` had finitely many zeros then `F²`
  would be a **polynomial function**.
* `XiLab.lower_bound_setIntegral` — `m · sinh x ≤ ∫₀^∞ Φ(u) sinh(xu) du` for `x ≥ 1`.
* `XiLab.F_zeros_infinite` — `{z | F z = 0}` is infinite.
* `XiLab.theorem_3_3` — the three conclusions of the paper's Theorem 3.3, packaged.

## The argument

Suppose `{z | F z = 0}` were finite.  Hadamard (order ≤ 1, finitely many zeros)
gives `F z = P(z) · exp(a z + b)`.  The **key trick** is to look at `F(z)·F(−z)`
rather than at `F` itself:

```
F(z) · F(−z) = P(z) exp(az+b) · P(−z) exp(−az+b) = P(z) P(−z) exp(2b),
```

so the exponential factor cancels *identically* — no growth comparison and no case
split on `a` is needed.  Since `F` is odd (`FGrowth.F_neg`), `F(z)·F(−z) = −F(z)²`,
whence

```
F(z)² = −exp(2b) · P(z) · P(−z) =: Q(z)
```

is a polynomial function (`exists_poly_sq_of_finite_zeros`).

On the other hand `F` is real and positive on `(0,∞)` (`Symmetry.F_ofReal`), and
restricting the integral to `(1,2]` — where `Φ ≥ m > 0` by compactness and
`sinh(xu) ≥ sinh x` by monotonicity — gives `F(x) ≥ 2 m sinh x ≥ m e^x / 2` for
`x ≥ 1` (`lower_bound_setIntegral`).  Hence `F(x)² ≥ (m²/4) e^x`, while
`|Q(x)| ≤ C x^{deg Q}` for `x ≥ 1` (`norm_eval_le_pow`).  Since
`x^n e^{-x} → 0` (`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`) the two are
incompatible, and the zero set must be infinite.

Every theorem in this file is `sorry`-free; see the axiom audit at the bottom.
-/

open scoped Real ComplexConjugate
open MeasureTheory Set Filter Topology

namespace XiLab

/-! ### Step 1 — `F²` would be a polynomial function -/

/-- **The exponential cancels in `F(z)·F(−z)`.**  If `F` had finitely many zeros then
`F²` would be the evaluation of a fixed polynomial.

Hadamard's factorization for order `≤ 1` supplies `F z = P(z) exp(a z + b)`; multiplying
the value at `z` by the value at `−z` cancels the `a z` term in the exponent, and oddness
of `F` turns the left side into `−F(z)²`.  The parameter `a` disappears entirely, so no
case analysis on it is required.
@isnad1 id=ex.1h0v.s5.83f35dd35581 from=translated src=- shape=ce8b06c9 vocab=fa4e9bc5
-/
theorem exists_poly_sq_of_finite_zeros (hfin : {z : ℂ | F z = 0}.Finite) :
    ∃ Q : Polynomial ℂ, ∀ z : ℂ, F z ^ 2 = Q.eval z := by
  obtain ⟨P, a, b, hP⟩ :=
    exists_poly_mul_exp_of_finite_zeros_of_hasOrderLeOne differentiable_F hasOrderLeOne_F hfin
  refine ⟨Polynomial.C (-(Complex.exp (2 * b))) * P * P.comp (-Polynomial.X), fun z => ?_⟩
  have hz := hP z
  have hnz := hP (-z)
  rw [F_neg z] at hnz
  have h3 : Complex.exp (a * z + b) * Complex.exp (a * -z + b) = Complex.exp (2 * b) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hQe : (Polynomial.C (-(Complex.exp (2 * b))) * P * P.comp (-Polynomial.X)).eval z
      = -(Complex.exp (2 * b)) * (P.eval z * P.eval (-z)) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X]
    ring
  have key : F z ^ 2 = -(F z * -F z) := by ring
  rw [key, hnz, hz, hQe, ← h3]
  ring

/-! ### Step 2 — a superpolynomial lower bound on the positive real axis -/

/-- `Φ` has a strictly positive lower bound on the compact interval `[1,2]`.

The value of the bound is astronomically small (`Φ(2) ≈ 1e-69`); only its positivity is
used.  Extreme value theorem + `Kernel.Phi_pos`.
@isnad1 id=ex.0h0v.s5.3ddf3c6f7653 from=translated src=- shape=3ec52be7 vocab=8ba79539
-/
theorem exists_pos_lower_bound_Phi_Icc :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc (1 : ℝ) 2, m ≤ Phi u := by
  obtain ⟨x₀, hx₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (s := Icc (1 : ℝ) 2)
      (Set.nonempty_Icc.mpr (by norm_num)) continuous_Phi.continuousOn
  refine ⟨Phi x₀, Phi_pos (by linarith [hx₀.1]), fun u hu => isMinOn_iff.mp hmin u hu⟩

/-- **`∫₀^∞ Φ(u) sinh(xu) du ≥ m sinh x` for `x ≥ 1`.**

The integrand is nonnegative on `(0,∞)`, so the integral only grows when the domain is
enlarged from `(1,2]` to `(0,∞)`.  On `(1,2]` one has `Φ(u) ≥ m` and, since `u ≥ 1` and
`x > 0`, `sinh(xu) ≥ sinh(x)`; the interval has length `1`.
@isnad1 id=le.3h2v.s7.46c40ace41fd from=translated src=- shape=1117710e vocab=09661a7b
-/
theorem lower_bound_setIntegral {m x : ℝ} (hm0 : 0 < m)
    (hm : ∀ u ∈ Icc (1 : ℝ) 2, m ≤ Phi u) (hx : 1 ≤ x) :
    m * Real.sinh x ≤ ∫ u in Ioi (0 : ℝ), Phi u * Real.sinh (x * u) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := fun u hu => lt_trans zero_lt_one hu.1
  have hintIoi := integrableOn_Phi_mul_rsinh x
  have hintIoc : IntegrableOn (fun u : ℝ => Phi u * Real.sinh (x * u)) (Ioc (1 : ℝ) 2) :=
    hintIoi.mono_set hsub
  have hconstint : IntegrableOn (fun _ : ℝ => m * Real.sinh x) (Ioc (1 : ℝ) 2) := by
    refine integrableOn_const ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hstep2 : ∫ _u in Ioc (1 : ℝ) 2, (m * Real.sinh x)
      ≤ ∫ u in Ioc (1 : ℝ) 2, Phi u * Real.sinh (x * u) := by
    refine setIntegral_mono_on hconstint hintIoc measurableSet_Ioc (fun u hu => ?_)
    have hu1 : (1 : ℝ) ≤ u := hu.1.le
    have hmu : m ≤ Phi u := hm u ⟨hu1, hu.2⟩
    have hsx : Real.sinh x ≤ Real.sinh (x * u) :=
      Real.sinh_le_sinh.mpr (le_mul_of_one_le_right hx0.le hu1)
    have hsx0 : (0 : ℝ) ≤ Real.sinh x := (Real.sinh_pos_iff.mpr hx0).le
    exact mul_le_mul hmu hsx hsx0 (le_trans hm0.le hmu)
  have hconstval : ∫ _u in Ioc (1 : ℝ) 2, (m * Real.sinh x) = m * Real.sinh x := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num
  rw [hconstval] at hstep2
  have hle : (Ioc (1 : ℝ) 2) ≤ᵐ[volume] (Ioi (0 : ℝ)) :=
    Filter.Eventually.of_forall (fun u (hu : u ∈ Ioc (1 : ℝ) 2) => hsub hu)
  have hstep1 : ∫ u in Ioc (1 : ℝ) 2, Phi u * Real.sinh (x * u)
      ≤ ∫ u in Ioi (0 : ℝ), Phi u * Real.sinh (x * u) := by
    refine setIntegral_mono_set hintIoi ?_ hle
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact mul_nonneg (Phi_nonneg (mem_Ioi.mp hu).le)
      (Real.sinh_pos_iff.mpr (mul_pos hx0 (mem_Ioi.mp hu))).le
  linarith

/-! ### Step 3 — polynomials are `O(xⁿ)` -/

/-- A crude but sufficient polynomial bound on the real axis: for `x ≥ 1`,
`‖Q(x)‖ ≤ (∑ ‖coeff i‖) · x^{natDegree Q}`.
@isnad1 id=le.1h2v.s6.6d862651bb46 from=translated src=- shape=6650fd57 vocab=f3ba26ed
-/
theorem norm_eval_le_pow {Q : Polynomial ℂ} {x : ℝ} (hx : 1 ≤ x) :
    ‖Q.eval (x : ℂ)‖
      ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖) * x ^ Q.natDegree := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i hi => ?_))
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hi') (norm_nonneg _)

/-! ### The theorem -/

/-- **Theorem 3.3, first conclusion: `F` has infinitely many zeros.**

Contradiction.  A finite zero set forces `F² = Q` for a polynomial `Q`
(`exists_poly_sq_of_finite_zeros`), while `F(x)² ≥ (m²/4) e^x` on `[1,∞)`
(`lower_bound_setIntegral`) outgrows every polynomial.
@isnad1 id=infinite.0h0v.s4.852b8417691b from=translated src=- shape=50446660 vocab=0966574a
-/
theorem F_zeros_infinite : {z : ℂ | F z = 0}.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  obtain ⟨Q, hQ⟩ := exists_poly_sq_of_finite_zeros hcon
  obtain ⟨m, hm0, hm⟩ := exists_pos_lower_bound_Phi_Icc
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Q.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖ := ⟨_, rfl⟩
  have hC0 : (0 : ℝ) ≤ C := by
    rw [hCdef]; exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have key : ∀ x : ℝ, 1 ≤ x → m ^ 2 / 4 * Real.exp x ≤ C * x ^ n := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hlow := lower_bound_setIntegral hm0 hm hx
    have hex2 : (2 : ℝ) ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hsinh : Real.exp x / 4 ≤ Real.sinh x := by
      rw [Real.sinh_eq]
      have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = 2 * ∫ u in Ioi (0 : ℝ), Phi u * Real.sinh (x * u) := ⟨_, rfl⟩
    have hglow : m * Real.exp x / 2 ≤ g := by
      have h2 : m * (Real.exp x / 4) ≤ m * Real.sinh x :=
        mul_le_mul_of_nonneg_left hsinh hm0.le
      rw [hgdef]; linarith
    have hFx : F (x : ℂ) = ((g : ℝ) : ℂ) := by rw [hgdef]; exact F_ofReal x
    have hnorm : ‖Q.eval (x : ℂ)‖ = g ^ 2 := by
      rw [← hQ, hFx, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg g)]
    have hub : g ^ 2 ≤ C * x ^ n := by
      rw [← hnorm, hCdef, hn]; exact norm_eval_le_pow hx
    have hlb : m ^ 2 / 4 * Real.exp x ≤ g ^ 2 := by
      have h1 : (m * Real.exp x / 2) ^ 2 ≤ g ^ 2 :=
        pow_le_pow_left₀ (by positivity) hglow 2
      have hxe : (1 : ℝ) ≤ Real.exp x := by linarith
      nlinarith [sq_nonneg m, Real.exp_pos x, hm0]
    linarith
  have hlim : Tendsto (fun x : ℝ => C * (x ^ n * Real.exp (-x))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul C
  have hpos : (0 : ℝ) < m ^ 2 / 4 := by positivity
  have hev := hlim.eventually_lt_const hpos
  obtain ⟨x, hx1, hx2⟩ := ((eventually_ge_atTop (1 : ℝ)).and hev).exists
  have hexp : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hne : Real.exp x ≠ 0 := ne_of_gt hexp
  rw [Real.exp_neg] at hx2
  have h6 := mul_lt_mul_of_pos_right hx2 hexp
  have hrw : C * (x ^ n * (Real.exp x)⁻¹) * Real.exp x = C * x ^ n := by field_simp
  rw [hrw] at h6
  linarith [key x hx1]

/-- **Theorem 3.3, packaged.**  `F` has infinitely many zeros; every nonzero zero has both
coordinates nonzero; and the zeros come in quartets `±w, ±w̄`.
@isnad1 id=and.0h0v.s7.6e0bdda8e487 from=translated src=- shape=2da985dc vocab=ae0eaff4
-/
theorem theorem_3_3 :
    {z : ℂ | F z = 0}.Infinite ∧
    (∀ w : ℂ, F w = 0 → w ≠ 0 → w.re ≠ 0 ∧ w.im ≠ 0) ∧
    (∀ w : ℂ, F w = 0 → F (-w) = 0 ∧ F (starRingEnd ℂ w) = 0 ∧ F (-(starRingEnd ℂ) w) = 0) :=
  ⟨F_zeros_infinite,
   fun _ hw hne => re_ne_zero_and_im_ne_zero_of_zero hw hne,
   fun _ hw => zero_quartet hw⟩

/-! ### Axiom audit

No `sorry`, no `native_decide`, no custom `axiom` anywhere in this file. -/
section AxiomAudit
end AxiomAudit

end XiLab

/-! ### Target signatures, pinned verbatim -/
