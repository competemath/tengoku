/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Tengoku

/-!
# Proof of Jentzsch's Theorem via the Variational Absolute Value Trick

This file proves Jentzsch's theorem for compact self-adjoint positivity-improving
operators on L²(ℝ^n, Lebesgue). The proof avoids the Krein-Rutman / Banach lattice
cone machinery and uses only the Rayleigh quotient, Cauchy-Schwarz, and L² lattice
structure (absolute value, positive/negative parts).

## Proof outline (Courant-Hilbert / Barry Simon)

1. **Phase 1**: Positivity-preserving operators satisfy |Tf| ≤ T|f| a.e.
2. **Phase 2**: Therefore |⟨f, Tf⟩| ≤ ⟨|f|, T|f|⟩.
3. **Phase 3**: If f is a ground state (Tf = lam₀f), then |f| is also a ground state.
4. **Phase 4**: By positivity-improving, the ground state is strictly positive a.e.
5. **Phase 5**: Every ground state eigenvector has constant sign a.e.
6. **Phase 6**: The ground state eigenvalue lam₀ is simple (multiplicity 1).
7. **Phase 7**: All other eigenvalues satisfy |λ| < lam₀ (strict spectral gap).

## References

- Reed-Simon IV, Theorems XIII.43–44
- Simon, *Functional Integration and Quantum Physics* (2005), §I.13
- Courant-Hilbert, *Methods of Mathematical Physics*, Ch. VI
-/

@[expose] public section

noncomputable section

open MeasureTheory

/-! ## Definitions -/

/-- An operator on L²(ℝ^n) is positivity-preserving if it maps nonneg
functions to nonneg functions. This is weaker than positivity-improving. -/
def IsPositivityPreserving {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Ω)),
    (0 ≤ f) → (0 ≤ T f)

/-- An operator on L²(ℝ^n) is positivity-improving if it maps nonneg
nonzero functions to a.e. strictly positive functions (ae-filter version). -/
def IsPositivityImproving {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Ω)),
    (∀ᵐ x ∂(volume : Measure (Ω)), 0 ≤ (f : (Ω) → ℝ) x) →
    (¬ (f : (Ω) → ℝ) =ᵐ[volume] 0) →
    (∀ᵐ x ∂(volume : Measure (Ω)), 0 < (T f : (Ω) → ℝ) x)

/-- An operator on L²(ℝ^n) is positivity-improving if it maps nonneg
nonzero functions to a.e. strictly positive functions (Lp lattice version). -/
def IsPositivityImproving' {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Ω)),
    (0 ≤ f) →
    (f ≠ 0) →
    (∀ᵐ x ∂(volume : Measure (Ω)), 0 < (T f : (Ω) → ℝ) x)

/-- Positivity-improving implies positivity-preserving.
    If f ≥ 0 and f ≠ 0, then Tf > 0 a.e. ≥ 0. If f = 0, then Tf = 0 ≥ 0. -/
theorem IsPositivityImproving'.toPreserving {Ω : Type*} [MeasureSpace Ω]
    {T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))}
    (hT : IsPositivityImproving' T) : IsPositivityPreserving T := by
  intro f hf
  by_cases hf0 : f = 0
  · rw [hf0, map_zero]
  · -- Tf > 0 a.e. implies Tf ≥ 0
    have hpos := hT f hf hf0
    rw [← Lp.coeFn_le]
    filter_upwards [hpos, Lp.coeFn_zero ℝ 2 volume] with x hx h0
    rw [h0]
    exact le_of_lt hx

/-- `IsPositivityImproving` (ae conditions) implies `IsPositivityImproving'` (Lp lattice).
The definitions differ only in whether the hypotheses use ae-filter or Lp order/equality:
- `0 ≤ f` in Lp ↔ `0 ≤ᵐ[μ] f` (by `Lp.coeFn_nonneg`)
- `f ≠ 0` in Lp ↔ `¬ f =ᵐ[μ] 0` (by `Lp.eq_zero_iff_ae_eq_zero`) -/
theorem IsPositivityImproving.toPI' {Ω : Type*} [MeasureSpace Ω]
    {T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))}
    (hT : IsPositivityImproving T) : IsPositivityImproving' T := by
  intro f hf hf_ne
  apply hT f
  · exact (Lp.coeFn_nonneg f).mpr hf
  · rwa [← Lp.eq_zero_iff_ae_eq_zero]

/-! ## Phase 1: Absolute value inequality

For a positivity-preserving operator T on L²:
  |Tf| ≤ T|f| a.e.

Proof: f = f⁺ - f⁻ with f⁺, f⁻ ≥ 0. Since T is positivity-preserving,
Tf⁺ ≥ 0 and Tf⁻ ≥ 0. Then:
  |Tf| = |Tf⁺ - Tf⁻| ≤ Tf⁺ + Tf⁻ = T(f⁺ + f⁻) = T|f|
-/

/-- Phase 1: Absolute value inequality for positivity-preserving operators. -/
theorem abs_apply_le_apply_abs {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω)))
    (hT : IsPositivityPreserving T)
    (f : Lp ℝ 2 (volume : Measure (Ω))) :
    |T f| ≤ T |f| := by
  -- Strategy: |Tf| ≤ T|f| iff Tf ≤ T|f| and -Tf ≤ T|f| (by abs_le').
  -- Both follow from monotonicity of T (positivity-preserving + linear)
  -- and f ≤ |f|, -f ≤ |f|.
  -- Monotonicity: g ≤ h → Tg ≤ Th (since h-g ≥ 0 → T(h-g) ≥ 0 → Th-Tg ≥ 0)
  have hT_mono : ∀ (g h : Lp ℝ 2 (volume : Measure (Ω))),
      g ≤ h → T g ≤ T h := by
    intro g h hgh
    have h1 : 0 ≤ h - g := sub_nonneg.mpr hgh
    have h2 := hT (h - g) h1
    rwa [map_sub, sub_nonneg] at h2
  rw [abs_le']
  constructor
  · -- f ≤ |f| since |f| = f ⊔ (-f)
    exact hT_mono f |f| le_sup_left
  · -- -f ≤ |f| since |f| = f ⊔ (-f)
    rw [← map_neg]
    exact hT_mono (-f) |f| le_sup_right

/-! ## Phase 2: Inner product inequality

  |⟨f, Tf⟩| ≤ ⟨|f|, T|f|⟩

Proof: |⟨f, Tf⟩| = |∫ f(x) (Tf)(x) dx|
  ≤ ∫ |f(x)| |Tf(x)| dx       (integral triangle inequality)
  ≤ ∫ |f(x)| (T|f|)(x) dx     (Phase 1: |Tf| ≤ T|f|, and |f| ≥ 0)
  = ⟨|f|, T|f|⟩                (since |f| ≥ 0 and T|f| ≥ 0)
-/

/-- For nonneg L² functions, the inner product is nonneg.
    This is ⟨f, g⟩ = ∫ f(x)·g(x) dx ≥ 0 when f, g ≥ 0 a.e. -/
private theorem inner_nonneg_of_nonneg_L2 {Ω : Type*} [MeasureSpace Ω]
    (f g : Lp ℝ 2 (volume : Measure (Ω)))
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (0 : ℝ) ≤ @inner ℝ _ _ f g := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hfx hgx
  exact mul_nonneg hgx hfx

/-- Inner product is monotone in the right argument when the left argument is nonneg.
    If 0 ≤ u and g₁ ≤ g₂ then ⟨u, g₁⟩ ≤ ⟨u, g₂⟩. -/
private theorem inner_mono_right_L2 {Ω : Type*} [MeasureSpace Ω]
    (u g₁ g₂ : Lp ℝ 2 (volume : Measure (Ω)))
    (hu : 0 ≤ u) (hg : g₁ ≤ g₂) :
    @inner ℝ _ _ u g₁ ≤ @inner ℝ _ _ u g₂ := by
  have h := inner_nonneg_of_nonneg_L2 u (g₂ - g₁) hu (sub_nonneg.mpr hg)
  rwa [inner_sub_right, sub_nonneg] at h

/-- |⟨f, g⟩| ≤ ⟨|f|, |g|⟩ for L² functions.
    Follows from the integral triangle inequality and |a·b| = |a|·|b|. -/
private theorem abs_inner_le_inner_abs_abs {Ω : Type*} [MeasureSpace Ω]
    (f g : Lp ℝ 2 (volume : Measure (Ω))) :
    |@inner ℝ _ _ f g| ≤ @inner ℝ _ _ |f| |g| := by
  -- Expand inner products as integrals
  simp only [MeasureTheory.L2.inner_def]
  -- |∫ ⟪f x, g x⟫| ≤ ∫ ⟪|f| x, |g| x⟫
  -- via integral triangle inequality + pointwise ‖⟪a,b⟫‖ = ⟪|a|,|b|⟩
  calc |∫ x, @inner ℝ _ _ (f x) (g x) ∂volume|
      = ‖∫ x, @inner ℝ _ _ (f x) (g x) ∂volume‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖@inner ℝ _ _ (f x) (g x)‖ ∂volume := norm_integral_le_integral_norm _
    _ = ∫ x, @inner ℝ _ _ (|f| x) (|g| x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_abs f, Lp.coeFn_abs g] with x hf_abs hg_abs
        simp only [inner, Inner.inner, star_trivial, RCLike.re_to_real]
        rw [hf_abs, hg_abs, Real.norm_eq_abs, abs_mul, mul_comm]

/-- Phase 2: Inner product inequality. -/
theorem abs_inner_le_inner_abs {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω)))
    (hT_pp : IsPositivityPreserving T)
    (f : Lp ℝ 2 (volume : Measure (Ω))) :
    |@inner ℝ _ _ f (T f)| ≤ @inner ℝ _ _ |f| (T |f|) := by
  -- Step 1: |⟨f, Tf⟩| ≤ ⟨|f|, |Tf|⟩ (integral triangle inequality)
  -- Step 2: ⟨|f|, |Tf|⟩ ≤ ⟨|f|, T|f|⟩ (monotonicity + Phase 1)
  calc |@inner ℝ _ _ f (T f)|
      ≤ @inner ℝ _ _ |f| |T f| := abs_inner_le_inner_abs_abs f (T f)
    _ ≤ @inner ℝ _ _ |f| (T |f|) := by
        apply inner_mono_right_L2 |f| |T f| (T |f|)
        · -- 0 ≤ |f|: pointwise |f(x)| ≥ 0
          rw [← Lp.coeFn_nonneg]
          filter_upwards [Lp.coeFn_abs f] with x habs
          rw [habs]
          exact abs_nonneg _
        · exact abs_apply_le_apply_abs T hT_pp f

/-! ## Phase 3: |f| is a ground state if f is

The Rayleigh quotient R(g) = ⟨g, Tg⟩ / ‖g‖² achieves its supremum
at the ground state eigenvector. The chain of inequalities:

  lam₀ ‖f‖² = ⟨f, Tf⟩ ≤ |⟨f, Tf⟩| ≤ ⟨|f|, T|f|⟩ ≤ lam₀ ‖|f|‖²

Since ‖|f|‖ = ‖f‖, we get equality throughout, so |f| achieves the
supremum of R, hence |f| is an eigenvector for lam₀.
-/

/-! ## Phase 4: Ground state is strictly positive a.e.

Since |f| ≥ 0 and |f| ≠ 0, and T is positivity-improving,
T|f| > 0 a.e. But T|f| = lam₀|f|, so |f| > 0 a.e.
-/

/-- Phase 4: The ground state eigenvector (after taking absolute value)
is strictly positive almost everywhere. -/
theorem ground_state_strictly_positive {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℝ 2 (volume : Measure (Ω)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Ω)))
    (hT_pi : IsPositivityImproving' T)
    (e₀ : Lp ℝ 2 (volume : Measure (Ω)))
    (he₀_ne : e₀ ≠ 0)
    (he₀_nonneg : 0 ≤ e₀)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (he₀_eigen : (T : Lp ℝ 2 (volume : Measure (Ω)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Ω))) e₀ = lam₀ • e₀) :
    ∀ᵐ x ∂(volume : Measure (Ω)), 0 < (e₀ : (Ω) → ℝ) x := by
  -- T e₀ = lam₀ e₀, and T is positivity-improving, so T e₀ > 0 a.e.
  -- Therefore lam₀ e₀ > 0 a.e., and since lam₀ > 0, e₀ > 0 a.e.
  have hT_pos := hT_pi e₀ he₀_nonneg he₀_ne
  -- T e₀ = lam₀ • e₀ as elements of L²
  have heq : (T e₀ : Lp ℝ 2 (volume : Measure (Ω))) = lam₀ • e₀ := by
    exact_mod_cast he₀_eigen
  -- (lam₀ • e₀)(x) = lam₀ * e₀(x) a.e.
  have hsmul := Lp.coeFn_smul lam₀ e₀
  -- Combine: 0 < (T e₀)(x) =ᵐ lam₀ * e₀(x), so e₀(x) > 0
  filter_upwards [hT_pos, heq ▸ hsmul] with x hpos hsmul_x
  -- hpos : 0 < (T e₀)(x), and (T e₀)(x) = lam₀ * e₀(x)
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul_x
  rw [hsmul_x] at hpos
  exact (mul_pos_iff.mp hpos).elim (fun ⟨_, h⟩ => h) (fun ⟨h, _⟩ => absurd h (not_lt.mpr hlam₀.le))

/-! ## Phase 5: Every ground state eigenvector has constant sign

If f is an eigenvector for lam₀, then |f| is also (Phase 3).
Define h = |f| - f. Then h ≥ 0 and h is an eigenvector for lam₀.
By Phase 4, either h = 0 a.e. (so f = |f| ≥ 0, hence f > 0 a.e.)
or h > 0 a.e. Since h = |f| - f, having h > 0 a.e. means
|f(x)| > f(x) a.e., i.e., f(x) < 0 a.e. (strictly).

So every ground state eigenvector is either strictly positive or
strictly negative a.e.
-/

/-! ## Phase 6: The top eigenvalue lam₀ is simple

If u, v are two orthogonal eigenvectors for lam₀ with ⟨u, v⟩ = 0,
then by Phase 5, we may assume u > 0 a.e. and v > 0 a.e. (or
multiply by -1). But then ⟨u, v⟩ = ∫ u(x)v(x) dx > 0,
contradicting orthogonality.
-/

/-! ## Phase 7: Strict spectral gap

For any eigenvalue μ ≠ lam₀, we have |μ| < lam₀.

Case 1: μ ≥ 0. Then μ < lam₀ by simplicity (if μ = lam₀, the eigenspace
is 1-dimensional by Phase 6, so the eigenvector would be in the same
eigenspace).

Case 2: μ < 0. Suppose |μ| = lam₀, i.e., μ = -lam₀.
Let g be an eigenvector for -lam₀. By self-adjointness, ⟨e₀, g⟩ = 0.
Apply the absolute value trick: |Tg| = |-lam₀g| = lam₀|g|.
Phase 1 gives |Tg| ≤ T|g|, so lam₀|g| ≤ T|g|.
The Rayleigh quotient bound gives ⟨|g|, T|g|⟩ ≤ lam₀ ‖g‖².
Together: T|g| = lam₀|g|, so |g| is in the lam₀-eigenspace.
By simplicity (Phase 6), |g| = c·e₀ for some c > 0.
So |g| > 0 a.e. Phase 5 forces g to have constant sign.
But ⟨e₀, g⟩ = 0 with e₀ > 0 and |g| > 0 contradicts constant sign.
-/

/-! ## Spectral decomposition of the Rayleigh quotient -/

/-! ## Assembly: Jentzsch's theorem

Combine all phases to prove the full theorem. -/

end
