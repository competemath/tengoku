import Tengoku.AbelFormalization.AbelFormalization.TransferFiniteBounds
import Tengoku.Seed.Algebra.MvPolynomial.Eval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial bounds and rapidly decaying coordinate perturbations

This module packages the finite polynomial estimate used in quantitative
transfer.  Polynomially bounded coefficients and coordinates give a
polynomially bounded evaluation.  If two coordinate assignments differ by a
superpolynomially decaying function in every coordinate, evaluation of any
fixed multivariate polynomial at those assignments differs by a
superpolynomially decaying function.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Topology

variable {X R sigma : Type*}

/-- A real-valued function has an eventual upper bound by one fixed natural
power of the scale.-/
def HasPolynomialUpperBound (l : Filter X) (S : X → ℝ)
    (f : X → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
    ∀ᶠ x in l, |f x| ≤ C * (S x) ^ P

namespace HasPolynomialUpperBound

/--
@isnad1 id=haspolyn.2h5v.s5.9e2927a06306 from=translated src=- shape=115c9b91 vocab=a59bc858
-/
theorem congr {l : Filter X} {S f g : X → ℝ}
    (hf : HasPolynomialUpperBound l S f) (hfg : ∀ x, g x = f x) :
    HasPolynomialUpperBound l S g := by
  obtain ⟨C, hC, P, hf⟩ := hf
  refine ⟨C, hC, P, ?_⟩
  filter_upwards [hf] with x hx
  rw [hfg x]
  exact hx

/--
@isnad1 id=haspolyn.0h4v.s4.00478fbd2660 from=translated src=- shape=dae4d1aa vocab=a59bc858
-/
theorem const (l : Filter X) (S : X → ℝ) (c : ℝ) :
    HasPolynomialUpperBound l S (fun _ => c) := by
  refine ⟨|c| + 1, by positivity, 0, ?_⟩
  filter_upwards with x
  simp

/--
@isnad1 id=haspolyn.0h3v.s4.1295cf8bdc46 from=translated src=- shape=7fe5948b vocab=a59bc858
-/
theorem zero (l : Filter X) (S : X → ℝ) :
    HasPolynomialUpperBound l S (fun _ => 0) := by
  simpa using const l S 0

/--
@isnad1 id=haspolyn.0h3v.s4.6d642fd81880 from=translated src=- shape=7fe5948b vocab=a59bc858
-/
theorem one (l : Filter X) (S : X → ℝ) :
    HasPolynomialUpperBound l S (fun _ => 1) := by
  simpa using const l S 1

/--
@isnad1 id=haspolyn.1h4v.s4.e40f65cdc2fe from=translated src=- shape=acd8765f vocab=d0efd78d
-/
theorem neg {l : Filter X} {S f : X → ℝ}
    (hf : HasPolynomialUpperBound l S f) :
    HasPolynomialUpperBound l S (fun x => -f x) := by
  obtain ⟨C, hC, P, hf⟩ := hf
  exact ⟨C, hC, P, hf.mono (fun x hx => by simpa)⟩

/--
@isnad1 id=haspolyn.3h5v.s6.05d038833cc0 from=translated src=- shape=a36862f1 vocab=06206be3
-/
theorem add {l : Filter X} {S f g : X → ℝ}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (hf : HasPolynomialUpperBound l S f)
    (hg : HasPolynomialUpperBound l S g) :
    HasPolynomialUpperBound l S (fun x => f x + g x) := by
  obtain ⟨Cf, hCf, Pf, hf⟩ := hf
  obtain ⟨Cg, hCg, Pg, hg⟩ := hg
  refine ⟨Cf + Cg, add_pos hCf hCg, Pf + Pg, ?_⟩
  filter_upwards [hS, hf, hg] with x hxS hxf hxg
  have hfPow : (S x) ^ Pf ≤ (S x) ^ (Pf + Pg) :=
    pow_le_pow_right₀ hxS (Nat.le_add_right Pf Pg)
  have hgPow : (S x) ^ Pg ≤ (S x) ^ (Pf + Pg) :=
    pow_le_pow_right₀ hxS (Nat.le_add_left Pg Pf)
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Cf * (S x) ^ Pf + Cg * (S x) ^ Pg := add_le_add hxf hxg
    _ ≤ Cf * (S x) ^ (Pf + Pg) + Cg * (S x) ^ (Pf + Pg) :=
      add_le_add (mul_le_mul_of_nonneg_left hfPow hCf.le)
        (mul_le_mul_of_nonneg_left hgPow hCg.le)
    _ = (Cf + Cg) * (S x) ^ (Pf + Pg) := by ring

/--
@isnad1 id=haspolyn.3h5v.s6.1460aaf02730 from=translated src=- shape=a36862f1 vocab=e8b6a221
-/
theorem sub {l : Filter X} {S f g : X → ℝ}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (hf : HasPolynomialUpperBound l S f)
    (hg : HasPolynomialUpperBound l S g) :
    HasPolynomialUpperBound l S (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hS hg.neg

/--
@isnad1 id=haspolyn.2h5v.s5.1b77d893f8bd from=translated src=- shape=130b7d40 vocab=9abc73ff
-/
theorem mul {l : Filter X} {S f g : X → ℝ}
    (hf : HasPolynomialUpperBound l S f)
    (hg : HasPolynomialUpperBound l S g) :
    HasPolynomialUpperBound l S (fun x => f x * g x) := by
  obtain ⟨Cf, hCf, Pf, hf⟩ := hf
  obtain ⟨Cg, hCg, Pg, hg⟩ := hg
  refine ⟨Cf * Cg, mul_pos hCf hCg, Pf + Pg, ?_⟩
  filter_upwards [hf, hg] with x hxf hxg
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (Cf * (S x) ^ Pf) * (Cg * (S x) ^ Pg) :=
      mul_le_mul hxf hxg (abs_nonneg _) ((abs_nonneg _).trans hxf)
    _ = (Cf * Cg) * (S x) ^ (Pf + Pg) := by rw [pow_add]; ring

/--
@isnad1 id=haspolyn.1h5v.s5.1cd54c4e4fa6 from=translated src=- shape=04241e24 vocab=005c4cb0
-/
theorem pow {l : Filter X} {S f : X → ℝ}
    (hf : HasPolynomialUpperBound l S f) (n : ℕ) :
    HasPolynomialUpperBound l S (fun x => (f x) ^ n) := by
  induction n with
  | zero => simpa using one l S
  | succ n ih =>
      simpa only [pow_succ] using ih.mul hf

end HasPolynomialUpperBound

/-- Multiplying a rapidly decaying function by a polynomially bounded one
preserves rapid decay.
@isnad1 id=superpol.3h5v.s6.3fea83756db7 from=translated src=- shape=05b150c9 vocab=16848f5b
-/
theorem Asymptotics.SuperpolynomialDecay.mul_of_hasPolynomialUpperBound
    {l : Filter X} {S e f : X → ℝ}
    (he : Asymptotics.SuperpolynomialDecay l S e)
    (hS : ∀ᶠ x in l, 0 ≤ S x)
    (hf : HasPolynomialUpperBound l S f) :
    Asymptotics.SuperpolynomialDecay l S (fun x => e x * f x) := by
  obtain ⟨C, hC, P, hf⟩ := hf
  exact Asymptotics.SuperpolynomialDecay.mul_of_polynomialBound
    he hS hC.le hf

/-- Evaluation of a fixed polynomial at polynomially bounded coefficient and
coordinate functions is polynomially bounded.
@isnad1 id=haspolyn.3h8v.s8.11277978367f from=translated src=- shape=801f4662 vocab=6c1056b6
-/
theorem mvPolynomial_eval₂Hom_hasPolynomialUpperBound
    [CommRing R]
    {l : Filter X} {S : X → ℝ}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (c : R →+* (X → ℝ)) (y : sigma → X → ℝ)
    (hc : ∀ r, HasPolynomialUpperBound l S (c r))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i))
    (p : MvPolynomial sigma R) :
    HasPolynomialUpperBound l S (MvPolynomial.eval₂Hom c y p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using hc r
  | add p q hp hq =>
      apply (hp.add hS hq).congr
      intro x
      simp
  | mul_X p i hp =>
      apply (hp.mul (hy i)).congr
      intro x
      simp

/-- Substituting coordinatewise rapidly decaying perturbations into a fixed
multivariate polynomial changes its value by a rapidly decaying function.
The coefficient functions may vary along the filter, provided each fixed
coefficient is polynomially bounded.
@isnad1 id=superpol.5h9v.s8.a30cf7d6f666 from=translated src=- shape=c18a5e4f vocab=e3ff0c73
-/
theorem mvPolynomial_eval₂Hom_sub_superpolynomialDecay
    [CommRing R]
    {l : Filter X} {S : X → ℝ}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (c : R →+* (X → ℝ)) (y z : sigma → X → ℝ)
    (hc : ∀ r, HasPolynomialUpperBound l S (c r))
    (hy : ∀ i, HasPolynomialUpperBound l S (y i))
    (hz : ∀ i, HasPolynomialUpperBound l S (z i))
    (hyz : ∀ i, Asymptotics.SuperpolynomialDecay l S
      (fun x => y i x - z i x))
    (p : MvPolynomial sigma R) :
    Asymptotics.SuperpolynomialDecay l S (fun x =>
      MvPolynomial.eval₂Hom c y p x - MvPolynomial.eval₂Hom c z p x) := by
  have hS0 : ∀ᶠ x in l, 0 ≤ S x := hS.mono (fun _ hx => zero_le_one.trans hx)
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact (Asymptotics.superpolynomialDecay_zero l S).congr (by simp)
  | add p q hp hq =>
      exact (hp.add hq).congr (fun x => by simp; ring)
  | mul_X p i hp =>
      have hpy := mvPolynomial_eval₂Hom_hasPolynomialUpperBound
        hS c z hc hz p
      have hfirst :=
        Asymptotics.SuperpolynomialDecay.mul_of_hasPolynomialUpperBound
          hp hS0 (hy i)
      have hsecond :=
        Asymptotics.SuperpolynomialDecay.mul_of_hasPolynomialUpperBound
          (hyz i) hS0 hpy
      exact (hfirst.add hsecond).congr (fun x => by simp; ring)

end AbelFormalization
