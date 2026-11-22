/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.Seed.Analysis.Normed.Lp.lpSpace
public import Tengoku.Seed.Analysis.Normed.Operator.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted `ℓ¹` coefficient infrastructure

The ordinary complex norm is not ultrametric.  We therefore work with honest
`ℓ¹` coefficient estimates: antidiagonal convolution is submultiplicative,
high shifts and low cuts have operator norm at most one, and evaluation on the
unit polydisc is bounded by the `ℓ¹` norm.
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
open Finset
open scoped ENNReal NNReal Topology

noncomputable section

namespace ClassicalComplexWPT

/-- Complex `ℓ¹` coefficients indexed by `I`. -/
abbrev L1Coeff (I : Type*) := lp (fun _ : I ↦ ℂ) 1

namespace L1Coeff

/--
@isnad1 id=summable.0h2v.s8.d934e76b8313 from=translated src=- shape=ea5cb721 vocab=f2407ac1
-/
lemma summable_norm {I : Type*} (f : L1Coeff I) : Summable (fun i ↦ ‖f i‖) := by
  simpa using (lp.memℓp f).summable (p := (1 : ℝ≥0∞)) (by norm_num)

/--
@isnad1 id=eq.0h2v.s8.288662bd35ab from=translated src=- shape=f55f18b0 vocab=4ad2753d
-/
lemma norm_eq_tsum_norm {I : Type*} (f : L1Coeff I) : ‖f‖ = ∑' i, ‖f i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num) f

end L1Coeff

section Convolution

variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

/-- Antidiagonal Cauchy product of two `ℓ¹` coefficient families. -/
def convolutionFun (f g : L1Coeff A) (n : A) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2

/--
@isnad1 id=summable.0h3v.s9.7e75148d45e8 from=translated src=- shape=45aa2c5a vocab=85334ce8
-/
lemma summable_antidiagonal_norm_product (f g : L1Coeff A) :
    Summable (fun n : A ↦ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖) := by
  apply summable_sum_mul_antidiagonal_of_summable_mul
    (A := A) (α := ℝ) (f := fun a ↦ ‖f a‖) (g := fun a ↦ ‖g a‖)
  exact (L1Coeff.summable_norm f).mul_of_nonneg (L1Coeff.summable_norm g)
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)

/--
@isnad1 id=summable.0h3v.s8.5f4111b6632f from=translated src=- shape=719dc092 vocab=9163d94f
-/
lemma summable_norm_convolutionFun (f g : L1Coeff A) :
    Summable (fun n ↦ ‖convolutionFun f g n‖) := by
  refine (summable_antidiagonal_norm_product f g).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  calc
    ‖convolutionFun f g n‖ ≤
        ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1 * g kl.2‖ := norm_sum_le _ _
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
      gcongr with kl hkl
      exact norm_mul_le _ _

/-- Antidiagonal convolution as an `ℓ¹` coefficient family. -/
def convolution (f g : L1Coeff A) : L1Coeff A :=
  ⟨convolutionFun f g, by
    apply memℓp_gen
    simpa using summable_norm_convolutionFun f g⟩

/--
@isnad1 id=eq.0h4v.s9.1ef1d1f6a5e0 from=translated src=- shape=4d05115d vocab=0229d632
-/
@[simp]
lemma convolution_apply (f g : L1Coeff A) (n : A) :
    convolution f g n = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := rfl

/-- The ordinary `ℓ¹` Cauchy-product estimate.
@isnad1 id=le.0h3v.s9.177e0e022646 from=translated src=- shape=6571a24a vocab=f0b719e1
-/
theorem norm_convolution_le (f g : L1Coeff A) : ‖convolution f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  have hf := L1Coeff.summable_norm f
  have hg := L1Coeff.summable_norm g
  have hprod : Summable (fun x : A × A ↦ ‖f x.1‖ * ‖g x.2‖) :=
    hf.mul_of_nonneg hg (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hant := summable_antidiagonal_norm_product f g
  have hconv := summable_norm_convolutionFun f g
  calc
    (∑' n, ‖convolution f g n‖) ≤
        ∑' n, ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
      apply hconv.tsum_le_tsum
      · intro n
        exact calc
          ‖convolution f g n‖ ≤
              ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1 * g kl.2‖ := norm_sum_le _ _
          _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by
            gcongr with kl hkl
            exact norm_mul_le _ _
      · exact hant
    _ = (∑' a, ‖f a‖) * ∑' a, ‖g a‖ := by
      symm
      exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hprod

/--
@isnad1 id=eq.0h4v.s10.e29779233cc4 from=translated src=- shape=38ec70d3 vocab=243c14a6
-/
lemma convolution_add_left (f₁ f₂ g : L1Coeff A) :
    convolution (f₁ + f₂) g = convolution f₁ g + convolution f₂ g := by
  apply lp.ext
  funext n
  simp only [convolution_apply, lp.coeFn_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h4v.s12.2fd29f1a7e9f from=translated src=- shape=0c86841a vocab=e19702fd
-/
lemma convolution_smul_left (c : ℂ) (f g : L1Coeff A) :
    convolution (c • f) g = c • convolution f g := by
  apply lp.ext
  funext n
  simp only [convolution_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

/-- Right convolution as a linear map. -/
def convolutionRightLinear (g : L1Coeff A) : L1Coeff A →ₗ[ℂ] L1Coeff A where
  toFun f := convolution f g
  map_add' f₁ f₂ := convolution_add_left f₁ f₂ g
  map_smul' c f := convolution_smul_left c f g

/-- Right convolution as a continuous linear map. -/
def convolutionRight (g : L1Coeff A) : L1Coeff A →L[ℂ] L1Coeff A :=
  (convolutionRightLinear g).mkContinuous ‖g‖ (fun f ↦ by
    change ‖convolution f g‖ ≤ ‖g‖ * ‖f‖
    simpa [mul_comm] using norm_convolution_le f g)

/--
@isnad1 id=eq.0h3v.s11.7fffdd7640eb from=translated src=- shape=3b38150b vocab=669e7f14
-/
@[simp]
lemma convolutionRight_apply (g f : L1Coeff A) : convolutionRight g f = convolution f g := rfl

/--
@isnad1 id=le.0h2v.s11.19f8e2340f5f from=translated src=- shape=a874e077 vocab=e42ded5a
-/
theorem norm_convolutionRight_le (g : L1Coeff A) : ‖convolutionRight g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖convolution f g‖ ≤ ‖g‖ * ‖f‖
  simpa [mul_comm] using norm_convolution_le f g

end Convolution

section DistinguishedShift

variable {A : Type*}

/-- Index map which discards the first `d` distinguished-variable coefficients. -/
def highIndex (d : ℕ) : A × ℕ → A × ℕ := fun x ↦ (x.1, x.2 + d)

/--
@isnad1 id=injectiv.0h2v.s3.4475b6576055 from=translated src=- shape=cda27322 vocab=3406518e
-/
lemma highIndex_injective (d : ℕ) : Function.Injective (highIndex (A := A) d) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  simp only [highIndex, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, Nat.add_right_cancel h.2⟩

/-- Delete the first `d` distinguished-variable coefficient layers. -/
def highShift (d : ℕ) (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  ⟨fun x ↦ f (highIndex d x), by
    apply memℓp_gen
    simpa [Function.comp_def] using
      (L1Coeff.summable_norm f).comp_injective (highIndex_injective (A := A) d)⟩

/--
@isnad1 id=eq.0h5v.s9.10c073fb24ac from=translated src=- shape=dff8d5a4 vocab=de82d6dc
-/
@[simp]
lemma highShift_apply (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) (n : ℕ) :
    highShift d f (a, n) = f (a, n + d) := rfl

/--
@isnad1 id=le.0h3v.s9.a8a1bdd7c409 from=translated src=- shape=2b6bdad6 vocab=662a5f35
-/
theorem norm_highShift_le (d : ℕ) (f : L1Coeff (A × ℕ)) :
    ‖highShift d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  let e := highIndex (A := A) d
  apply (L1Coeff.summable_norm (highShift d f)).tsum_le_tsum_of_inj e
    (highIndex_injective (A := A) d)
  · intro c hc
    exact norm_nonneg _
  · intro i
    exact le_rfl
  · exact L1Coeff.summable_norm f

/--
@isnad1 id=eq.0h4v.s11.1fe8589a79a3 from=translated src=- shape=b3aa8e96 vocab=4482e540
-/
lemma highShift_add (d : ℕ) (f g : L1Coeff (A × ℕ)) :
    highShift d (f + g) = highShift d f + highShift d g := by
  apply lp.ext
  funext x
  rfl

/--
@isnad1 id=eq.0h4v.s12.6bccd9bb3235 from=translated src=- shape=49f88d9a vocab=9d36d258
-/
lemma highShift_smul (d : ℕ) (c : ℂ) (f : L1Coeff (A × ℕ)) :
    highShift d (c • f) = c • highShift d f := by
  apply lp.ext
  funext x
  rfl

/-- High shift as a complex-linear map. -/
def highShiftLinear (d : ℕ) : L1Coeff (A × ℕ) →ₗ[ℂ] L1Coeff (A × ℕ) where
  toFun := highShift d
  map_add' := highShift_add d
  map_smul' := highShift_smul d

/-- High shift as a contraction. -/
def highShiftCLM (d : ℕ) : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  (highShiftLinear d).mkContinuous 1 (by
    intro f
    change ‖highShift d f‖ ≤ 1 * ‖f‖
    simpa using norm_highShift_le (A := A) d f)

/--
@isnad1 id=le.0h2v.s11.cb4562bde9e9 from=translated src=- shape=3f297705 vocab=9e462a42
-/
theorem norm_highShiftCLM_le (d : ℕ) : ‖highShiftCLM (A := A) d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖highShift d f‖ ≤ 1 * ‖f‖
  simpa using norm_highShift_le (A := A) d f

/-- Keep exactly the distinguished-variable coefficient layers below `d`. -/
def lowCut (d : ℕ) (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  ⟨fun x ↦ if x.2 < d then f x else 0, by
    apply memℓp_gen
    simpa using (L1Coeff.summable_norm f).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun x ↦ by split_ifs <;> simp)⟩

/--
@isnad1 id=eq.1h5v.s9.f64acec069ed from=translated src=- shape=63e48d1a vocab=2bb2fb81
-/
@[simp]
lemma lowCut_apply_of_lt (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : n < d) : lowCut d f (a, n) = f (a, n) := by simp [lowCut, hn]

/--
@isnad1 id=eq.1h5v.s8.343a734392a1 from=translated src=- shape=9e4e424c vocab=f34fc3e9
-/
@[simp]
lemma lowCut_apply_of_le (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : d ≤ n) : lowCut d f (a, n) = 0 := by simp [lowCut, Nat.not_lt.mpr hn]

/--
@isnad1 id=le.0h3v.s9.881eb3d11913 from=translated src=- shape=2b6bdad6 vocab=e9d28fbf
-/
theorem norm_lowCut_le (d : ℕ) (f : L1Coeff (A × ℕ)) : ‖lowCut d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  apply (L1Coeff.summable_norm (lowCut d f)).tsum_le_tsum
  · intro x
    change ‖if x.2 < d then f x else 0‖ ≤ ‖f x‖
    split_ifs <;> simp
  · exact L1Coeff.summable_norm f

/--
@isnad1 id=eq.0h4v.s11.ab94b5cee7fd from=translated src=- shape=b3aa8e96 vocab=b2d573d1
-/
lemma lowCut_add (d : ℕ) (f g : L1Coeff (A × ℕ)) :
    lowCut d (f + g) = lowCut d f + lowCut d g := by
  apply lp.ext
  funext x
  simp only [lowCut, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h4v.s12.b448eec141c2 from=translated src=- shape=49f88d9a vocab=2ea3ca57
-/
lemma lowCut_smul (d : ℕ) (c : ℂ) (f : L1Coeff (A × ℕ)) :
    lowCut d (c • f) = c • lowCut d f := by
  apply lp.ext
  funext x
  simp only [lowCut, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

/-- Low-degree cutoff as a complex-linear map. -/
def lowCutLinear (d : ℕ) : L1Coeff (A × ℕ) →ₗ[ℂ] L1Coeff (A × ℕ) where
  toFun := lowCut d
  map_add' := lowCut_add d
  map_smul' := lowCut_smul d

/-- Low cutoff as a contraction. -/
def lowCutCLM (d : ℕ) : L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  (lowCutLinear d).mkContinuous 1 (by
    intro f
    change ‖lowCut d f‖ ≤ 1 * ‖f‖
    simpa using norm_lowCut_le (A := A) d f)

end DistinguishedShift

section Evaluation

variable {S : Type*}

/-- A multivariate monomial indexed by a finitely-supported exponent vector. -/
def monomial (y : S → ℂ) (a : S →₀ ℕ) : ℂ :=
  a.prod fun i n ↦ y i ^ n

/--
@isnad1 id=eq.0h2v.s5.3ad50554d874 from=translated src=- shape=4b63daf7 vocab=33606e5b
-/
@[simp]
lemma monomial_zero (y : S → ℂ) : monomial y 0 = 1 := by simp [monomial]

/-- Multiplicative real polyradius weight. -/
def monomialWeight (r : S → ℝ) (a : S →₀ ℕ) : ℝ :=
  a.prod fun i n ↦ r i ^ n

/-- Evaluate an `ℓ¹` coefficient family on the unit polydisc. -/
def evalL1 (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ) : ℂ :=
  ∑' a, f a * monomial y a

end Evaluation

end ClassicalComplexWPT
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
