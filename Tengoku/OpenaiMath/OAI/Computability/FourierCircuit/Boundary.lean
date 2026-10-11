import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.FFTCircuit

namespace OAI

section
namespace ExactFourier.Boundary
open Polynomial
open scoped BigOperators

noncomputable def quotientLinear (ℓ : ℂ[X]) (hℓ : ℓ.Monic) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun f := f /ₘ ℓ
  map_add' f g := by
    apply (div_modByMonic_unique (f /ₘ ℓ + g /ₘ ℓ)
      (f %ₘ ℓ + g %ₘ ℓ) hℓ ?_).1
    constructor
    · rw [mul_add]
      linear_combination modByMonic_add_div f ℓ + modByMonic_add_div g ℓ
    · exact lt_of_le_of_lt (degree_add_le _ _) (max_lt
        (degree_modByMonic_lt _ hℓ) (degree_modByMonic_lt _ hℓ))
  map_smul' c f := by
    apply (div_modByMonic_unique (c • (f /ₘ ℓ)) (c • (f %ₘ ℓ)) hℓ ?_).1
    constructor
    · rw [mul_smul_comm, ← smul_add, modByMonic_add_div]
    · exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hℓ)

@[simp] theorem quotientLinear_apply (ℓ : ℂ[X]) (hℓ : ℓ.Monic) (f : ℂ[X]) :
    quotientLinear ℓ hℓ f = f /ₘ ℓ := rfl

/-- Inputs strictly before the final d times do not cross the coefficient boundary. -/
theorem prefix_quotient_zero (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d t b : ℕ} (ht : ℓ.natDegree = t) (hf : f.natDegree ≤ d) (hb : b + d < t) :
    (f * X ^ b) /ₘ ℓ = 0 := by
  apply (divByMonic_eq_zero_iff hℓ).mpr
  rw [degree_eq_natDegree hℓ.ne_zero, ht]
  apply (degree_le_natDegree).trans_lt
  exact_mod_cast (calc
    (f * X ^ b).natDegree ≤ f.natDegree + (X ^ b : ℂ[X]).natDegree := natDegree_mul_le
    _ ≤ d + b := by simpa using Nat.add_le_add_right hf b
    _ < t := by omega)

/-- The quotient, with sign reversed, has strictly fewer than d coefficients. -/
theorem quotient_degree_lt (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d t b : ℕ} (ht : ℓ.natDegree = t) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hb : b < t) :
    ((f * X ^ b) /ₘ ℓ).natDegree < d := by
  rw [natDegree_divByMonic _ hℓ, ht]
  have h : (f * X ^ b).natDegree ≤ d + b := by
    exact natDegree_mul_le.trans (by simpa using Nat.add_le_add_right hf b)
  omega

/-- Exact division of a shifted matrix entry. This keeps the generator coefficients
on the left, ready for the ordered J_i*G_j matrix formula. -/
theorem quotient_shift_expansion (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d : ℕ} (hf : f.natDegree ≤ d) (b : ℕ) :
    (f * X ^ b) /ₘ ℓ =
      ∑ j ∈ Finset.range (d + 1), f.coeff j • ((X ^ (b + j) : ℂ[X]) /ₘ ℓ) := by
  have hF : f * X ^ b =
      ∑ j ∈ Finset.range (d + 1), f.coeff j • (X ^ (b + j) : ℂ[X]) := by
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := d+1) (by omega)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_eq_C_mul, mul_assoc, ← pow_add, Nat.add_comm j b]
  change quotientLinear ℓ hℓ (f * X ^ b) = _
  rw [hF, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp

/-- Entrywise modulus reduction differs from time truncation by minus the modulus
 times precisely the quotient above. No bounds on coefficients are imposed. -/
theorem boundary_difference (ℓ f : ℂ[X]) (b : ℕ) :
    (f * X ^ b) %ₘ ℓ - f * X ^ b = -ℓ * ((f * X ^ b) /ₘ ℓ) := by
  rw [modByMonic_eq_sub_mul_div]
  ring

noncomputable def timeMatrix {ι : Type} (t : ℕ) (G : Matrix ι ι ℂ[X]) :
    Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  fun a b => (G a.2 b.2 * X ^ b.1.val).coeff a.1.val

noncomputable def modulusMatrix {ι : Type} (t : ℕ) (ℓ : ℂ[X])
    (G : Matrix ι ι ℂ[X]) : Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  fun a b => ((G a.2 b.2 * X ^ b.1.val) %ₘ ℓ).coeff a.1.val

/-- Scalar weights for the exact ordered generator formula. Prefix correction uses
η=1. The suffix uses the first t coefficients of ℓ/u^k. -/
noncomputable def orderedWeight (η ℓ : ℂ[X]) (a b i j : ℕ) : ℂ :=
  -(η * X ^ i * ((X ^ (b + j) : ℂ[X]) /ₘ ℓ)).coeff a

theorem polynomial_ordered_expansion (η ℓ f g : ℂ[X]) (hℓ : ℓ.Monic)
    {d e : ℕ} (hg : g.natDegree ≤ d) (hf : f.natDegree ≤ e) (b : ℕ) :
    η * f * (-((g * X ^ b) /ₘ ℓ)) =
      ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (d+1),
        (f.coeff i * g.coeff j) • (-(η * X ^ i * ((X ^ (b+j) : ℂ[X]) /ₘ ℓ))) := by
  rw [quotient_shift_expansion ℓ g hℓ hg]
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := e+1) (by omega)]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib,
    mul_neg, smul_eq_C_mul]
  apply congrArg Neg.neg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring

noncomputable def coefficientMatrix {ι κ : Type} (G : Matrix ι κ ℂ[X]) (j : ℕ) :
    Matrix ι κ ℂ := fun u v => (G u v).coeff j

/-- Polynomial correction for a single input time b, before taking its output
coefficient. Matrix multiplication is in the original order J then G. -/
noncomputable def weightedCorrection {ι : Type} [Fintype ι] (η ℓ : ℂ[X])
    (J G : Matrix ι ι ℂ[X]) (b : ℕ) : Matrix ι ι ℂ[X] :=
  fun u v => ∑ x, η * J u x * (-((G x v * X ^ b) /ₘ ℓ))

/-- Exact ordered-span part of the coefficient-boundary comparison. There is no
commutation hypothesis on any pair of spatial coefficient matrices. -/
theorem ordered_span {ι : Type} [Fintype ι] (η ℓ : ℂ[X]) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι ℂ[X]) {d e : ℕ}
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e) (a b : ℕ) :
    coefficientMatrix (weightedCorrection η ℓ J G b) a =
      ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (d+1),
        orderedWeight η ℓ a b i j • (coefficientMatrix J i * coefficientMatrix G j) := by
  classical
  ext u v
  simp only [coefficientMatrix, weightedCorrection, finsetSum_coeff,
    polynomial_ordered_expansion η ℓ _ _ hℓ (hG _ _) (hJ _ _) b,
    coeff_smul, coeff_neg]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    coefficientMatrix, orderedWeight, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- No weighted correction has an input column before the suffix. -/
theorem weightedCorrection_prefix_zero {ι : Type} [Fintype ι]
    (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X]) {d t b : ℕ}
    (ht : ℓ.natDegree = t) (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hb : b+d < t) : weightedCorrection η ℓ J G b = 0 := by
  classical
  funext u v
  simp only [weightedCorrection, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [prefix_quotient_zero ℓ (G x v) hℓ ht (hG _ _) hb]
  simp

/-- The actual early--suffix formula after the scalar prefix conjugation. -/
noncomputable def activeCorrection {ι : Type} [Fintype ι]
    (t d : ℕ) (η ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X]) :
    Matrix (Fin t × ι) (Fin t × ι) ℂ := fun a b =>
  if a.1.val < t-d then
    (weightedCorrection 1 ℓ J G b.1.val a.2 b.2).coeff a.1.val
  else (weightedCorrection η ℓ J G b.1.val a.2 b.2).coeff a.1.val

def ActiveTime (t d e a : ℕ) : Prop := a < min (t-d) (e+d) ∨ t-d ≤ a

instance (t d e a : ℕ) : Decidable (ActiveTime t d e a) := by
  unfold ActiveTime
  infer_instance

/-- Simultaneous row/column permutation isolates every matrix correction supported
on a single active index set, with an exact identity on its complement. -/
theorem supported_identity_decomposition {κ : Type} [DecidableEq κ]
    (S : κ → Prop) [DecidablePred S] (L : Matrix κ κ ℂ)
    (hrow : ∀ i j, ¬S i → L i j = 0)
    (hcol : ∀ i j, ¬S j → L i j = 0) :
    (1 + L).submatrix (Equiv.sumCompl S) (Equiv.sumCompl S) =
      Matrix.fromBlocks (1 + L.submatrix Subtype.val Subtype.val)
        (0 : Matrix {i // S i} {i // ¬S i} ℂ) 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.submatrix, Matrix.one_apply, Subtype.ext_iff]
  · have hij : (i : κ) ≠ (j : κ) := by intro h; exact j.property (h ▸ i.property)
    simp [Matrix.submatrix, Matrix.one_apply, hcol _ _ j.property]
  · have hij : (i : κ) ≠ (j : κ) := by intro h; exact i.property (h.symm ▸ j.property)
    simp [Matrix.submatrix, Matrix.one_apply, hrow _ _ i.property]
  · simp [Matrix.submatrix, Matrix.one_apply, hrow _ _ i.property, Subtype.ext_iff]

end ExactFourier.Boundary

end

section
/-! Literal relation between modulus multiplication and the supported correction.
This is the missing interface at 06-feedback:86--196, not an assumed theorem.
Noncommutative coefficient matrices remain ordered J_i G_j. -/
namespace ExactFourier.Boundary
open Polynomial
open CoefficientTime
open scoped Kronecker BigOperators

noncomputable def seriesMatrix {ι : Type} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ[X] →+* Matrix ι ι (PowerSeries ℂ) :=
  (Polynomial.coeToPowerSeries.ringHom : ℂ[X] →+* PowerSeries ℂ).mapMatrix

@[simp] theorem seriesMatrix_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ[X]) (i j : ι) : seriesMatrix G i j = (G i j : PowerSeries ℂ) := rfl

noncomputable def quotientColumns {ι : Type} (t : ℕ) (ℓ : ℂ[X])
    (G : Matrix ι ι ℂ[X]) : Matrix ι (Fin t × ι) (PowerSeries ℂ) :=
  fun i b => (-((G i b.2 * X^b.1.val) /ₘ ℓ) : ℂ[X])

/-- A prefix-only scalar convolution cancels the denominator on early rows, and
literally leaves the late rows unchanged. -/
theorem prefix_scalar_cancels {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f η : PowerSeries ℂ) (hfη : f*η=1)
    (V : Matrix ι κ (PowerSeries ℂ)) (a : Fin t × ι) (b : κ) :
    ((prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) *
      coefficientColumns t (η • V)) a b =
        if a.1.val < T then PowerSeries.coeff a.1.val (V a.2 b)
        else PowerSeries.coeff a.1.val (η * V a.2 b) := by
  rw [prefix_mul_columns]
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hfη, one_mul]

end ExactFourier.Boundary

namespace ExactFourier.Boundary
open Polynomial CoefficientTime
open scoped Kronecker BigOperators

/-- Coefficients below t cannot see the discarded tail of a scalar series. -/
theorem coeff_trunc_mul_series (t : ℕ) (η V : PowerSeries ℂ) (a : Fin t) :
    PowerSeries.coeff a.val (((PowerSeries.trunc t η : ℂ[X]) : PowerSeries ℂ) * V) =
      PowerSeries.coeff a.val (η*V) := by
  rw [coeff_mul_truncated _ _ a, coeff_mul_truncated _ _ a]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hka : k.val ≤ a.val
  · have hat : a.val-k.val < t := by have := a.isLt; omega
    simp [hka, PowerSeries.coeff_trunc, hat]
  · simp [hka]

/-- Converting the finite polynomial ordered generator formula to series changes
neither matrix order nor the sign of the quotient. -/
theorem weightedCorrection_series {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (η ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X])
    (i : ι) (b : Fin t × ι) :
    (((weightedCorrection η ℓ J G b.1.val) i b.2 : ℂ[X]) : PowerSeries ℂ) =
      (η : PowerSeries ℂ) * (seriesMatrix J * quotientColumns t ℓ G) i b := by
  simp only [weightedCorrection, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul,
    Matrix.mul_apply, seriesMatrix_apply, quotientColumns, Finset.mul_sum, mul_assoc]

/-- Quotient columns vanish on the whole coefficient prefix, not merely on an
assumed active direct summand. -/
theorem quotientColumns_prefix_zero {ι : Type} (t d : ℕ) (ℓ : ℂ[X])
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (G : Matrix ι ι ℂ[X])
    (hG : ∀ i j, (G i j).natDegree ≤ d) (i : ι) (b : Fin t × ι)
    (hb : b.1.val < t-d) : quotientColumns t ℓ G i b = 0 := by
  have hb' : b.1.val+d<t := by omega
  simp only [quotientColumns, prefix_quotient_zero ℓ _ hℓ ht (hG _ _) hb',
    neg_zero, Polynomial.coe_zero]

end ExactFourier.Boundary

namespace ExactFourier.Boundary
open Polynomial CoefficientTime
open scoped Kronecker BigOperators

end ExactFourier.Boundary

end

end OAI
