import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvPolynomial_CrossingResolution
import Tengoku.FltAnthropic.Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

open scoped Polynomial LaurentPolynomial

namespace NZDKIT

universe u

variable {W : Type u} [CommRing W] (t : W)

noncomputable def gen₁ : Fin 2 → W[T;T⁻¹] :=
  ![LaurentPolynomial.T 1, LaurentPolynomial.C t * LaurentPolynomial.T (-1)]

noncomputable def gen₂ : Fin 2 → W[T;T⁻¹] :=
  ![LaurentPolynomial.C t * LaurentPolynomial.T 1, LaurentPolynomial.T (-1)]

/--
@isnad1 id=eq.0h2v.s5.55d6d0795beb from=translated src=- shape=038754d1 vocab=0f2485fb
-/
theorem gen₁_zero : gen₁ t 0 = LaurentPolynomial.T 1 := rfl
/--
@isnad1 id=eq.0h2v.s7.f622fad8e31e from=translated src=- shape=0e85391b vocab=42ae8dd8
-/
theorem gen₁_one : gen₁ t 1 = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := rfl
/--
@isnad1 id=eq.0h2v.s7.4feef63e6875 from=translated src=- shape=a9942fb3 vocab=fccd1947
-/
theorem gen₂_zero : gen₂ t 0 = LaurentPolynomial.C t * LaurentPolynomial.T 1 := rfl
/--
@isnad1 id=eq.0h2v.s5.6a310dec844e from=translated src=- shape=c6dbfefe vocab=0983201e
-/
theorem gen₂_one : gen₂ t 1 = LaurentPolynomial.T (-1) := rfl

/--
@isnad1 id=eq.0h1v.s6.a805304883ad from=translated src=- shape=f9f54c7c vocab=121b4101
-/
theorem T_one_mul_T_neg_one :
    (LaurentPolynomial.T 1 : W[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; rfl

/--
@isnad1 id=eq.0h2v.s8.0d8402036fb6 from=translated src=- shape=11207a91 vocab=4c3bddbb
-/
theorem rel₁ : (LaurentPolynomial.T 1 : W[T;T⁻¹]) * (LaurentPolynomial.C t * LaurentPolynomial.T (-1))
    = LaurentPolynomial.C t := by
  rw [mul_left_comm, T_one_mul_T_neg_one, mul_one]

/--
@isnad1 id=eq.0h2v.s8.51fe081c705b from=translated src=- shape=79a4902a vocab=4c3bddbb
-/
theorem rel₂ : (LaurentPolynomial.C t * LaurentPolynomial.T 1 : W[T;T⁻¹]) * LaurentPolynomial.T (-1)
    = LaurentPolynomial.C t := by
  rw [mul_assoc, T_one_mul_T_neg_one, mul_one]

/--
@isnad1 id=eq.0h2v.s9.46f3c23b864f from=translated src=- shape=a90764a9 vocab=87e40d3a
-/
theorem aeval_gen₁_rel : aeval (gen₁ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₁_zero, gen₁_one, rel₁,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

/--
@isnad1 id=eq.0h2v.s9.3e39f26ca31d from=translated src=- shape=a90764a9 vocab=87671aa6
-/
theorem aeval_gen₂_rel : aeval (gen₂ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₂_zero, gen₂_one, rel₂,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

noncomputable def φ₁ : CrossingQuotient W t →ₐ[W] W[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (gen₁ t)) (fun p hp => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, aeval_gen₁_rel, mul_zero])

noncomputable def φ₂ : CrossingQuotient W t →ₐ[W] W[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (gen₂ t)) (fun p hp => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, aeval_gen₂_rel, mul_zero])

/--
@isnad1 id=eq.0h3v.s12.9f9304467c66 from=translated src=- shape=3bc79ae7 vocab=c7fd9015
-/
theorem φ₁_mk (p : MvPolynomial (Fin 2) W) : φ₁ t (mk t p) = aeval (gen₁ t) p := rfl

/--
@isnad1 id=eq.0h3v.s11.5b5fde1864af from=translated src=- shape=de132f78 vocab=8a766459
-/
theorem φ₁_monomial (n : ℤ) :
    φ₁ t (monomial t n) = LaurentPolynomial.C (t ^ (-n).toNat) * LaurentPolynomial.T n := by
  rcases le_or_gt 0 n with h | h
  · rw [monomial_of_nonneg t h, map_pow, φ₁_mk, aeval_X, gen₁_zero, LaurentPolynomial.T_pow,
      mul_one, Int.toNat_of_nonneg h, Int.toNat_of_nonpos (neg_nonpos.mpr h), pow_zero, map_one,
      one_mul]
  · rw [monomial_of_neg t h, map_pow, φ₁_mk, aeval_X, gen₁_one, mul_pow, ← map_pow,
      LaurentPolynomial.T_pow, mul_neg_one, Int.toNat_of_nonneg (by omega : 0 ≤ -n), neg_neg]

/--
@isnad1 id=eq.0h3v.s11.bc910a34ccbf from=translated src=- shape=7e626c56 vocab=1588b22b
-/
theorem φ₁_repr (c : ℤ →₀ W) :
    φ₁ t (c.sum fun n r => r • monomial t n)
      = c.sum fun n r => AddMonoidAlgebra.single n (r * t ^ (-n).toNat) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [map_smul, φ₁_monomial, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    LaurentPolynomial.single_eq_C_mul_T]

/--
@isnad1 id=eq.0h4v.s11.4bf73f77853b from=translated src=- shape=c142a1ba vocab=e333c175
-/
theorem coeff_φ₁_repr (c : ℤ →₀ W) (m : ℤ) :
    (φ₁ t (c.sum fun n r => r • monomial t n)).coeff m = c m * t ^ (-m).toNat := by
  rw [φ₁_repr, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_single]
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m]
  · rw [Finsupp.single_eq_same]
  · intro n _ hn
    rw [Finsupp.single_apply, ite_eq_right hn]
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm, zero_mul, Finsupp.single_zero, Finsupp.zero_apply]

/--
@isnad1 id=ex.0h3v.s10.d5c14b6f3535 from=translated src=- shape=8417c014 vocab=66238530
-/
theorem exists_repr (a : CrossingQuotient W t) :
    ∃ c : ℤ →₀ W, (c.sum fun n r => r • monomial t n) = a := by
  have h := (MvPolynomial.CrossingQuotient.linearIndependent_monomial_and_span_eq_top t).2
  have ha : a ∈ Submodule.span W (Set.range (monomial t)) := by rw [h]; trivial
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp ha

/--
@isnad1 id=injectiv.1h2v.s11.135fd9d5225d from=translated src=- shape=899546bb vocab=c8e41031
-/
theorem φ₁_injective_of_mem (ht : t ∈ nonZeroDivisors W) : Function.Injective (φ₁ t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨c, rfl⟩ := exists_repr t a
  suffices hc : c = 0 by rw [hc, Finsupp.sum_zero_index]
  ext m
  have hm := coeff_φ₁_repr t c m
  rw [ha] at hm
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hm
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ht _)).mp hm.symm

/--
@isnad1 id=mem.2h4v.s7.923f9d49045c from=translated src=- shape=26c18212 vocab=925aa445
-/
theorem mem_nonZeroDivisors_of_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (ha : f a ∈ nonZeroDivisors B) : a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  apply hf
  rw [map_zero]
  exact (mem_nonZeroDivisors_iff_right.mp ha) (f b) (by rw [← map_mul, hb, map_zero])

/--
@isnad1 id=mem.1h3v.s8.6bb3fdcf52ac from=translated src=- shape=ff17db93 vocab=d72b7bb3
-/
theorem C_mul_T_mem (ht : t ∈ nonZeroDivisors W) (n : ℤ) :
    (LaurentPolynomial.C t * LaurentPolynomial.T n : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  refine mul_mem ?_ (LaurentPolynomial.isUnit_T n).mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro f hf

  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro m
  have := AddMonoidAlgebra.coeff_mul_single_zero f t m
  rw [LaurentPolynomial.single_eq_C] at this
  change (f * LaurentPolynomial.C t : W[T;T⁻¹]).coeff m = f.coeff m * t at this
  rw [hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  exact ((mul_right_mem_nonZeroDivisors_eq_zero_iff ht).mp this.symm)

/--
@isnad1 id=eq.0h2v.s11.2288b52bb3b8 from=translated src=- shape=0320185a vocab=11f00c93
-/
theorem φ₁_U : φ₁ t (U t) = LaurentPolynomial.T 1 := by
  rw [show U t = mk t (X 0) from rfl, φ₁_mk, aeval_X, gen₁_zero]

/--
@isnad1 id=eq.0h2v.s11.02c499eb8fb9 from=translated src=- shape=4beeb3f7 vocab=54be9932
-/
theorem φ₁_V : φ₁ t (V t) = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := by
  rw [show V t = mk t (X 1) from rfl, φ₁_mk, aeval_X, gen₁_one]

/--
@isnad1 id=and.1h2v.s11.b3a1037d3d96 from=translated src=- shape=68517a41 vocab=96cfce88
-/
theorem N1 (ht : t ∈ nonZeroDivisors W) :
    U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧ V t ∈ nonZeroDivisors (CrossingQuotient W t) := by
  refine ⟨mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_,
    mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_⟩
  · change φ₁ t (U t) ∈ _
    rw [φ₁_U]
    exact (LaurentPolynomial.isUnit_T 1).mem_nonZeroDivisors
  · change φ₁ t (V t) ∈ _
    rw [φ₁_V]
    exact C_mul_T_mem t ht (-1)

end NZDKIT

/--
@isnad1 id=and.1h2v.s11.b3a1037d3d96 from=translated src=- shape=68517a41 vocab=96cfce88
-/
theorem solution
    {W : Type*} [CommRing W] (t : W) (ht : t ∈ nonZeroDivisors W) :
    U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧ V t ∈ nonZeroDivisors (CrossingQuotient W t) :=
  NZDKIT.N1 t ht
