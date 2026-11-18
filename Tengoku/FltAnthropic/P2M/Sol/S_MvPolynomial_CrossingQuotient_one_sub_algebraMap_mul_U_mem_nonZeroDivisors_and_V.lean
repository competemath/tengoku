import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvPolynomial_CrossingResolution
import Tengoku.FltAnthropic.Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_CrossingQuotient_one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_CrossingQuotient_one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V

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
@isnad1 id=eq.0h2v.s5.8f470b508714 from=translated src=- shape=038754d1 vocab=c6f88331
-/
theorem gen₁_zero : gen₁ t 0 = LaurentPolynomial.T 1 := rfl
/--
@isnad1 id=eq.0h2v.s7.ff22554b9f92 from=translated src=- shape=0e85391b vocab=07761493
-/
theorem gen₁_one : gen₁ t 1 = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := rfl
/--
@isnad1 id=eq.0h2v.s7.de75b037333b from=translated src=- shape=a9942fb3 vocab=d9b292a6
-/
theorem gen₂_zero : gen₂ t 0 = LaurentPolynomial.C t * LaurentPolynomial.T 1 := rfl
/--
@isnad1 id=eq.0h2v.s5.e12ec8ab08e2 from=translated src=- shape=c6dbfefe vocab=d0bb0a83
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
@isnad1 id=eq.0h2v.s9.ea9f71932c13 from=translated src=- shape=a90764a9 vocab=fce5b5db
-/
theorem aeval_gen₁_rel : aeval (gen₁ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₁_zero, gen₁_one, rel₁,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

/--
@isnad1 id=eq.0h2v.s9.180c946cf031 from=translated src=- shape=a90764a9 vocab=2a3f7af7
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
@isnad1 id=eq.0h3v.s12.c9fa3419b91c from=translated src=- shape=3bc79ae7 vocab=676e3bb6
-/
theorem φ₁_mk (p : MvPolynomial (Fin 2) W) : φ₁ t (mk t p) = aeval (gen₁ t) p := rfl

/--
@isnad1 id=eq.0h3v.s11.92c330f5844c from=translated src=- shape=de132f78 vocab=61551b4a
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
@isnad1 id=eq.0h3v.s11.e06911e9f2a2 from=translated src=- shape=7e626c56 vocab=6f2f5fef
-/
theorem φ₁_repr (c : ℤ →₀ W) :
    φ₁ t (c.sum fun n r => r • monomial t n)
      = c.sum fun n r => AddMonoidAlgebra.single n (r * t ^ (-n).toNat) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [map_smul, φ₁_monomial, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    LaurentPolynomial.single_eq_C_mul_T]

/--
@isnad1 id=eq.0h4v.s11.0fd60a0a420b from=translated src=- shape=c142a1ba vocab=490e3736
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
@isnad1 id=injectiv.1h2v.s11.e7572f5d716d from=translated src=- shape=899546bb vocab=2ad3a919
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
@isnad1 id=mem.1h4v.s8.d79f97ede673 from=translated src=- shape=8f719aba vocab=b73e7fe4
-/
theorem mem_nonZeroDivisors_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {a : A} (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  have : e.symm b * a = 0 := by
    apply e.injective
    rw [map_mul, e.apply_symm_apply, map_zero, hb]
  have h2 := (mem_nonZeroDivisors_iff_right.mp ha) _ this
  simpa using congrArg e h2

/--
@isnad1 id=mem.0h2v.s8.77609b72e5e9 from=translated src=- shape=f9ad7e0c vocab=af878bfe
-/
theorem T_one_sub_C_mem (a : W) :
    (LaurentPolynomial.T 1 - LaurentPolynomial.C a : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  nontriviality W
  have hmon : (Polynomial.X - Polynomial.C a : W[X]).Monic := Polynomial.monic_X_sub_C a
  have h1 : (Polynomial.X - Polynomial.C a : W[X]) ∈ nonZeroDivisors W[X] := hmon.mem_nonZeroDivisors
  have h2 := IsLocalization.nonZeroDivisors_le_comap (M := .powers (Polynomial.X : W[X]))
    (S := W[T;T⁻¹]) h1
  rw [Submonoid.mem_comap, LaurentPolynomial.algebraMap_eq_toLaurent, map_sub, Polynomial.toLaurent_X,
    Polynomial.toLaurent_C] at h2
  exact h2

/--
@isnad1 id=mem.0h2v.s8.7fd7ec5a25b3 from=translated src=- shape=5e2b8ecb vocab=5634b88f
-/
theorem one_sub_C_mul_T_neg_one_mem (a : W) :
    (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1) : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  have h : (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1) : W[T;T⁻¹])
      = LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 - LaurentPolynomial.C a) := by
    rw [mul_sub, ← LaurentPolynomial.T_add, mul_comm]
    rfl
  rw [h]
  exact mul_mem (LaurentPolynomial.isUnit_T (-1)).mem_nonZeroDivisors (T_one_sub_C_mem a)

/--
@isnad1 id=mem.0h2v.s8.acf33db41b2c from=translated src=- shape=c8945414 vocab=f4711199
-/
theorem one_sub_C_mul_T_one_mem (a : W) :
    (1 - LaurentPolynomial.C a * LaurentPolynomial.T 1 : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  have h := mem_nonZeroDivisors_of_ringEquiv (LaurentPolynomial.invert (R := W)).toRingEquiv
    (one_sub_C_mul_T_neg_one_mem a)
  have h2 : (LaurentPolynomial.invert (R := W)).toRingEquiv
      (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1)) = 1 - LaurentPolynomial.C a * LaurentPolynomial.T 1 := by
    change LaurentPolynomial.invert (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1)) = _
    rw [map_sub, map_one, map_mul, LaurentPolynomial.invert_T, neg_neg, LaurentPolynomial.invert_C]
  rwa [h2] at h

/--
@isnad1 id=eq.0h2v.s11.3a5c15b15860 from=translated src=- shape=0320185a vocab=3685a2b1
-/
theorem φ₁_U : φ₁ t (U t) = LaurentPolynomial.T 1 := by
  rw [show U t = mk t (X 0) from rfl, φ₁_mk, aeval_X, gen₁_zero]

/--
@isnad1 id=eq.0h2v.s11.e2197c29a589 from=translated src=- shape=4beeb3f7 vocab=73a0e8fb
-/
theorem φ₁_V : φ₁ t (V t) = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := by
  rw [show V t = mk t (X 1) from rfl, φ₁_mk, aeval_X, gen₁_one]

/--
@isnad1 id=and.1h3v.s13.6448b65397e7 from=translated src=- shape=fc270918 vocab=2200d052
-/
theorem N2 (ht : t ∈ nonZeroDivisors W) (w : W) :
    1 - algebraMap W (CrossingQuotient W t) w * U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧
      1 - algebraMap W (CrossingQuotient W t) w * V t ∈ nonZeroDivisors (CrossingQuotient W t) := by
  refine ⟨mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_,
    mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_⟩
  · change φ₁ t (1 - algebraMap W (CrossingQuotient W t) w * U t) ∈ _
    rw [map_sub, map_one, map_mul, AlgHom.commutes, φ₁_U, ← LaurentPolynomial.C_eq_algebraMap]
    exact one_sub_C_mul_T_one_mem w
  · change φ₁ t (1 - algebraMap W (CrossingQuotient W t) w * V t) ∈ _
    rw [map_sub, map_one, map_mul, AlgHom.commutes, φ₁_V, ← LaurentPolynomial.C_eq_algebraMap,
      ← mul_assoc, ← map_mul]
    exact one_sub_C_mul_T_neg_one_mem (w * t)

end NZDKIT

/--
@isnad1 id=and.1h3v.s13.6448b65397e7 from=translated src=- shape=fc270918 vocab=2200d052
-/
theorem solution
    {W : Type*} [CommRing W] (t : W) (ht : t ∈ nonZeroDivisors W) (w : W) :
    1 - algebraMap W (CrossingQuotient W t) w * U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧
      1 - algebraMap W (CrossingQuotient W t) w * V t ∈ nonZeroDivisors (CrossingQuotient W t) :=
  NZDKIT.N2 t ht w
