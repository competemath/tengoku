import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

variable (W : Type*) [CommRing W]

abbrev CrossingQuotient (t : W) : Type _ :=
  MvPolynomial (Fin 2) W ⧸ Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}

variable {W}

namespace CrossingQuotient

variable (t : W)

abbrev mk : MvPolynomial (Fin 2) W →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.mkₐ W (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)})

/--
@isnad1 id=eq.0h3v.s12.492ef9f5d20e from=translated src=- shape=c970a963 vocab=59f4e912
-/
theorem mk_apply (p : MvPolynomial (Fin 2) W) :
    mk t p = Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) p := rfl

/--
@isnad1 id=surjecti.0h2v.s11.75b7a646795a from=translated src=- shape=6656100e vocab=c5153993
-/
theorem mk_surjective : Function.Surjective (mk t) := Ideal.Quotient.mkₐ_surjective W _

/--
@isnad1 id=eq.0h2v.s12.6a3311d4dc46 from=translated src=- shape=02164397 vocab=911d00c7
-/
theorem mk_X_mul_mk_X : mk t (X 0) * mk t (X 1) = algebraMap W (CrossingQuotient W t) t := by
  rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

def monomial (n : ℤ) : CrossingQuotient W t :=
  if 0 ≤ n then mk t (X 0) ^ n.toNat else mk t (X 1) ^ (-n).toNat

/--
@isnad1 id=eq.1h3v.s11.cb3994527b67 from=translated src=- shape=f5ddf90a vocab=c376822b
-/
theorem monomial_of_nonneg {n : ℤ} (h : 0 ≤ n) : monomial t n = mk t (X 0) ^ n.toNat := ite_eq_left h

/--
@isnad1 id=eq.1h3v.s11.8d316f2db643 from=translated src=- shape=051e5658 vocab=086040e9
-/
theorem monomial_of_neg {n : ℤ} (h : n < 0) : monomial t n = mk t (X 1) ^ (-n).toNat := ite_eq_right (not_le.mpr h)

/--
@isnad1 id=eq.0h3v.s11.136220cb726a from=translated src=- shape=7b92cb7f vocab=99db0e32
-/
@[simp] theorem monomial_natCast (n : ℕ) : monomial t (n : ℤ) = mk t (X 0) ^ n := by
  rw [monomial_of_nonneg t (Int.natCast_nonneg n), Int.toNat_natCast]

/--
@isnad1 id=eq.0h3v.s11.042c181472b5 from=translated src=- shape=f615a096 vocab=5009368f
-/
@[simp] theorem monomial_neg_natCast (n : ℕ) : monomial t (-(n : ℤ)) = mk t (X 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, neg_zero, monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero, pow_zero]
  · rw [monomial_of_neg t (by omega), neg_neg, Int.toNat_natCast]

/--
@isnad1 id=eq.0h2v.s9.08cabba96a19 from=translated src=- shape=4e86086a vocab=99fe267e
-/
@[simp] theorem monomial_zero : monomial t 0 = 1 := by
  rw [monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero]

def powMap (e : ℕ) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C (t ^ e) : MvPolynomial (Fin 2) W)})
    (aeval fun i : Fin 2 => mk t (X i) ^ e) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, map_sub, map_mul, aeval_X, aeval_X, aeval_C, ← mul_pow, mk_X_mul_mk_X, ← map_pow, sub_self,
        mul_zero])

/--
@isnad1 id=eq.0h4v.s13.aa7200d48d76 from=translated src=- shape=1f3fbe1c vocab=751f4429
-/
theorem powMap_mk (e : ℕ) (p : MvPolynomial (Fin 2) W) :
    powMap t e (mk (t ^ e) p) = aeval (fun i : Fin 2 => mk t (X i) ^ e) p := rfl

/--
@isnad1 id=eq.0h4v.s13.8478bb73bbde from=translated src=- shape=756f052b vocab=d4d04607
-/
@[simp] theorem powMap_mk_X (e : ℕ) (i : Fin 2) : powMap t e (mk (t ^ e) (X i)) = mk t (X i) ^ e := by
  rw [powMap_mk, aeval_X]

end CrossingQuotient

end MvPolynomial

end
