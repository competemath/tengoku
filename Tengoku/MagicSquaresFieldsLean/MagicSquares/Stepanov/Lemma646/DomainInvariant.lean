import Tengoku.Seed.Algebra.Polynomial.Expand
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Lemma 6.46 over an integral-domain coefficient ring

The original `Lemma646.Invariant` was written over a field.  In the actual
LN97 proof the symmetric orbit product has coefficients in `F_q[X]`, which is
an integral domain but not a field.  These are the same invariant/contraction
lemmas at exactly the generality needed for that bivariate step.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

/--
@isnad1 id=eq.3h5v.s7.5620482a1fbb from=translated src=- shape=1a9f7516 vocab=c79595b3
-/
theorem coeff_eq_zero_of_primitiveRoot_scale_invariant_domain
    {m n : ℕ} {zeta : R} {B : Polynomial R}
    (hzeta : IsPrimitiveRoot zeta m)
    (hinv : B.comp (C zeta * X) = B)
    (hndvd : ¬ m ∣ n) :
    B.coeff n = 0 := by
  have hc := congrArg (fun P : Polynomial R => P.coeff n) hinv
  simp only [Polynomial.comp_C_mul_X_coeff] at hc
  have hpow : zeta ^ n ≠ 1 := by
    intro h
    exact hndvd (hzeta.dvd_of_pow_eq_one n h)
  by_contra hcoeff
  have hzpow : zeta ^ n = 1 := by
    apply mul_left_cancel₀ hcoeff
    simpa using hc
  exact hpow hzpow

/--
@isnad1 id=eq.3h4v.s8.8d3d6aaa6ffb from=translated src=- shape=1e21cdc4 vocab=10c7c3f0
-/
theorem expand_contract_eq_of_primitiveRoot_scale_invariant_domain
    {m : ℕ} {zeta : R} {B : Polynomial R}
    (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m)
    (hinv : B.comp (C zeta * X) = B) :
    (Polynomial.expand R m) (Polynomial.contract m B) = B := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_expand hm]
  by_cases hdvd : m ∣ n
  · rw [ite_eq_left hdvd]
    rw [Polynomial.coeff_contract (Nat.ne_of_gt hm)]
    rw [Nat.div_mul_cancel hdvd]
  · rw [ite_eq_right hdvd]
    have hz :=
      coeff_eq_zero_of_primitiveRoot_scale_invariant_domain
        (R := R) hzeta hinv hdvd
    simpa using hz.symm

/--
@isnad1 id=ex.3h4v.s8.efb08eac552c from=translated src=- shape=61652b8f vocab=5b90a7f8
-/
theorem exists_comp_X_pow_of_primitiveRoot_scale_invariant_domain
    {m : ℕ} {zeta : R} {B : Polynomial R}
    (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m)
    (hinv : B.comp (C zeta * X) = B) :
    ∃ G : Polynomial R, B = G.comp (X ^ m) := by
  refine ⟨Polynomial.contract m B, ?_⟩
  have h :=
    expand_contract_eq_of_primitiveRoot_scale_invariant_domain
      (R := R) hm hzeta hinv
  rw [Polynomial.expand_eq_comp_X_pow] at h
  exact h.symm

/--
@isnad1 id=eq.3h4v.s7.815adc3a669b from=translated src=- shape=0fdefb72 vocab=ce78b72b
-/
theorem natDegree_contract_mul_eq_of_primitiveRoot_scale_invariant_domain
    {m : ℕ} {zeta : R} {B : Polynomial R}
    (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m)
    (hinv : B.comp (C zeta * X) = B) :
    (Polynomial.contract m B).natDegree * m = B.natDegree := by
  have h :=
    congrArg Polynomial.natDegree
      (expand_contract_eq_of_primitiveRoot_scale_invariant_domain
        (R := R) hm hzeta hinv)
  simpa [Polynomial.natDegree_expand] using h

end LN97
end MagicSquares
