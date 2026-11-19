import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.RootDegree
import Tengoku.Seed.Algebra.Polynomial.Expand
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# The root-of-unity invariant step in LN97 Lemma 6.46

On p. 302, LN97 forms a symmetric product and concludes that, after
specializing the variables to the `m`th roots of unity times `Y`, the
result is a polynomial in `Y^m`.

For the Lean formalization we use the equivalent and more economical
criterion:

* if `ζ` is a primitive `m`th root of unity, and
* `B(ζ Y) = B(Y)`,

then every nonzero coefficient of `B` has exponent divisible by `m`.
Consequently `B` is the `m`-fold expansion of its contraction, i.e.

    B(Y) = G(Y^m)

for `G = contract m B`.

Mathlib's `Polynomial.expand` is exactly composition with `X^m`, and
`Polynomial.contract` is the corresponding coefficient-compression
operation.
-/

/-- If a polynomial is invariant under scaling its variable by a
primitive `m`th root of unity, every coefficient in a degree not
divisible by `m` is zero.
@isnad1 id=eq.3h5v.s7.84c50bb11c6a from=translated src=- shape=47768e61 vocab=1e89b7ac
-/
theorem coeff_eq_zero_of_primitiveRoot_scale_invariant
    {m n : ℕ} {ζ : F} {B : Polynomial F}
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : B.comp (C ζ * X) = B)
    (hndvd : ¬ m ∣ n) :
    B.coeff n = 0 := by
  have hc := congrArg (fun P : Polynomial F => P.coeff n) hinv
  simp only [Polynomial.comp_C_mul_X_coeff] at hc
  have hpow : ζ ^ n ≠ 1 := by
    intro h
    exact hndvd (hζ.dvd_of_pow_eq_one n h)
  by_contra hcoeff
  have hzpow : ζ ^ n = 1 := by
    apply mul_left_cancel₀ hcoeff
    simpa using hc
  exact hpow hzpow

/-- The support formulation of the preceding lemma.
@isnad1 id=dvd.3h5v.s7.fb0e3ec35a73 from=translated src=- shape=7caade5b vocab=d0432dc7
-/
theorem support_dvd_of_primitiveRoot_scale_invariant
    {m : ℕ} {ζ : F} {B : Polynomial F}
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : B.comp (C ζ * X) = B) :
    ∀ n ∈ B.support, m ∣ n := by
  intro n hn
  by_contra hndvd
  have hz :=
    coeff_eq_zero_of_primitiveRoot_scale_invariant
      (F := F) hζ hinv hndvd
  exact (Polynomial.mem_support_iff.mp hn) hz

/-- A primitive-root invariant polynomial is a polynomial in `X^m`.

More precisely, if `m > 0`, then

    expand F m (contract m B) = B.

Since `expand F m G = G.comp (X^m)`, this is exactly the statement that
there exists `G` with `B(X) = G(X^m)`.
@isnad1 id=eq.3h4v.s8.27949ef7b8c3 from=translated src=- shape=27f67201 vocab=33809d22
-/
theorem expand_contract_eq_of_primitiveRoot_scale_invariant
    {m : ℕ} {ζ : F} {B : Polynomial F}
    (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : B.comp (C ζ * X) = B) :
    (Polynomial.expand F m) (Polynomial.contract m B) = B := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_expand hm]
  by_cases hdvd : m ∣ n
  · rw [ite_eq_left hdvd]
    rw [Polynomial.coeff_contract (Nat.ne_of_gt hm)]
    have hcancel : n / m * m = n := Nat.div_mul_cancel hdvd
    rw [hcancel]
  · rw [ite_eq_right hdvd]
    have hz :=
      coeff_eq_zero_of_primitiveRoot_scale_invariant
        (F := F) hζ hinv hdvd
    simpa using hz.symm

/-- The explicit existence form matching the sentence in LN97:
`B` can be expressed as a polynomial in `Y^m`.
@isnad1 id=ex.3h4v.s8.7a2afd5dc2c3 from=translated src=- shape=7b83d608 vocab=46b15508
-/
theorem exists_comp_X_pow_of_primitiveRoot_scale_invariant
    {m : ℕ} {ζ : F} {B : Polynomial F}
    (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : B.comp (C ζ * X) = B) :
    ∃ G : Polynomial F, B = G.comp (X ^ m) := by
  refine ⟨Polynomial.contract m B, ?_⟩
  have h :=
    expand_contract_eq_of_primitiveRoot_scale_invariant
      (F := F) hm hζ hinv
  rw [Polynomial.expand_eq_comp_X_pow] at h
  exact h.symm

/-- The contraction has exactly the expected degree scaling.

This will convert LN97's bound `deg B ≤ m(m-1)` into
`deg G ≤ m-1` once the orbit product `B` has been constructed.
@isnad1 id=eq.3h4v.s8.dcdf4eb3bd0e from=translated src=- shape=a90d9a8f vocab=516d297a
-/
theorem natDegree_contract_mul_eq_of_primitiveRoot_scale_invariant
    {m : ℕ} {ζ : F} {B : Polynomial F}
    (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : B.comp (C ζ * X) = B) :
    (Polynomial.contract m B).natDegree * m = B.natDegree := by
  have h :=
    congrArg Polynomial.natDegree
      (expand_contract_eq_of_primitiveRoot_scale_invariant
        (F := F) hm hζ hinv)
  simpa [Polynomial.natDegree_expand] using h

end LN97
end MagicSquares
