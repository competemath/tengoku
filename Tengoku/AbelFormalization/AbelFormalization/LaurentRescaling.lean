import Tengoku.Seed.Algebra.Polynomial.Laurent
import Tengoku.Seed.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer-weight Laurent rescaling

Flattening the Laurent and polynomial exponents identifies rescaling with an
actual additive monoid automorphism. The coefficient formula records the
absence of cancellation between different original Laurent exponents at a
fixed polynomial monomial, which is the key algebraic fact in the paper's
full initial-ideal construction.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*} [CommSemiring R]

/-- Integer rescaling is a shear of the Laurent exponent by the polynomial
monomial's weight. No sign restriction on the variable weights is needed.-/
def laurentExponentShear (ω : ι → ℤ) :
    (ℤ × (ι →₀ ℕ)) ≃+ (ℤ × (ι →₀ ℕ)) where
  toFun a := (a.1 + Finsupp.weight ω a.2, a.2)
  invFun a := (a.1 - Finsupp.weight ω a.2, a.2)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

/--
@isnad1 id=eq.0h4v.s8.7ffa21bd82db from=translated src=- shape=93633b00 vocab=2303327b
-/
@[simp]
theorem laurentExponentShear_apply (ω : ι → ℤ) (n : ℤ) (d : ι →₀ ℕ) :
    laurentExponentShear ω (n, d) = (n + Finsupp.weight ω d, d) := rfl

/--
@isnad1 id=eq.0h4v.s8.43f248fa1911 from=translated src=- shape=3d4c3699 vocab=eae9cfef
-/
@[simp]
theorem laurentExponentShear_symm_apply (ω : ι → ℤ) (n : ℤ) (d : ι →₀ ℕ) :
    (laurentExponentShear ω).symm (n, d) = (n - Finsupp.weight ω d, d) := rfl

/-- Flattening separates the integer Laurent exponent from the natural
polynomial multi-index.-/
def laurentPolynomialFlatten :
    LaurentPolynomial (MvPolynomial ι R) ≃ₐ[R]
      AddMonoidAlgebra R (ℤ × (ι →₀ ℕ)) :=
  (AddMonoidAlgebra.curryAlgEquiv R).symm

/--
@isnad1 id=eq.0h5v.s9.54f54fb646cc from=translated src=- shape=24db2c4e vocab=0fc78f98
-/
@[simp]
theorem laurentPolynomialFlatten_coeff
    (f : LaurentPolynomial (MvPolynomial ι R)) (n : ℤ) (d : ι →₀ ℕ) :
    (laurentPolynomialFlatten f).coeff (n, d) = (f.coeff n).coeff d := rfl

/--
@isnad1 id=eq.0h5v.s9.73d18677ce3e from=translated src=- shape=1aff98c2 vocab=eee573ab
-/
@[simp]
theorem laurentPolynomialFlatten_symm_coeff
    (f : AddMonoidAlgebra R (ℤ × (ι →₀ ℕ))) (n : ℤ) (d : ι →₀ ℕ) :
    ((laurentPolynomialFlatten.symm f).coeff n).coeff d =
      f.coeff (n, d) := rfl

/--
@isnad1 id=eq.0h5v.s9.cc69f527e2d4 from=translated src=- shape=50ec3af3 vocab=d82ab598
-/
@[simp]
theorem laurentPolynomialFlatten_monomial (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    laurentPolynomialFlatten
      (LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n) =
      AddMonoidAlgebra.single (n, d) c := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← MvPolynomial.single_eq_monomial]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single n d c

/--
@isnad1 id=eq.0h5v.s10.69f97593a1d4 from=translated src=- shape=0d219ead vocab=b2afecaa
-/
@[simp]
theorem laurentPolynomialFlatten_symm_single (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    laurentPolynomialFlatten.symm (AddMonoidAlgebra.single (n, d) c) =
      LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n := by
  rw [← laurentPolynomialFlatten_monomial]
  exact laurentPolynomialFlatten.symm_apply_apply _

/-- The actual coefficient-fixing automorphism `zᵢ ↦ τ^(ωᵢ) zᵢ`, with
the Laurent parameter `τ` fixed.-/
def laurentWeightRescaling (ω : ι → ℤ) :
    LaurentPolynomial (MvPolynomial ι R) ≃ₐ[R]
      LaurentPolynomial (MvPolynomial ι R) :=
  laurentPolynomialFlatten.trans
    ((AddMonoidAlgebra.domCongr R R (laurentExponentShear ω)).trans
      laurentPolynomialFlatten.symm)

/-- Exact action on every Laurent-polynomial monomial.
@isnad1 id=eq.0h6v.s10.b9f09daef396 from=translated src=- shape=1261a193 vocab=4109f0c3
-/
@[simp]
theorem laurentWeightRescaling_monomial (ω : ι → ℤ)
    (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    laurentWeightRescaling ω
      (LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n) =
      LaurentPolynomial.C (MvPolynomial.monomial d c) *
        LaurentPolynomial.T (n + Finsupp.weight ω d) := by
  simp [laurentWeightRescaling]

/-- Each resulting pair of exponents has exactly one preimage. In particular,
the deformation's polynomiality can be checked without a domain assumption.
@isnad1 id=eq.0h6v.s9.cbb37faeca14 from=translated src=- shape=3a597d4a vocab=c63c5ae5
-/
@[simp]
theorem laurentWeightRescaling_coeff (ω : ι → ℤ)
    (f : LaurentPolynomial (MvPolynomial ι R)) (n : ℤ) (d : ι →₀ ℕ) :
    ((laurentWeightRescaling ω f).coeff n).coeff d =
      (f.coeff (n - Finsupp.weight ω d)).coeff d := by
  simp [laurentWeightRescaling]

/-- The inverse shifts each Laurent exponent by the opposite amount.
@isnad1 id=eq.0h6v.s10.987620def0be from=translated src=- shape=8ee5c7ee vocab=8834b994
-/
@[simp]
theorem laurentWeightRescaling_symm_monomial (ω : ι → ℤ)
    (n : ℤ) (d : ι →₀ ℕ) (c : R) :
    (laurentWeightRescaling ω).symm
      (LaurentPolynomial.C (MvPolynomial.monomial d c) * LaurentPolynomial.T n) =
      LaurentPolynomial.C (MvPolynomial.monomial d c) *
        LaurentPolynomial.T (n - Finsupp.weight ω d) := by
  apply (laurentWeightRescaling ω).injective
  simp

/--
@isnad1 id=eq.0h4v.s8.d067af42dd22 from=translated src=- shape=a2223a5a vocab=5ad9215b
-/
@[simp]
theorem laurentWeightRescaling_T (ω : ι → ℤ) (n : ℤ) :
    laurentWeightRescaling (R := R) ω (LaurentPolynomial.T n) =
      LaurentPolynomial.T n := by
  simpa only [← MvPolynomial.one_def, map_one, one_mul, map_zero, add_zero] using
    laurentWeightRescaling_monomial (R := R) ω n 0 1

/--
@isnad1 id=eq.0h4v.s9.ffdc605925c6 from=translated src=- shape=0e9cb205 vocab=fbe0c9eb
-/
@[simp]
theorem laurentWeightRescaling_C_C (ω : ι → ℤ) (c : R) :
    laurentWeightRescaling ω (LaurentPolynomial.C (MvPolynomial.C c)) =
      LaurentPolynomial.C (MvPolynomial.C c) := by
  simpa only [← MvPolynomial.C_apply, LaurentPolynomial.T_zero, mul_one,
    map_zero, add_zero] using laurentWeightRescaling_monomial ω 0 0 c

/--
@isnad1 id=eq.0h4v.s9.40ede3ffaf62 from=translated src=- shape=845a00b8 vocab=0f586f04
-/
@[simp]
theorem laurentWeightRescaling_C_X (ω : ι → ℤ) (i : ι) :
    laurentWeightRescaling (R := R) ω (LaurentPolynomial.C (MvPolynomial.X i)) =
      LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T (ω i) := by
  simpa only [← MvPolynomial.X_pow_eq_monomial, pow_one,
    LaurentPolynomial.T_zero, mul_one, zero_add, Finsupp.weight_single, one_smul] using
    laurentWeightRescaling_monomial (R := R) ω 0 (Finsupp.single i 1) 1

/--
@isnad1 id=eq.0h3v.s7.029c4278971b from=translated src=- shape=9445312f vocab=9818f40c
-/
theorem finsupp_weight_neg (ω : ι → ℤ) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => -ω i) d = -Finsupp.weight ω d := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h4v.s8.84beab5cbf42 from=translated src=- shape=41b31779 vocab=ec4b8b94
-/
theorem finsupp_weight_add (ω ν : ι → ℤ) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => ω i + ν i) d =
      Finsupp.weight ω d + Finsupp.weight ν d := by
  simp [Finsupp.weight_apply, Finsupp.sum, mul_add, Finset.sum_add_distrib]

/-- The inverse rescaling is the one with all variable weights negated.
@isnad1 id=eq.0h3v.s8.b5a1f935b67d from=translated src=- shape=db145524 vocab=55091bee
-/
theorem laurentWeightRescaling_symm (ω : ι → ℤ) :
    (laurentWeightRescaling (R := R) ω).symm =
      laurentWeightRescaling (fun i => -ω i) := by
  apply AlgEquiv.ext
  intro f
  apply (laurentWeightRescaling ω).injective
  rw [AlgEquiv.apply_symm_apply]
  apply LaurentPolynomial.ext
  intro n
  apply MvPolynomial.ext
  intro d
  simp only [laurentWeightRescaling_coeff, finsupp_weight_neg, sub_neg_eq_add,
    sub_add_cancel]

/-- Successive rescalings add their weight vectors.
@isnad1 id=eq.0h4v.s8.a59f91b01693 from=translated src=- shape=28f3ba29 vocab=2f8b9a47
-/
theorem laurentWeightRescaling_trans (ω ν : ι → ℤ) :
    (laurentWeightRescaling (R := R) ω).trans (laurentWeightRescaling ν) =
      laurentWeightRescaling (fun i => ω i + ν i) := by
  apply AlgEquiv.ext
  intro f
  apply LaurentPolynomial.ext
  intro n
  apply MvPolynomial.ext
  intro d
  change ((laurentWeightRescaling ν (laurentWeightRescaling ω f)).coeff n).coeff d = _
  simp only [laurentWeightRescaling_coeff, finsupp_weight_add]
  congr 2
  abel_nf

end AbelFormalization
