import Tengoku.AbelFormalization.AbelFormalization.LaurentRescaling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rescaling polynomial variables by arbitrary group Laurent monomials

The construction is an actual exponent shear, with no domain, finite-variable, or order assumption.
For G = Fin h → ℤ it supplies the independent Laurent-coordinate substitutions
used in the paper's central-ideal construction.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {R ι G : Type*} [CommSemiring R] [AddCommGroup G]

/-- The additive shear of a group Laurent exponent by a polynomial weight.-/
def groupLaurentExponentShear (ω : ι → G) :
    (G × (ι →₀ ℕ)) ≃+ (G × (ι →₀ ℕ)) where
  toFun a := (a.1 + Finsupp.weight ω a.2, a.2)
  invFun a := (a.1 - Finsupp.weight ω a.2, a.2)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

/--
@isnad1 id=eq.0h5v.s8.efaed7d4415d from=translated src=- shape=3f0d8561 vocab=fef1407c
-/
@[simp] theorem groupLaurentExponentShear_apply (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) :
    groupLaurentExponentShear ω (g, d) = (g + Finsupp.weight ω d, d) := rfl

/--
@isnad1 id=eq.0h5v.s8.edf63c079ff1 from=translated src=- shape=746f4f9c vocab=08a80870
-/
@[simp] theorem groupLaurentExponentShear_symm_apply (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) :
    (groupLaurentExponentShear ω).symm (g, d) =
      (g - Finsupp.weight ω d, d) := rfl

/-- Flatten the Laurent and polynomial indices without altering coefficients.-/
def groupLaurentPolynomialFlatten :
    AddMonoidAlgebra (MvPolynomial ι R) G ≃ₐ[R]
      AddMonoidAlgebra R (G × (ι →₀ ℕ)) :=
  (AddMonoidAlgebra.curryAlgEquiv R).symm

/--
@isnad1 id=eq.0h6v.s9.f99fe4c7c88d from=translated src=- shape=65abf954 vocab=debc93ad
-/
@[simp] theorem groupLaurentPolynomialFlatten_coeff
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) (g : G) (d : ι →₀ ℕ) :
    (groupLaurentPolynomialFlatten f).coeff (g, d) = (f.coeff g).coeff d := rfl

/--
@isnad1 id=eq.0h6v.s9.a4710587c0dc from=translated src=- shape=a8745482 vocab=e5a12c1f
-/
@[simp] theorem groupLaurentPolynomialFlatten_symm_coeff
    (f : AddMonoidAlgebra R (G × (ι →₀ ℕ))) (g : G) (d : ι →₀ ℕ) :
    ((groupLaurentPolynomialFlatten.symm f).coeff g).coeff d = f.coeff (g, d) := rfl

/--
@isnad1 id=eq.0h6v.s9.e37892a3509b from=translated src=- shape=0c8d6565 vocab=6929b2ad
-/
@[simp] theorem groupLaurentPolynomialFlatten_single_monomial
    (g : G) (d : ι →₀ ℕ) (c : R) :
    groupLaurentPolynomialFlatten (AddMonoidAlgebra.single g (MvPolynomial.monomial d c)) =
      AddMonoidAlgebra.single (g, d) c := by
  rw [← MvPolynomial.single_eq_monomial]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single g d c

/--
@isnad1 id=eq.0h6v.s9.480cd77cef65 from=translated src=- shape=575229d7 vocab=0dfdfad7
-/
@[simp] theorem groupLaurentPolynomialFlatten_symm_single
    (g : G) (d : ι →₀ ℕ) (c : R) :
    groupLaurentPolynomialFlatten.symm (AddMonoidAlgebra.single (g, d) c) =
      AddMonoidAlgebra.single g (MvPolynomial.monomial d c) := by
  rw [← groupLaurentPolynomialFlatten_single_monomial]
  exact groupLaurentPolynomialFlatten.symm_apply_apply _

/-- Rescale each polynomial variable zᵢ by the Laurent monomial of exponent ωᵢ.
The Laurent variables and the base coefficient ring are fixed.-/
def groupLaurentWeightRescaling (ω : ι → G) :
    AddMonoidAlgebra (MvPolynomial ι R) G ≃ₐ[R]
      AddMonoidAlgebra (MvPolynomial ι R) G :=
  groupLaurentPolynomialFlatten.trans
    ((AddMonoidAlgebra.domCongr R R (groupLaurentExponentShear ω)).trans
      groupLaurentPolynomialFlatten.symm)

/--
@isnad1 id=eq.0h7v.s9.e910bc2b9d83 from=translated src=- shape=2efffaf2 vocab=8eb90dd2
-/
@[simp] theorem groupLaurentWeightRescaling_single_monomial (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) (c : R) :
    groupLaurentWeightRescaling ω (AddMonoidAlgebra.single g (MvPolynomial.monomial d c)) =
      AddMonoidAlgebra.single (g + Finsupp.weight ω d) (MvPolynomial.monomial d c) := by
  simp [groupLaurentWeightRescaling]

/-- Each output exponent pair has exactly one input coefficient.
@isnad1 id=eq.0h7v.s9.59acd49ef874 from=translated src=- shape=761a3c33 vocab=e8c767cc
-/
@[simp] theorem groupLaurentWeightRescaling_coeff (ω : ι → G)
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) (g : G) (d : ι →₀ ℕ) :
    ((groupLaurentWeightRescaling ω f).coeff g).coeff d =
      (f.coeff (g - Finsupp.weight ω d)).coeff d := by
  simp [groupLaurentWeightRescaling]

/--
@isnad1 id=eq.0h7v.s10.f520a3be645c from=translated src=- shape=c7eb769e vocab=59f1487f
-/
@[simp] theorem groupLaurentWeightRescaling_symm_single_monomial (ω : ι → G)
    (g : G) (d : ι →₀ ℕ) (c : R) :
    (groupLaurentWeightRescaling ω).symm
      (AddMonoidAlgebra.single g (MvPolynomial.monomial d c)) =
      AddMonoidAlgebra.single (g - Finsupp.weight ω d) (MvPolynomial.monomial d c) := by
  apply (groupLaurentWeightRescaling ω).injective
  simp

/--
@isnad1 id=eq.0h5v.s9.81b7e61f20a5 from=translated src=- shape=c6700b2b vocab=d01cffe8
-/
@[simp] theorem groupLaurentWeightRescaling_single_one (ω : ι → G) (g : G) :
    groupLaurentWeightRescaling (R := R) ω (AddMonoidAlgebra.single g 1) =
      AddMonoidAlgebra.single g 1 := by
  simpa only [← MvPolynomial.one_def, map_zero, add_zero] using
    groupLaurentWeightRescaling_single_monomial (R := R) ω g 0 1

/--
@isnad1 id=eq.0h5v.s9.865f5bae273b from=translated src=- shape=ca22aa18 vocab=340846ac
-/
@[simp] theorem groupLaurentWeightRescaling_single_C (ω : ι → G) (c : R) :
    groupLaurentWeightRescaling ω (AddMonoidAlgebra.single 0 (MvPolynomial.C c)) =
      AddMonoidAlgebra.single 0 (MvPolynomial.C c) := by
  simpa only [← MvPolynomial.C_apply, map_zero, add_zero] using
    groupLaurentWeightRescaling_single_monomial ω 0 0 c

/--
@isnad1 id=eq.0h5v.s9.574b7aa18015 from=translated src=- shape=3413a44c vocab=981211f6
-/
@[simp] theorem groupLaurentWeightRescaling_single_X (ω : ι → G) (i : ι) :
    groupLaurentWeightRescaling (R := R) ω (AddMonoidAlgebra.single 0 (MvPolynomial.X i)) =
      AddMonoidAlgebra.single (ω i) (MvPolynomial.X i) := by
  simpa only [← MvPolynomial.X_pow_eq_monomial, pow_one, zero_add,
    Finsupp.weight_single, one_smul] using
    groupLaurentWeightRescaling_single_monomial (R := R) ω 0 (Finsupp.single i 1) 1

/--
@isnad1 id=eq.0h4v.s8.4a9ef3ff7fe5 from=translated src=- shape=80aec272 vocab=be0bb162
-/
theorem group_finsupp_weight_neg (ω : ι → G) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => -ω i) d = -Finsupp.weight ω d := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h5v.s8.ee6fa93e84d7 from=translated src=- shape=597ebe56 vocab=c7deae8d
-/
theorem group_finsupp_weight_add (ω ν : ι → G) (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => ω i + ν i) d =
      Finsupp.weight ω d + Finsupp.weight ν d := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_add_distrib]

/-- The inverse substitution has exactly the opposite weights.
@isnad1 id=eq.0h4v.s8.411826030615 from=translated src=- shape=09e41203 vocab=f4e1cb92
-/
theorem groupLaurentWeightRescaling_symm (ω : ι → G) :
    (groupLaurentWeightRescaling (R := R) ω).symm =
      groupLaurentWeightRescaling (fun i => -ω i) := by
  apply AlgEquiv.ext
  intro f
  apply (groupLaurentWeightRescaling ω).injective
  rw [AlgEquiv.apply_symm_apply]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply MvPolynomial.ext
  intro d
  simp only [groupLaurentWeightRescaling_coeff, group_finsupp_weight_neg,
    sub_neg_eq_add, sub_add_cancel]

/-- Composing actual rescalings adds their group-valued weights.
@isnad1 id=eq.0h5v.s9.bb18cf1da8aa from=translated src=- shape=cd240d7b vocab=f860cb85
-/
theorem groupLaurentWeightRescaling_trans (ω ν : ι → G) :
    (groupLaurentWeightRescaling (R := R) ω).trans (groupLaurentWeightRescaling ν) =
      groupLaurentWeightRescaling (fun i => ω i + ν i) := by
  apply AlgEquiv.ext
  intro f
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply MvPolynomial.ext
  intro d
  change ((groupLaurentWeightRescaling ν (groupLaurentWeightRescaling ω f)).coeff g).coeff d = _
  simp only [groupLaurentWeightRescaling_coeff, group_finsupp_weight_add]
  congr 2
  abel_nf

end AbelFormalization
