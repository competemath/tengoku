import Tengoku.AbelFormalization.AbelFormalization.WeightedDeformationGenerators
import Tengoku.Seed.Algebra.MvPolynomial.Degrees

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Literal ordinary homogenization

The new ordinary polynomial variable is the homogenizing parameter. A
monomial of total degree `k` receives parameter exponent `totalDegree f - k`.
This is exactly the minimum-weight normalization for constant weight `-1`.
The zero polynomial uses the usual mathlib total degree convention `0`.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*}

section Semiring

variable [CommSemiring R]

/-- The literal ordinary homogenization, retaining the original variables in
the coefficient ring and using the outer polynomial variable as parameter.-/
def ordinaryHomogenize (f : MvPolynomial ι R) : Polynomial (MvPolynomial ι R) := by
  classical
  exact ∑ d ∈ f.support,
    Polynomial.monomial (f.totalDegree - d.sum (fun _ n => n))
      (MvPolynomial.monomial d (f.coeff d))

/--
@isnad1 id=eq.0h2v.s7.37d643306b4d from=translated src=- shape=05b81e69 vocab=71135b24
-/
@[simp]
theorem ordinaryHomogenize_zero : ordinaryHomogenize (0 : MvPolynomial ι R) = 0 := by
  simp [ordinaryHomogenize]

/-- Constant integer weight `-1` is minus the usual monomial total degree.
@isnad1 id=eq.0h2v.s7.477dcbbbf56e from=translated src=- shape=0b8a2304 vocab=78d23d73
-/
theorem finsupp_weight_neg_one (d : ι →₀ ℕ) :
    Finsupp.weight (fun _ : ι => (-1 : ℤ)) d =
      -((d.sum (fun _ n => n) : ℕ) : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib]

/-- The minimum negative total degree is minus the largest total degree,
including for the zero polynomial.
@isnad1 id=eq.0h3v.s5.a80b0e854de7 from=translated src=- shape=63d1f4a0 vocab=020c57ea
-/
theorem minimumSupportWeight_neg_one (f : MvPolynomial ι R) :
    minimumSupportWeight (fun _ : ι => (-1 : ℤ)) f = -(f.totalDegree : ℤ) := by
  classical
  by_cases hf : f = 0
  · subst f
    simp
  have hs : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
  obtain ⟨d, hd, hdegree⟩ :=
    Finset.exists_mem_eq_sup f.support hs (fun d : ι →₀ ℕ => d.sum (fun _ n => n))
  have hdegree' : d.sum (fun _ n => n) = f.totalDegree := by
    exact hdegree.symm
  apply le_antisymm
  · have hmin := minimumSupportWeight_le (fun _ : ι => (-1 : ℤ)) f hd
    simpa only [finsupp_weight_neg_one, hdegree'] using hmin
  · obtain ⟨e, he, hweight⟩ :=
      exists_support_weight_eq_minimum (fun _ : ι => (-1 : ℤ)) hf
    rw [← hweight, finsupp_weight_neg_one]
    exact neg_le_neg (Nat.cast_le.mpr (MvPolynomial.le_totalDegree he))

/-- The weighted construction at weight `-1` agrees term by term with the
literal formula for ordinary homogenization.
@isnad1 id=eq.0h3v.s5.bfece4057687 from=translated src=- shape=2085e413 vocab=a4cd0e9f
-/
theorem weightedNormalize_neg_one (f : MvPolynomial ι R) :
    weightedNormalize (fun _ : ι => (-1 : ℤ)) f = ordinaryHomogenize f := by
  classical
  rw [weightedNormalize, ordinaryHomogenize]
  apply Finset.sum_congr rfl
  intro d hd
  rw [finsupp_weight_neg_one, minimumSupportWeight_neg_one]
  have hcast :
      -((d.sum (fun _ n => n) : ℕ) : ℤ) - -(f.totalDegree : ℤ) =
        ((f.totalDegree - d.sum (fun _ n => n) : ℕ) : ℤ) := by
    rw [sub_neg_eq_add, Nat.cast_sub (MvPolynomial.le_totalDegree hd), sub_eq_add_neg]
    exact add_comm _ _
  rw [hcast, Int.toNat_natCast]

/-- The ordinary homogenization is the literal Laurent substitution
`τ^D f(τ⁻¹ z)`, where `D` is the actual total degree of `f`.
@isnad1 id=eq.0h3v.s10.d621eb749aae from=translated src=- shape=516c8b84 vocab=596b767a
-/
theorem ordinaryHomogenize_toLaurent (f : MvPolynomial ι R) :
    Polynomial.toLaurent (ordinaryHomogenize f) =
      LaurentPolynomial.T (f.totalDegree : ℤ) *
        laurentWeightRescaling (fun _ : ι => (-1 : ℤ)) (LaurentPolynomial.C f) := by
  rw [← weightedNormalize_neg_one, weightedNormalize_toLaurent,
    minimumSupportWeight_neg_one, neg_neg]

/-- Setting the homogenizing parameter equal to one recovers the original
polynomial, with no nonzero or degree hypothesis.
@isnad1 id=eq.0h3v.s6.42c0f47497ad from=translated src=- shape=636fc989 vocab=6e76ca66
-/
@[simp]
theorem ordinaryHomogenize_eval_one (f : MvPolynomial ι R) :
    (ordinaryHomogenize f).eval 1 = f := by
  classical
  simp [ordinaryHomogenize, Polynomial.eval_finsetSum]

/-- Full ordinary homogenization uses the homogenizations of every element
of the ideal, independently of a selected generating set.-/
def fullOrdinaryHomogenization (I : Ideal (MvPolynomial ι R)) :
    Ideal (Polynomial (MvPolynomial ι R)) :=
  Ideal.span (ordinaryHomogenize '' (I : Set (MvPolynomial ι R)))

/--
@isnad1 id=mem.1h4v.s8.0fb70793c6a0 from=translated src=- shape=6ea0bed1 vocab=971f5458
-/
theorem ordinaryHomogenize_mem_fullOrdinaryHomogenization
    (I : Ideal (MvPolynomial ι R)) {f : MvPolynomial ι R} (hf : f ∈ I) :
    ordinaryHomogenize f ∈ fullOrdinaryHomogenization I :=
  Ideal.subset_span ⟨f, hf, rfl⟩

end Semiring

section Ring

variable [CommRing R]

/-- The ideal generated by all literal ordinary homogenizations is exactly
the Laurent contraction. This identifies the full operation, rather than
only the homogenizations of a selected finite generating list.
@isnad1 id=eq.0h3v.s6.99f497ab4236 from=translated src=- shape=80f315e0 vocab=589fb1d2
-/
theorem fullOrdinaryHomogenization_eq_contraction
    (I : Ideal (MvPolynomial ι R)) :
    fullOrdinaryHomogenization I = ordinaryHomogenizationContraction I := by
  unfold fullOrdinaryHomogenization ordinaryHomogenizationContraction
  rw [weightedDeformationIdeal_eq_span_normalize]
  have hnorm : weightedNormalize (fun _ : ι => (-1 : ℤ)) =
      (ordinaryHomogenize : MvPolynomial ι R → Polynomial (MvPolynomial ι R)) := by
    funext f
    exact weightedNormalize_neg_one f
  rw [hnorm]

/-- Saturation in the homogenizing parameter follows for the actual full
ideal from its proved contraction presentation.
@isnad1 id=mem.1h4v.s9.5f7c06d6c66f from=translated src=- shape=f13be04a vocab=33f7b00a
-/
theorem fullOrdinaryHomogenization_cancel_X (I : Ideal (MvPolynomial ι R))
    (f : Polynomial (MvPolynomial ι R))
    (hf : Polynomial.X * f ∈ fullOrdinaryHomogenization I) :
    f ∈ fullOrdinaryHomogenization I := by
  rw [fullOrdinaryHomogenization_eq_contraction] at hf ⊢
  exact ordinaryHomogenizationContraction_cancel_X I f hf

end Ring

end AbelFormalization
