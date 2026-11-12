import Tengoku.AbelFormalization.AbelFormalization.LexicographicInitialIdealLocalization
import Tengoku.Seed.RingTheory.MvPolynomial.Localization
import Tengoku.Seed.RingTheory.Localization.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Lexicographic initial ideals commute with coefficient localization

The forward inclusion is valid for every coefficient homomorphism and is
proved in `LexicographicInitialIdealLocalization`.  For the reverse
inclusion, write a polynomial in the extended ideal with one constant
denominator and numerator `p ∈ I`.  Every coefficient of `p` below the
least surviving weight maps to zero.  Since there are only finitely many of
them, one element of the localization submonoid annihilates all of them.
After multiplying `p` by this common annihilator, its actual initial form
maps to a unit times the desired localized initial form.
-/

noncomputable section

namespace AbelFormalization

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## Two denominator-clearing lemmas -/

/-- Finitely many elements, each annihilated by some member of a commutative
submonoid, have a common annihilator in that submonoid.-/
theorem exists_submonoid_common_annihilator
    {R κ : Type*} [CommRing R]
    (S : Submonoid R) (indices : Finset κ) (a : κ → R)
    (h : ∀ i ∈ indices, ∃ s : S, (s : R) * a i = 0) :
    ∃ s : S, ∀ i ∈ indices, (s : R) * a i = 0 := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      exact ⟨1, by simp⟩
  | @insert i indices hi ih =>
      obtain ⟨si, hsi⟩ := h i (Finset.mem_insert_self i indices)
      obtain ⟨st, hst⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
      refine ⟨si * st, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · change ((si : R) * (st : R)) * a j = 0
        calc
          ((si : R) * (st : R)) * a j =
              (st : R) * ((si : R) * a j) := by ac_rfl
          _ = (st : R) * ((si : R) * a i) := by rw [hji]
          _ = 0 := by rw [hsi, mul_zero]
      · change ((si : R) * (st : R)) * a j = 0
        rw [mul_assoc, hst j hj, mul_zero]

/-- Membership in the extension of an ideal to a coefficient localization
can be expressed with a numerator in the source ideal and one constant
denominator.-/
theorem exists_mul_C_eq_map_of_mem_localizedIdeal
    {R ι : Type*} [CommRing R]
    (S : Submonoid R) (I : Ideal (MvPolynomial ι R))
    {g : MvPolynomial ι (Localization S)}
    (hg : g ∈ I.map
      (MvPolynomial.map (algebraMap R (Localization S)))) :
    ∃ p ∈ I, ∃ s : S,
      g * MvPolynomial.C (algebraMap R (Localization S) (s : R)) =
        MvPolynomial.map (algebraMap R (Localization S)) p := by
  have hg' : g ∈ I.map
      (algebraMap (MvPolynomial ι R)
        (MvPolynomial ι (Localization S))) := by
    simpa only [MvPolynomial.algebraMap_def] using hg
  obtain ⟨⟨⟨p, hp⟩, denominator⟩, hdenominator⟩ :=
    (IsLocalization.mem_map_algebraMap_iff
      (S.map (MvPolynomial.C : R →+* MvPolynomial ι R))
      (MvPolynomial ι (Localization S))).mp hg'
  obtain ⟨s, hs, hsdenominator⟩ := denominator.property
  refine ⟨p, hp, ⟨s, hs⟩, ?_⟩
  rw [← hsdenominator] at hdenominator
  simpa only [MvPolynomial.algebraMap_def,
    MvPolynomial.map_C] using hdenominator

/-! ## Clearing the killed lower components -/

/-! ## Equality after localization -/

end AbelFormalization
