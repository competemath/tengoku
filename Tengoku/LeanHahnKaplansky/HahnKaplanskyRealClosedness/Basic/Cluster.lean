/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.Residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# K[X]-level odd-cluster route and high-level reductions
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Bundled coefficient conditions for the `K[X]` odd-cluster statement.-/
def KOddClusterHypotheses (F : (HahnField k Γ)[X]) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i)) ∧
      (∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i)) ∧
        addVal k Γ (F.coeff m) = 0

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=lt.1h4v.s6.46a413b3d4de from=translated src=- shape=81be4e6b vocab=cf622151
-/
theorem KOddClusterHypotheses.pos {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    0 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=odd.1h4v.s6.255ad676cca7 from=translated src=- shape=fd93fdfc vocab=ad8e6746
-/
theorem KOddClusterHypotheses.odd {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    Odd m :=
  h.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=le.1h5v.s8.cf1cf439509e from=translated src=- shape=a3b98ddc vocab=f7ef0e06
-/
theorem KOddClusterHypotheses.nonneg {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i) :=
  h.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=lt.2h5v.s8.dc2ce0ecbaa8 from=translated src=- shape=2bdd86e5 vocab=797dd872
-/
theorem KOddClusterHypotheses.lower {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i) :=
  h.2.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=eq.1h4v.s8.1b26b06589dd from=translated src=- shape=1e03c5ab vocab=4901bc8d
-/
theorem KOddClusterHypotheses.main {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    addVal k Γ (F.coeff m) = 0 :=
  h.2.2.2.2

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=eq.2h5v.s7.aad8572da0ac from=translated src=- shape=9ec84213 vocab=cc0e603e
-/
theorem coeff_newtonInitialPolynomial_zero_zero_eq_zero_of_KOddCluster_lt
    {F : (HahnField k Γ)[X]} {m i : ℕ}
    (h : KOddClusterHypotheses k Γ F m) (hi : i < m) :
    (newtonInitialPolynomial k Γ F 0 0).coeff i = 0 := by
  rw [coeff_newtonInitialPolynomial]
  apply newtonInitialCoeff_of_notMem
  intro hmem
  rcases (mem_newtonInitialSupport k Γ F 0 0).mp hmem with ⟨_hisupp, hweight⟩
  have hval : addVal k Γ (F.coeff i) = 0 := by
    simpa [newtonWeight] using hweight
  exact (ne_of_gt (KOddClusterHypotheses.lower (k := k) (Γ := Γ) h i hi)) hval

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=ne.1h4v.s7.38b6082062b9 from=translated src=- shape=7dda9234 vocab=b47e85ab
-/
theorem coeff_newtonInitialPolynomial_zero_zero_ne_zero_of_KOddCluster
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    (newtonInitialPolynomial k Γ F 0 0).coeff m ≠ 0 := by
  rw [coeff_newtonInitialPolynomial]
  apply newtonInitialCoeff_ne_zero_of_mem
  rw [mem_newtonInitialSupport]
  constructor
  · rw [Polynomial.mem_support_iff]
    intro hcoeff
    have htop : addVal k Γ (F.coeff m) = ⊤ := by
      rw [hcoeff, AddValuation.map_zero]
    rw [h.main] at htop
    exact WithTop.coe_ne_top (a := (0 : Γ)) htop
  · simp [newtonWeight, h.main]

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=eq.1h4v.s7.6cadff552eb6 from=translated src=- shape=4c71dacf vocab=7053dc72
-/
theorem natTrailingDegree_newtonInitialPolynomial_zero_zero_of_KOddCluster
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    (newtonInitialPolynomial k Γ F 0 0).natTrailingDegree = m := by
  let p : k[X] := newtonInitialPolynomial k Γ F 0 0
  have hcoeff_ne : p.coeff m ≠ 0 :=
    coeff_newtonInitialPolynomial_zero_zero_ne_zero_of_KOddCluster k Γ h
  have hp_ne : p ≠ 0 := by
    intro hp
    exact hcoeff_ne (by rw [hp, Polynomial.coeff_zero])
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hcoeff_ne
  · apply Polynomial.le_natTrailingDegree hp_ne
    intro i hi
    exact coeff_newtonInitialPolynomial_zero_zero_eq_zero_of_KOddCluster_lt k Γ h hi

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=eq.1h4v.s7.be4f4f8a7b5a from=translated src=- shape=53bdb276 vocab=ca7cb402
-/
theorem rootMultiplicity_zero_newtonInitialPolynomial_zero_zero_of_KOddCluster
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    (newtonInitialPolynomial k Γ F 0 0).rootMultiplicity 0 = m := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  exact natTrailingDegree_newtonInitialPolynomial_zero_zero_of_KOddCluster k Γ h

/-- A root at a fixed odd-cluster multiplicity.-/
def KOddClusterRootAt (m : ℕ) : Prop :=
  ∀ {F : (HahnField k Γ)[X]},
    KOddClusterHypotheses k Γ F m → PositiveHahnRoot k Γ F

/-- Roots for all odd-cluster multiplicities below `M`.-/
def KOddClusterRootBelow (M : ℕ) : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    m < M → KOddClusterHypotheses k Γ F m → PositiveHahnRoot k Γ F

/-- A selected odd residue branch of the zero-slope initial polynomial.

This is the Hahn analogue of the Puiseux residue branch API, stripped of fixed-level and
denominator data.  The branch records that the initial polynomial has an odd root multiplicity
`r` at residue root `a`.-/
def KResidueBranchMultiplicity (F : (HahnField k Γ)[X]) (m : ℕ) (a : k)
    (r : ℕ) : Prop :=
  KOddClusterHypotheses k Γ F m ∧
    (newtonInitialPolynomial k Γ F 0 0).rootMultiplicity a = r ∧ 0 < r ∧ r ≤ m ∧ Odd r

/-- A translated branch whose chosen residue root is `0`.-/
def KTranslatedZeroBranch (F : (HahnField k Γ)[X]) (m r : ℕ) : Prop :=
  KResidueBranchMultiplicity k Γ F m 0 r

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=kresidue.1h4v.s7.69e95cc32f7f from=translated src=- shape=d5cc1ef8 vocab=2f739ff0
-/
theorem KOddClusterHypotheses.zero_residueBranchMultiplicity
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    KResidueBranchMultiplicity k Γ F m 0 m :=
  ⟨h, rootMultiplicity_zero_newtonInitialPolynomial_zero_zero_of_KOddCluster k Γ h,
    h.pos, le_rfl, h.odd⟩

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=ktransla.1h4v.s6.b21c9f12f6f1 from=translated src=- shape=3b18d5c7 vocab=1c2ba75e
-/
theorem KOddClusterHypotheses.translatedZeroBranch
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    KTranslatedZeroBranch k Γ F m m :=
  h.zero_residueBranchMultiplicity

/-- Same-multiplicity translated branch.  This is the boundary that must not be hidden inside
the ordinary induction step.-/
def KTranslatedSameMultiplicityZeroBranch (F : (HahnField k Γ)[X]) (m : ℕ) : Prop :=
  1 < m ∧ KTranslatedZeroBranch k Γ F m m

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=lt.1h4v.s6.6178463ebd47 from=translated src=- shape=81be4e6b vocab=6131fce8
-/
theorem KTranslatedSameMultiplicityZeroBranch.one_lt
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    1 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
/--
@isnad1 id=ktransla.1h4v.s6.e66e3f40d274 from=translated src=- shape=3b18d5c7 vocab=e806cebc
-/
theorem KTranslatedSameMultiplicityZeroBranch.branch
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    KTranslatedZeroBranch k Γ F m m :=
  h.2

/-- Same-multiplicity omega continuation closes the same-multiplicity branch.-/
def KSameMultiplicityOmegaContinuationHypothesis : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    KTranslatedSameMultiplicityZeroBranch k Γ F m → PositiveHahnRoot k Γ F

/-- Omega continuation for all odd-cluster multiplicities strictly above one.-/
def KOddClusterOmegaContinuationAboveOneHypothesis : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    1 < m → KOddClusterHypotheses k Γ F m → PositiveHahnRoot k Γ F

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If the value group is subsingleton, the Hahn field is real closed because it is ring
equivalent to the coefficient field.
@isnad1 id=isrealcl.0h2v.s5.c43d2e2ba06c from=translated src=- shape=4c74414b vocab=0370b821
-/
theorem isRealClosed_of_subsingleton_valueGroup [IsRealClosed k] [Subsingleton Γ] :
    IsRealClosed (HahnField k Γ) :=
  isRealClosed_of_ringEquiv (subsingletonValueGroupRingEquiv k Γ)

end HahnField

end

end HahnKaplanskyRealClosedness
