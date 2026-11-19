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
theorem KOddClusterHypotheses.pos {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    0 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.odd {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    Odd m :=
  h.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.nonneg {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i) :=
  h.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.lower {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i) :=
  h.2.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.main {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    addVal k Γ (F.coeff m) = 0 :=
  h.2.2.2.2

omit [LinearOrder k] [IsStrictOrderedRing k] in
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
theorem KOddClusterHypotheses.zero_residueBranchMultiplicity
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    KResidueBranchMultiplicity k Γ F m 0 m :=
  ⟨h, rootMultiplicity_zero_newtonInitialPolynomial_zero_zero_of_KOddCluster k Γ h,
    h.pos, le_rfl, h.odd⟩

omit [LinearOrder k] [IsStrictOrderedRing k] in
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
theorem KTranslatedSameMultiplicityZeroBranch.one_lt
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    1 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
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
equivalent to the coefficient field.-/
theorem isRealClosed_of_subsingleton_valueGroup [IsRealClosed k] [Subsingleton Γ] :
    IsRealClosed (HahnField k Γ) :=
  isRealClosed_of_ringEquiv (subsingletonValueGroupRingEquiv k Γ)

end HahnField

end

end HahnKaplanskyRealClosedness
