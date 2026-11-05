import Tengoku.NsP23.P23.Semigroup.AperyQuotient
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chosen-base tail presentation

This file constructs the three-variable presentation of the genuine quotient
`k[Γ]/(t^q)`.  Its arguments use arbitrary semigroup factorizations; no
unique-factorization hypothesis or bounded search is used.
-/

namespace P23.Semigroup

noncomputable section

open scoped BigOperators
open FourGeneratedNumericalSemigroup AperyArtin

variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

/-- Three-variable polynomial ring attached to the three generators other
than the chosen base.-/
abbrev TailPoly (k : Type*) [CommSemiring k] := MvPolynomial (Fin 3) k

/-- Degree of a tail exponent vector in the numerical semigroup.-/
def tailDegree (u : Fin 3 →₀ ℕ) : ℕ :=
  ∑ j : Fin 3, u j * D.tailGen i j

/--
@isnad1 id=eq.0h2v.s5.2ffdfd9ef159 from=translated src=- shape=db7dfd5b vocab=ac2e2824
-/
@[simp] theorem tailDegree_zero : tailDegree D i 0 = 0 := by
  simp [tailDegree]

/--
@isnad1 id=eq.0h4v.s6.be750bdd54dd from=translated src=- shape=32649446 vocab=3fdcdf4d
-/
theorem tailDegree_add (u v : Fin 3 →₀ ℕ) :
    tailDegree D i (u + v) = tailDegree D i u + tailDegree D i v := by
  simp [tailDegree, add_mul, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h4v.s5.4db010fbd972 from=translated src=- shape=8a5fe069 vocab=19f60de8
-/
@[simp] theorem tailDegree_single (j : Fin 3) (n : ℕ) :
    tailDegree D i (Finsupp.single j n) = n * D.tailGen i j := by
  classical
  simp [tailDegree, Finsupp.single_apply]

/-- Restriction of a four-generator factorization to the three tail
coordinates.-/
def tailExponent (u : Fin 4 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => u (D.tailIndex i j))

/--
@isnad1 id=eq.0h4v.s7.11784f1d76cc from=translated src=- shape=8d1d89cf vocab=057c9c45
-/
@[simp] theorem tailExponent_apply (u : Fin 4 →₀ ℕ) (j : Fin 3) :
    tailExponent D i u j = u (D.tailIndex i j) := by
  simp [tailExponent]

/--
@isnad1 id=eq.1h3v.s6.0b04ab45c9c3 from=translated src=- shape=dca4a3b6 vocab=614a1f13
-/
theorem weightedDegree_eq_tailDegree_of_base_zero (u : Fin 4 →₀ ℕ)
    (hu : u i = 0) :
    D.weightedDegree u = tailDegree D i (tailExponent D i u) := by
  change (∑ j : Fin 4, u j * D.n j) =
    ∑ j : Fin 3, u (i.succAbove j) * D.n (i.succAbove j)
  rw [Fin.sum_univ_succAbove _ i]
  simp [hu, tailDegree, tailExponent, FourGeneratedNumericalSemigroup.tailGen,
    FourGeneratedNumericalSemigroup.tailIndex]

/-- A tail exponent vector extended by zero at the selected base index.-/
def extendTailExponent (u : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (Fin.succAboveCases i (0 : ℕ) (fun j => u j))

/--
@isnad1 id=eq.0h2v.s6.160ad787e3dc from=translated src=- shape=b4895b9f vocab=7c644982
-/
@[simp] theorem extendTailExponent_base (u : Fin 3 →₀ ℕ) :
    extendTailExponent i u i = 0 := by
  simp [extendTailExponent]

/--
@isnad1 id=eq.0h3v.s6.dd28ea2194cf from=translated src=- shape=a961acf1 vocab=c6588665
-/
@[simp] theorem extendTailExponent_tail (u : Fin 3 →₀ ℕ) (j : Fin 3) :
    extendTailExponent i u (i.succAbove j) = u j := by
  simp [extendTailExponent]

/--
@isnad1 id=eq.0h3v.s5.430a30f4ca23 from=translated src=- shape=6fb35b43 vocab=1445cf35
-/
theorem weightedDegree_extendTailExponent (u : Fin 3 →₀ ℕ) :
    D.weightedDegree (extendTailExponent i u) = tailDegree D i u := by
  rw [weightedDegree_eq_tailDegree_of_base_zero D i _ (extendTailExponent_base i u)]
  congr 1
  apply Finsupp.ext
  intro j
  simp [tailExponent, extendTailExponent]

/-- Semigroup degree represented by a tail exponent vector.-/
def tailDegreeGamma (u : Fin 3 →₀ ℕ) : D.Gamma :=
  ⟨tailDegree D i u, (D.mem_Gamma_iff _).2
    ⟨extendTailExponent i u, weightedDegree_extendTailExponent D i u⟩⟩

/--
@isnad1 id=eq.0h2v.s7.8ae8bded2be8 from=translated src=- shape=7399a3e7 vocab=58dc7aaa
-/
@[simp] theorem tailDegreeGamma_zero : tailDegreeGamma D i 0 = 0 := by
  apply Subtype.ext
  simp [tailDegreeGamma]

/--
@isnad1 id=eq.0h4v.s7.2eba8bd4f6c9 from=translated src=- shape=7fb7b63d vocab=b7a35a2a
-/
theorem tailDegreeGamma_add (u v : Fin 3 →₀ ℕ) :
    tailDegreeGamma D i (u + v) = tailDegreeGamma D i u + tailDegreeGamma D i v := by
  apply Subtype.ext
  exact tailDegree_add D i u v

/-- Tail variable in the finite Apéry algebra.-/
def tailVariableA (j : Fin 3) : AperyArtin k D i :=
  A (k := k) (D.tail i j) (D.tail_isApery i j)

/--
@isnad1 id=eq.0h4v.s5.9a084aea70f7 from=translated src=- shape=392ce6e0 vocab=de7df74b
-/
@[simp] theorem truncatedAperyMonomial_tail (j : Fin 3) :
    truncatedAperyMonomial (k := k) D i (D.tail i j) =
      tailVariableA (k := k) D i j := by
  simp [truncatedAperyMonomial, tailVariableA, D.tail_isApery i j]

/-- Polynomial evaluation in the finite Apéry model.-/
def tailPolyToApery : TailPoly k →ₐ[k] AperyArtin k D i :=
  MvPolynomial.aeval (tailVariableA (k := k) D i)

/-- Polynomial evaluation in the genuine chosen-base quotient.-/
def tailPolyToChosenBase : TailPoly k →ₐ[k] ChosenBaseQuotient (k := k) D i :=
  (chosenBaseEquivApery (k := k) D i).symm.toAlgHom.comp
    (tailPolyToApery (k := k) D i)

/--
@isnad1 id=eq.0h4v.s8.9077e1992245 from=translated src=- shape=d8a61f4c vocab=796f2a3f
-/
@[simp] theorem tailPolyToApery_X (j : Fin 3) :
    tailPolyToApery (k := k) D i (MvPolynomial.X j) = tailVariableA (k := k) D i j := by
  simp [tailPolyToApery]

private theorem tailVariable_prod (u : Fin 3 →₀ ℕ) :
    u.prod (fun j n => (tailVariableA (k := k) D i j) ^ n) =
      truncatedAperyMonomial (k := k) D i
        (tailDegreeGamma D i u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      rw [hu, hv, ← truncatedAperyMonomial_add]
      congr 2
      exact (tailDegreeGamma_add D i u v).symm
  | single j n =>
      rw [Finsupp.prod_single_index]
      · induction n with
        | zero => simp
        | succ n hn =>
            rw [pow_succ, hn, ← truncatedAperyMonomial_tail,
              ← truncatedAperyMonomial_add]
            congr 2
            apply Subtype.ext
            simp only [AddSubmonoid.coe_add]
            change tailDegree D i (Finsupp.single j n) + D.tailGen i j =
              tailDegree D i (Finsupp.single j (n + 1))
            rw [tailDegree_single, tailDegree_single]
            simp [Nat.add_mul]
      · simp

/-- Exact arbitrary tail-monomial image.
@isnad1 id=eq.0h5v.s9.a093388b95ec from=translated src=- shape=67c20613 vocab=b2cd059c
-/
@[simp] theorem tailPolyToApery_monomial (u : Fin 3 →₀ ℕ) (r : k) :
    tailPolyToApery (k := k) D i (MvPolynomial.monomial u r) =
      r • truncatedAperyMonomial (k := k) D i
        (tailDegreeGamma D i u) := by
  rw [tailPolyToApery, MvPolynomial.aeval_monomial, tailVariable_prod]
  simp [Algebra.smul_def]

/-- Every Apéry degree has a tail-only factorization.
@isnad1 id=ex.1h3v.s6.c81753351ffe from=translated src=- shape=abfe2e95 vocab=ffd3e95c
-/
theorem exists_tailExponent_of_isApery {s : D.Gamma} (hs : D.IsApery i s) :
    ∃ u : Fin 3 →₀ ℕ, tailDegree D i u = s.1 := by
  rcases (D.mem_Gamma_iff s.1).1 s.2 with ⟨v, hv⟩
  have hvi := D.apery_factorization_base_eq_zero i hs v hv
  refine ⟨tailExponent D i v, ?_⟩
  rw [← weightedDegree_eq_tailDegree_of_base_zero D i v hvi, hv]

/-- Minimality of the original four generators says that the only tail
factorization of a tail generator is its coordinate vector.
@isnad1 id=iff.0h4v.s6.32cce8c48eee from=translated src=- shape=e6b6b9fe vocab=f9dbd2dc
-/
theorem tailDegree_eq_tailGen_iff {u : Fin 3 →₀ ℕ} {j : Fin 3} :
    tailDegree D i u = D.tailGen i j ↔ u = Finsupp.single j 1 := by
  constructor
  · intro hdeg
    let w := extendTailExponent i u
    let tj : Fin 4 := D.tailIndex i j
    have hwdeg : D.weightedDegree w = D.n tj := by
      rw [weightedDegree_extendTailExponent, hdeg]
      rfl
    have huj0 : u j ≠ 0 := by
      intro huj
      have hwtj : w tj = 0 := by
        simp [w, tj, extendTailExponent, huj]
      exact D.minimal tj w hwtj hwdeg
    have hujpos : 0 < u j := Nat.pos_of_ne_zero huj0
    have hterm : u j * D.tailGen i j ≤ tailDegree D i u := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hgenpos := D.tailGen_positive i j
    have huj : u j = 1 := by nlinarith [hterm]
    have hrest : ∑ l ∈ Finset.univ.erase j, u l * D.tailGen i l = 0 := by
      have hsplit := Finset.sum_erase_add (s := Finset.univ)
        (f := fun l : Fin 3 => u l * D.tailGen i l) (Finset.mem_univ j)
      change (∑ l ∈ Finset.univ.erase j, u l * D.tailGen i l) +
        u j * D.tailGen i j = tailDegree D i u at hsplit
      rw [hdeg, huj, one_mul] at hsplit
      omega
    apply Finsupp.ext
    intro l
    by_cases hlj : l = j
    · subst l
      simp [huj]
    · have hlmem : l ∈ Finset.univ.erase j := by simp [hlj]
      have hle : u l * D.tailGen i l ≤
          ∑ x ∈ Finset.univ.erase j, u x * D.tailGen i x := by
        exact Finset.single_le_sum
          (f := fun x : Fin 3 => u x * D.tailGen i x)
          (fun _ _ => Nat.zero_le _) hlmem
      have hlpos := D.tailGen_positive i l
      have hul : u l = 0 := by nlinarith [hle, hrest]
      simp [Finsupp.single_apply, hlj, hul]
  · rintro rfl
    simp

/-- The three-tail polynomial map onto the finite Apéry model is surjective.
@isnad1 id=surjecti.0h3v.s8.7ec1fd06f752 from=translated src=- shape=8ffefe06 vocab=897473bc
-/
theorem tailPolyToApery_surjective :
    Function.Surjective (tailPolyToApery (k := k) D i) := by
  intro x
  induction x using AperyArtin.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      rcases hx with ⟨f, rfl⟩
      rcases hy with ⟨g, rfl⟩
      exact ⟨f + g, by simp⟩
  | single s r =>
      rcases exists_tailExponent_of_isApery D i s.2 with ⟨u, hu⟩
      refine ⟨MvPolynomial.monomial u r, ?_⟩
      rw [tailPolyToApery_monomial]
      simp only [truncatedAperyMonomial]
      split
      · rw [AperyArtin.smul_A]
        congr 2
        apply Subtype.ext
        apply Subtype.ext
        exact hu
      · rename_i hnot
        exfalso
        apply hnot
        have heq : tailDegreeGamma D i u = s.1 := Subtype.ext hu
        exact heq ▸ s.2

/-- The genuine chosen-base tail presentation is surjective.
@isnad1 id=surjecti.0h3v.s9.db49e487126f from=translated src=- shape=8ffefe06 vocab=e34c9fab
-/
theorem tailPolyToChosenBase_surjective :
    Function.Surjective (tailPolyToChosenBase (k := k) D i) := by
  intro q
  rcases tailPolyToApery_surjective (k := k) D i
      ((chosenBaseEquivApery (k := k) D i) q) with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  apply (chosenBaseEquivApery (k := k) D i).injective
  simpa [tailPolyToChosenBase] using hf

/-- Exact arbitrary monomial formula in the genuine quotient, stated through
the quotient/Apéry equivalence.
@isnad1 id=eq.0h5v.s10.939ab4eacb9c from=translated src=- shape=48a57ff2 vocab=2a260d29
-/
theorem tailPolyToChosenBase_monomial (u : Fin 3 →₀ ℕ) (r : k) :
    chosenBaseEquivApery (k := k) D i
        (tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial u r)) =
      r • truncatedAperyMonomial (k := k) D i (tailDegreeGamma D i u) := by
  simpa [tailPolyToChosenBase] using tailPolyToApery_monomial (k := k) D i u r

/-- Every tail variable survives in the genuine quotient.
@isnad1 id=ne.0h4v.s6.56445ca6dad3 from=translated src=- shape=a3c62e80 vocab=8f9ccb0f
-/
theorem tailVariableA_ne_zero (j : Fin 3) :
    tailVariableA (k := k) D i j ≠ 0 := by
  intro h
  have hc := congrArg (fun x : AperyArtin k D i =>
    x.coeff ⟨D.tail i j, D.tail_isApery i j⟩) h
  simpa [tailVariableA] using hc

/--
@isnad1 id=ne.0h4v.s9.2ecbdfcd4d11 from=translated src=- shape=c5986bd8 vocab=768d5bee
-/
theorem tailVariableChosenBase_ne_zero (j : Fin 3) :
    tailPolyToChosenBase (k := k) D i (MvPolynomial.X j) ≠ 0 := by
  intro h
  have he := congrArg (chosenBaseEquivApery (k := k) D i) h
  exact tailVariableA_ne_zero (k := k) D i j (by
    simpa [tailPolyToChosenBase, tailPolyToApery] using he)

/--
@isnad1 id=ne.0h4v.s9.2ecbdfcd4d11 from=translated src=- shape=c5986bd8 vocab=768d5bee
-/
theorem tailVariable_ne_zero (j : Fin 3) :
    tailPolyToChosenBase (k := k) D i (MvPolynomial.X j) ≠ 0 :=
  tailVariableChosenBase_ne_zero (k := k) D i j

/-- The positive-degree augmentation ideal in the Apéry model.-/
def aperyAugmentationIdeal : Ideal (AperyArtin k D i) :=
  Ideal.span {x | ∃ s : D.AperyIndex i,
    s.1 ≠ 0 ∧ x = A (k := k) s.1 s.2}

/-- The actual square of the positive-degree augmentation ideal.-/
def aperyAugmentationSquare : Ideal (AperyArtin k D i) :=
  aperyAugmentationIdeal (k := k) D i ^ 2

/--
@isnad1 id=mem.1h4v.s8.46e5cc8822e9 from=translated src=- shape=2b08e995 vocab=415c92aa
-/
theorem A_mem_aperyAugmentationIdeal (s : D.AperyIndex i) (hs : s.1 ≠ 0) :
    A (k := k) s.1 s.2 ∈ aperyAugmentationIdeal (k := k) D i := by
  apply Ideal.subset_span
  exact ⟨s, hs, rfl⟩

/--
@isnad1 id=mem.0h4v.s7.26d57d23fc8c from=translated src=- shape=1f6816b7 vocab=351e3042
-/
theorem tailVariableA_mem_aperyAugmentationIdeal (j : Fin 3) :
    tailVariableA (k := k) D i j ∈ aperyAugmentationIdeal (k := k) D i := by
  simpa [tailVariableA] using
    A_mem_aperyAugmentationIdeal (k := k) D i
      ⟨D.tail i j, D.tail_isApery i j⟩
      (by
        intro h
        have hv := congrArg Subtype.val h
        simpa [FourGeneratedNumericalSemigroup.tail,
          FourGeneratedNumericalSemigroup.generator] using
          (Nat.ne_of_gt (D.tailGen_positive i j) hv))

/-- The ideal generated by the three surviving tail classes.-/
def tailVariableIdeal : Ideal (AperyArtin k D i) :=
  Ideal.span (Set.range (tailVariableA (k := k) D i))

private theorem truncatedAperyMonomial_mem_tailVariableIdeal_of_ne_zero
    (u : Fin 3 →₀ ℕ) (hu : u ≠ 0) :
    truncatedAperyMonomial (k := k) D i (tailDegreeGamma D i u) ∈
      tailVariableIdeal (k := k) D i := by
  classical
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hu
  have hjpos : 0 < u j := Nat.pos_of_ne_zero hj
  let v : Fin 3 →₀ ℕ := u - Finsupp.single j 1
  have huv : u = Finsupp.single j 1 + v := by
    apply Finsupp.ext
    intro l
    by_cases hlj : l = j
    · subst l
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, v,
        Finsupp.tsub_apply]
      exact (Nat.add_sub_of_le hjpos).symm
    · simp [v, Finsupp.single_apply, hlj]
  rw [huv, tailDegreeGamma_add, truncatedAperyMonomial_add]
  have hsingleGamma :
      tailDegreeGamma D i (Finsupp.single j 1) = D.tail i j := by
    apply Subtype.ext
    simp [tailDegreeGamma, tailDegree_single,
      FourGeneratedNumericalSemigroup.tail,
      FourGeneratedNumericalSemigroup.generator,
      FourGeneratedNumericalSemigroup.tailGen,
      FourGeneratedNumericalSemigroup.tailIndex]
  rw [hsingleGamma, truncatedAperyMonomial_tail]
  exact Ideal.mul_mem_right _ (tailVariableIdeal (k := k) D i)
    (Ideal.subset_span (Set.mem_range_self j))

/-- The positive-degree augmentation ideal is generated by exactly the three
tail-variable classes.
@isnad1 id=eq.0h3v.s5.6fb3925a1e5b from=translated src=- shape=68a591a2 vocab=b1317335
-/
theorem aperyAugmentationIdeal_eq_tailVariableIdeal :
    aperyAugmentationIdeal (k := k) D i = tailVariableIdeal (k := k) D i := by
  apply le_antisymm
  · rw [aperyAugmentationIdeal, Ideal.span_le]
    rintro x ⟨s, hs, rfl⟩
    rcases exists_tailExponent_of_isApery D i s.2 with ⟨u, hu⟩
    have une : u ≠ 0 := by
      intro hz
      subst u
      simp at hu
      exact hs (Subtype.ext hu.symm)
    have hm := truncatedAperyMonomial_mem_tailVariableIdeal_of_ne_zero
      (k := k) D i u une
    have hgamma : tailDegreeGamma D i u = s.1 := Subtype.ext hu
    rw [hgamma, truncatedAperyMonomial, dite_eq_left s.2] at hm
    exact hm
  · rw [tailVariableIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact tailVariableA_mem_aperyAugmentationIdeal (k := k) D i j

/-- Every positive Apéry basis monomial other than one of the three minimal
tail generators lies in the actual square of the augmentation ideal.
@isnad1 id=mem.2h4v.s8.2f986e39b87a from=translated src=- shape=20797651 vocab=772410d1
-/
theorem A_mem_aperyAugmentationSquare_of_ne_tail
    (s : D.AperyIndex i) (hs : s.1 ≠ 0)
    (hnot : ∀ j : Fin 3, s.1 ≠ D.tail i j) :
    A (k := k) s.1 s.2 ∈ aperyAugmentationSquare (k := k) D i := by
  classical
  rcases exists_tailExponent_of_isApery D i s.2 with ⟨u, hu⟩
  have une : u ≠ 0 := by
    intro hz
    subst u
    simp at hu
    exact hs (Subtype.ext hu.symm)
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp une
  have hjpos : 0 < u j := Nat.pos_of_ne_zero hj
  let v : Fin 3 →₀ ℕ := u - Finsupp.single j 1
  have huv : u = Finsupp.single j 1 + v := by
    apply Finsupp.ext
    intro l
    by_cases hlj : l = j
    · subst l
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, v,
        Finsupp.tsub_apply]
      exact (Nat.add_sub_of_le hjpos).symm
    · simp [v, Finsupp.single_apply, hlj]
  have vne : v ≠ 0 := by
    intro hv
    have husingle : u = Finsupp.single j 1 := by simpa [hv] using huv
    have hval : s.1.1 = D.tailGen i j := by
      rw [← hu, husingle, tailDegree_single, one_mul]
    apply hnot j
    apply Subtype.ext
    simpa [FourGeneratedNumericalSemigroup.tail,
      FourGeneratedNumericalSemigroup.generator,
      FourGeneratedNumericalSemigroup.tailGen,
      FourGeneratedNumericalSemigroup.tailIndex] using hval
  have hgamma : tailDegreeGamma D i u = s.1 := Subtype.ext hu
  have hsumApery : D.IsApery i
      (tailDegreeGamma D i (Finsupp.single j 1) + tailDegreeGamma D i v) := by
    rw [← tailDegreeGamma_add, ← huv, hgamma]
    exact s.2
  have hvApery : D.IsApery i (tailDegreeGamma D i v) :=
    AperyArtin.isApery_of_add_right hsumApery
  have hsingleGamma :
      tailDegreeGamma D i (Finsupp.single j 1) = D.tail i j := by
    apply Subtype.ext
    simp [tailDegreeGamma, tailDegree_single,
      FourGeneratedNumericalSemigroup.tail,
      FourGeneratedNumericalSemigroup.generator,
      FourGeneratedNumericalSemigroup.tailGen,
      FourGeneratedNumericalSemigroup.tailIndex]
  have hfactor :
      A (k := k) s.1 s.2 =
        tailVariableA (k := k) D i j *
          A (k := k) (tailDegreeGamma D i v) hvApery := by
    rw [← truncatedAperyMonomial_tail, ← hsingleGamma,
      ← show truncatedAperyMonomial (k := k) D i (tailDegreeGamma D i v) =
        A (k := k) (tailDegreeGamma D i v) hvApery by
          simp [truncatedAperyMonomial, hvApery],
      ← truncatedAperyMonomial_add]
    rw [← tailDegreeGamma_add, ← huv, hgamma]
    simp [truncatedAperyMonomial, s.2]
  rw [hfactor, aperyAugmentationSquare, pow_two]
  exact Ideal.mul_mem_mul
    (tailVariableA_mem_aperyAugmentationIdeal (k := k) D i j)
    (A_mem_aperyAugmentationIdeal (k := k) D i
      ⟨tailDegreeGamma D i v, hvApery⟩
      (by
        intro hz
        apply vne
        apply Finsupp.ext
        intro l
        have hnonneg : v l * D.tailGen i l ≤ tailDegree D i v := by
          apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
        have hdegzero : tailDegree D i v = 0 := by
          simpa [tailDegreeGamma] using congrArg Subtype.val hz
        have hpos := D.tailGen_positive i l
        simp only [Finsupp.zero_apply]
        nlinarith))

/-- Coefficient of a tail basis vector.-/
def tailCoeff (j : Fin 3) : AperyArtin k D i →ₗ[k] k where
  toFun x := x.coeff ⟨D.tail i j, D.tail_isApery i j⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/--
@isnad1 id=eq.0h5v.s8.bad553f65e39 from=translated src=- shape=5ca6bc86 vocab=b2e07820
-/
@[simp] theorem tailCoeff_tailVariable (j l : Fin 3) :
    tailCoeff (k := k) D i j (tailVariableA (k := k) D i l) =
      if j = l then 1 else 0 := by
  classical
  change (A (k := k) (D.tail i l) (D.tail_isApery i l)).coeff
    ⟨D.tail i j, D.tail_isApery i j⟩ = _
  rw [coeff_A]
  by_cases hjl : j = l
  · subst l
    simp
  · have htail : D.tail i j ≠ D.tail i l := by
      intro h
      apply hjl
      apply D.tailGen_injective i
      exact congrArg Subtype.val h
    simp [hjl, htail]

/--
@isnad1 id=eq.2h6v.s9.420f0f2b2e09 from=translated src=- shape=efc3f232 vocab=dcbb4969
-/
theorem positive_basis_mul_tailCoeff_zero
    (p q : D.AperyIndex i) (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) (j : Fin 3) :
    tailCoeff (k := k) D i j
      (A (k := k) p.1 p.2 * A (k := k) q.1 q.2) = 0 := by
  classical
  rw [A_mul_A]
  split
  · rename_i hpq
    change (A (k := k) (p.1 + q.1) hpq).coeff
      ⟨D.tail i j, D.tail_isApery i j⟩ = 0
    rw [coeff_A]
    by_cases heq : D.tail i j = p.1 + q.1
    · simp only [ite_eq_left heq]
      exfalso
      rcases (D.mem_Gamma_iff p.1.1).1 p.1.2 with ⟨up, hup⟩
      rcases (D.mem_Gamma_iff q.1.1).1 q.1.2 with ⟨uq, huq⟩
      let tj := D.tailIndex i j
      have hsumdeg : D.weightedDegree (up + uq) = D.n tj := by
        change weightedDegreeOf D.n (up + uq) = D.n tj
        rw [weightedDegreeOf_add]
        change D.weightedDegree up + D.weightedDegree uq = D.n tj
        rw [hup, huq]
        have hv := congrArg (fun z : D.Gamma => z.1) heq
        simpa [FourGeneratedNumericalSemigroup.tail,
          FourGeneratedNumericalSemigroup.generator, tj] using hv.symm
      have hcoord : (up + uq) tj ≠ 0 := by
        intro hz
        exact D.minimal tj (up + uq) hz hsumdeg
      have hcases : up tj ≠ 0 ∨ uq tj ≠ 0 := by
        by_cases hz : up tj = 0
        · right
          intro hzq
          apply hcoord
          simp [hz, hzq]
        · exact Or.inl hz
      rcases hcases with hupj | huqj
      · have hterm : up tj * D.n tj ≤ D.weightedDegree up := by
          change up tj * D.n tj ≤ weightedDegreeOf D.n up
          apply Finset.single_le_sum
            (f := fun x : Fin 4 => up x * D.n x)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ tj)
        have hge : D.n tj ≤ p.1.1 := by
          have hpos : 1 ≤ up tj := Nat.one_le_iff_ne_zero.2 hupj
          have hmul : D.n tj ≤ up tj * D.n tj := by
            simpa using Nat.mul_le_mul_right (D.n tj) hpos
          omega
        have hqnat : q.1.1 ≠ 0 := by
          intro hz
          apply hq
          exact Subtype.ext hz
        have hqpos : 0 < q.1.1 := Nat.pos_of_ne_zero hqnat
        have hv := congrArg (fun z : D.Gamma => z.1) heq
        have hgen := D.tailGen_positive i j
        simp [FourGeneratedNumericalSemigroup.tail,
          FourGeneratedNumericalSemigroup.generator, tj] at hv
        change D.n (i.succAbove j) ≤ p.1.1 at hge
        omega
      · have hterm : uq tj * D.n tj ≤ D.weightedDegree uq := by
          change uq tj * D.n tj ≤ weightedDegreeOf D.n uq
          apply Finset.single_le_sum
            (f := fun x : Fin 4 => uq x * D.n x)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ tj)
        have hge : D.n tj ≤ q.1.1 := by
          have hpos : 1 ≤ uq tj := Nat.one_le_iff_ne_zero.2 huqj
          have hmul : D.n tj ≤ uq tj * D.n tj := by
            simpa using Nat.mul_le_mul_right (D.n tj) hpos
          omega
        have hpnat : p.1.1 ≠ 0 := by
          intro hz
          apply hp
          exact Subtype.ext hz
        have hppos : 0 < p.1.1 := Nat.pos_of_ne_zero hpnat
        have hv := congrArg (fun z : D.Gamma => z.1) heq
        simp [FourGeneratedNumericalSemigroup.tail,
          FourGeneratedNumericalSemigroup.generator, tj] at hv
        change D.n (i.succAbove j) ≤ q.1.1 at hge
        omega
    · simp [heq]
  · simp [tailCoeff]

/-- Degree-zero coefficient in the Apéry basis.-/
def aperyConstantCoeff : AperyArtin k D i →ₗ[k] k where
  toFun x := x.coeff ⟨0, D.zero_isApery i⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/--
@isnad1 id=eq.1h4v.s8.615fde091a09 from=translated src=- shape=10258026 vocab=f9b4212b
-/
@[simp] theorem aperyConstantCoeff_A (s : D.Gamma) (hs : D.IsApery i s) :
    aperyConstantCoeff (k := k) D i (A (k := k) s hs) =
      if s = 0 then 1 else 0 := by
  classical
  change (A (k := k) s hs).coeff ⟨0, D.zero_isApery i⟩ = _
  rw [coeff_A]
  simp [eq_comm]

/-- First-order coefficient map: degree-zero term together with the three tail
coefficients, valued in the trivial square-zero extension.-/
def aperyFirstOrderLinear :
    AperyArtin k D i →ₗ[k] TrivSqZeroExt k (Fin 3 → k) where
  toFun x := (aperyConstantCoeff (k := k) D i x,
    fun j => tailCoeff (k := k) D i j x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h4v.s9.930366b0f0cb from=translated src=- shape=25389dd8 vocab=72748b57
-/
@[simp] theorem aperyFirstOrderLinear_fst (x : AperyArtin k D i) :
    (aperyFirstOrderLinear (k := k) D i x).fst =
      aperyConstantCoeff (k := k) D i x := rfl

/--
@isnad1 id=eq.0h5v.s9.765c0620c871 from=translated src=- shape=4ff13cde vocab=99a6b74c
-/
@[simp] theorem aperyFirstOrderLinear_snd (x : AperyArtin k D i) (j : Fin 3) :
    (aperyFirstOrderLinear (k := k) D i x).snd j =
      tailCoeff (k := k) D i j x := rfl

/--
@isnad1 id=eq.0h3v.s9.f4ad79475146 from=translated src=- shape=c138560d vocab=36b4698e
-/
@[simp] theorem aperyFirstOrderLinear_one :
    aperyFirstOrderLinear (k := k) D i (1 : AperyArtin k D i) = 1 := by
  apply TrivSqZeroExt.ext
  · change (A (k := k) 0 (D.zero_isApery i)).coeff
      ⟨0, D.zero_isApery i⟩ = 1
    simp [coeff_A]
  · funext j
    change (A (k := k) 0 (D.zero_isApery i)).coeff
      ⟨D.tail i j, D.tail_isApery i j⟩ = 0
    rw [coeff_A]
    have hne : D.tail i j ≠ 0 := by
      intro h
      have hv := congrArg Subtype.val h
      simpa [FourGeneratedNumericalSemigroup.tail,
        FourGeneratedNumericalSemigroup.generator] using
        (Nat.ne_of_gt (D.tailGen_positive i j) hv)
    simp [hne]

private theorem positive_basis_mul_constantCoeff_zero
    (p q : D.AperyIndex i) (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) :
    aperyConstantCoeff (k := k) D i
      (A (k := k) p.1 p.2 * A (k := k) q.1 q.2) = 0 := by
  classical
  rw [A_mul_A]
  split
  · rename_i hpq
    rw [aperyConstantCoeff_A]
    split
    · rename_i hzero
      have hv := congrArg (fun z : D.Gamma => z.1) hzero
      have hpval : p.1.1 ≠ 0 := fun hz => hp (Subtype.ext hz)
      have hqval : q.1.1 ≠ 0 := fun hz => hq (Subtype.ext hz)
      simp only [AddSubmonoid.coe_add, AddSubmonoid.coe_zero] at hv
      omega
    · rfl
  · simp [aperyConstantCoeff]

private theorem aperyFirstOrderLinear_A_mul_A
    (p q : D.AperyIndex i) :
    aperyFirstOrderLinear (k := k) D i
        (A (k := k) p.1 p.2 * A (k := k) q.1 q.2) =
      aperyFirstOrderLinear (k := k) D i (A (k := k) p.1 p.2) *
        aperyFirstOrderLinear (k := k) D i (A (k := k) q.1 q.2) := by
  classical
  by_cases hp : p.1 = 0
  · have peq : p = ⟨0, D.zero_isApery i⟩ := Subtype.ext hp
    subst p
    have hA0 : A (k := k) (⟨0, D.zero_isApery i⟩ : D.AperyIndex i).1
        (⟨0, D.zero_isApery i⟩ : D.AperyIndex i).2 =
        (1 : AperyArtin k D i) := rfl
    rw [hA0, one_mul, aperyFirstOrderLinear_one, one_mul]
  · by_cases hq : q.1 = 0
    · have qeq : q = ⟨0, D.zero_isApery i⟩ := Subtype.ext hq
      subst q
      have hA0 : A (k := k) (⟨0, D.zero_isApery i⟩ : D.AperyIndex i).1
          (⟨0, D.zero_isApery i⟩ : D.AperyIndex i).2 =
          (1 : AperyArtin k D i) := rfl
      rw [hA0, mul_one, aperyFirstOrderLinear_one, mul_one]
    · apply TrivSqZeroExt.ext
      · change aperyConstantCoeff (k := k) D i
            (A (k := k) p.1 p.2 * A (k := k) q.1 q.2) =
          aperyConstantCoeff (k := k) D i (A (k := k) p.1 p.2) *
            aperyConstantCoeff (k := k) D i (A (k := k) q.1 q.2)
        rw [positive_basis_mul_constantCoeff_zero (k := k) D i p q hp hq]
        simp [aperyConstantCoeff_A, hp, hq]
      · funext j
        have hz := positive_basis_mul_tailCoeff_zero (k := k) D i p q hp hq j
        change tailCoeff (k := k) D i j
            (A (k := k) p.1 p.2 * A (k := k) q.1 q.2) = _
        rw [hz]
        simp [aperyConstantCoeff_A, hp, hq]

/-- The first-order coefficient map is an algebra homomorphism.  This is the
symbolic detector for the actual augmentation square.-/
def aperyFirstOrderAlgHom :
    AperyArtin k D i →ₐ[k] TrivSqZeroExt k (Fin 3 → k) where
  toFun := aperyFirstOrderLinear (k := k) D i
  map_zero' := (aperyFirstOrderLinear (k := k) D i).map_zero
  map_add' := (aperyFirstOrderLinear (k := k) D i).map_add
  map_one' := aperyFirstOrderLinear_one (k := k) D i
  map_mul' x y := by
    classical
    induction x using AperyArtin.induction_linear with
    | zero => simp [aperyFirstOrderLinear]
    | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
    | single p rp =>
      induction y using AperyArtin.induction_linear with
      | zero => simp [aperyFirstOrderLinear]
      | add y₁ y₂ hy₁ hy₂ => simp [mul_add, hy₁, hy₂]
      | single q rq =>
        rw [← AperyArtin.smul_A rp, ← AperyArtin.smul_A rq]
        simp only [AperyArtin.smul_mul_raw, AperyArtin.mul_smul_raw,
          LinearMap.map_smul]
        rw [aperyFirstOrderLinear_A_mul_A (k := k) D i p q]
        simp [smul_mul_assoc, mul_smul_comm]
  commutes' r := by
    change aperyFirstOrderLinear (k := k) D i
      (algebraMap k (AperyArtin k D i) r) = _
    rw [Algebra.algebraMap_eq_smul_one,
      (aperyFirstOrderLinear (k := k) D i).map_smul,
      aperyFirstOrderLinear_one]
    simp [Algebra.algebraMap_eq_smul_one]

/--
@isnad1 id=eq.0h4v.s9.c291e7e5a389 from=translated src=- shape=3f4fc058 vocab=b19c104a
-/
theorem aperyFirstOrder_tail_fst (j : Fin 3) :
    (aperyFirstOrderAlgHom (k := k) D i
      (tailVariableA (k := k) D i j)).fst = 0 := by
  change aperyConstantCoeff (k := k) D i
    (tailVariableA (k := k) D i j) = 0
  simp [tailVariableA, aperyConstantCoeff_A]
  have hne : D.tail i j ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    simpa [FourGeneratedNumericalSemigroup.tail,
      FourGeneratedNumericalSemigroup.generator] using
      (Nat.ne_of_gt (D.tailGen_positive i j) hv)
  simp [hne]

/--
@isnad1 id=eq.0h5v.s9.ba5ee89454da from=translated src=- shape=1a3c4eb7 vocab=182bb11b
-/
@[simp] theorem aperyFirstOrder_tail_snd (j l : Fin 3) :
    (aperyFirstOrderAlgHom (k := k) D i
      (tailVariableA (k := k) D i l)).snd j =
      if j = l then 1 else 0 := by
  exact tailCoeff_tailVariable (k := k) D i j l

/--
@isnad1 id=le.0h3v.s10.3c3951fa4fd6 from=translated src=- shape=69633487 vocab=109534dc
-/
theorem aperyAugmentationIdeal_le_firstOrder_kerIdeal :
    aperyAugmentationIdeal (k := k) D i ≤
      Ideal.comap (aperyFirstOrderAlgHom (k := k) D i).toRingHom
        (TrivSqZeroExt.kerIdeal k (Fin 3 → k)) := by
  rw [aperyAugmentationIdeal_eq_tailVariableIdeal, tailVariableIdeal,
    Ideal.span_le]
  rintro x ⟨j, rfl⟩
  change aperyFirstOrderAlgHom (k := k) D i
      (tailVariableA (k := k) D i j) ∈
    TrivSqZeroExt.kerIdeal k (Fin 3 → k)
  rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
  apply TrivSqZeroExt.ext
  · simp [aperyFirstOrder_tail_fst]
  · rfl

/-- Every element of the actual augmentation square has zero first-order
image.
@isnad1 id=eq.1h4v.s9.ff70b2a572f7 from=translated src=- shape=4e7f7bb6 vocab=a476150d
-/
theorem aperyFirstOrder_eq_zero_of_mem_square
    {x : AperyArtin k D i}
    (hx : x ∈ aperyAugmentationSquare (k := k) D i) :
    aperyFirstOrderAlgHom (k := k) D i x = 0 := by
  let F := aperyFirstOrderAlgHom (k := k) D i
  let I := aperyAugmentationIdeal (k := k) D i
  let K := TrivSqZeroExt.kerIdeal k (Fin 3 → k)
  have hI : Ideal.map F.toRingHom I ≤ K :=
    (Ideal.map_le_iff_le_comap).2
      (aperyAugmentationIdeal_le_firstOrder_kerIdeal (k := k) D i)
  have hxmap : F x ∈ Ideal.map F.toRingHom (I ^ 2) := by
    apply Ideal.mem_map_of_mem
    simpa [I, aperyAugmentationSquare] using hx
  rw [Ideal.map_pow] at hxmap
  have hpow : Ideal.map F.toRingHom I ^ 2 ≤ K ^ 2 := by
    gcongr
  have hxK : F x ∈ K ^ 2 := hpow hxmap
  simpa [K, TrivSqZeroExt.kerIdeal_sq] using hxK

/-- Each of the three tail-variable classes is nonzero in the actual
cotangent quotient: it is not contained in the augmentation square.
@isnad1 id=not.0h4v.s7.6b5b9fcc2b51 from=translated src=- shape=0319a53b vocab=d51f3a8e
-/
theorem tailVariableA_not_mem_aperyAugmentationSquare (j : Fin 3) :
    tailVariableA (k := k) D i j ∉ aperyAugmentationSquare (k := k) D i := by
  intro hj
  have hz := aperyFirstOrder_eq_zero_of_mem_square (k := k) D i hj
  have hsnd := congrArg (fun z : TrivSqZeroExt k (Fin 3 → k) => z.snd j) hz
  simpa using hsnd

/-- Exact linear-independence test modulo the actual augmentation square.
@isnad1 id=iff.0h4v.s8.231c7bd33bdb from=translated src=- shape=123b7862 vocab=ed008e5a
-/
theorem tail_linearCombination_mem_aperyAugmentationSquare_iff
    (c : Fin 3 → k) :
    (∑ j : Fin 3, c j • tailVariableA (k := k) D i j) ∈
        aperyAugmentationSquare (k := k) D i ↔
      ∀ j, c j = 0 := by
  constructor
  · intro h j
    have hz := aperyFirstOrder_eq_zero_of_mem_square (k := k) D i h
    have hcalc :
        (aperyFirstOrderAlgHom (k := k) D i
          (∑ l : Fin 3, c l • tailVariableA (k := k) D i l)).snd j = c j := by
      rw [map_sum]
      change ((TrivSqZeroExt.sndHom k (Fin 3 → k))
        (∑ l : Fin 3, c l • aperyFirstOrderAlgHom (k := k) D i
          (tailVariableA (k := k) D i l))) j = c j
      rw [map_sum]
      simp [aperyFirstOrder_tail_snd]
    have hsnd := congrArg
      (fun z : TrivSqZeroExt k (Fin 3 → k) => z.snd j) hz
    rw [hcalc] at hsnd
    simpa using hsnd
  · intro hc
    simp [hc]

/-- The coefficient-level cotangent model, indexed by the three tail
variables.-/
abbrev ChosenBaseCotangentModel := Fin 3 → k

/-- The coordinate model used by the exact cotangent basis theorem has
dimension three.
@isnad1 id=eq.0h1v.s6.543b4db68ba4 from=translated src=- shape=a4033e76 vocab=44fbcea0
-/
theorem chosenBase_cotangentModel_finrank :
    Module.finrank k (ChosenBaseCotangentModel (k := k)) = 3 := by
  exact Module.finrank_fin_fun k

/-- An exact basis theorem for the genuine cotangent space, expressed without
replacing the actual ideals by a definition.  The first field identifies the
maximal/augmentation ideal with the three-tail ideal; the second says that a
tail linear combination lies in the actual square exactly when all three
coefficients vanish; the third places every other positive Apéry basis class
in that square.  Thus the images of the ordered `Fin 3` tail family are a
basis of `m/m²`.-/
structure ChosenBaseCotangentBasis : Prop where
  augmentation_eq_tail_span :
    aperyAugmentationIdeal (k := k) D i = tailVariableIdeal (k := k) D i
  tail_independent_mod_square : ∀ c : Fin 3 → k,
    (∑ j : Fin 3, c j • tailVariableA (k := k) D i j) ∈
        aperyAugmentationSquare (k := k) D i ↔
      ∀ j, c j = 0
  positive_non_tail_mem_square : ∀ (s : D.AperyIndex i), s.1 ≠ 0 →
    (∀ j : Fin 3, s.1 ≠ D.tail i j) →
      A (k := k) s.1 s.2 ∈ aperyAugmentationSquare (k := k) D i

/-- Exact embedding-dimension-three foundation for the chosen-base quotient,
in the permitted equivalent-basis form indexed by `Fin 3`.
@isnad1 id=chosenba.0h3v.s4.7d0e3d6f8a06 from=translated src=- shape=9b42ccea vocab=5919523c
-/
theorem chosenBase_embeddingDimension_eq_three :
    ChosenBaseCotangentBasis (k := k) D i where
  augmentation_eq_tail_span :=
    aperyAugmentationIdeal_eq_tailVariableIdeal (k := k) D i
  tail_independent_mod_square :=
    tail_linearCombination_mem_aperyAugmentationSquare_iff (k := k) D i
  positive_non_tail_mem_square :=
    A_mem_aperyAugmentationSquare_of_ne_tail (k := k) D i

/-- The genuine chosen-base defining ideal `J_q`.-/
def chosenBaseDefiningIdeal : Ideal (TailPoly k) :=
  RingHom.ker (tailPolyToChosenBase (k := k) D i).toRingHom

/-- Exact polynomial quotient presentation of the chosen-base algebra.-/
def tailPolynomialQuotientEquiv :
    (TailPoly k ⧸ chosenBaseDefiningIdeal (k := k) D i) ≃ₐ[k]
      ChosenBaseQuotient (k := k) D i :=
  Ideal.quotientKerAlgEquivOfSurjective
    (tailPolyToChosenBase_surjective (k := k) D i)

/-- Scope-explicit Run20 boundary object.  The embedding-dimension witness is
the ordered surviving minimal tail family; no Betti or NG data is included.-/
structure ChosenBaseFoundation where
  quotientEquiv : ChosenBaseQuotient (k := k) D i ≃ₐ[k] AperyArtin k D i
  tailSurjective : Function.Surjective (tailPolyToChosenBase (k := k) D i)
  tailSurvives : ∀ j, tailPolyToChosenBase (k := k) D i (MvPolynomial.X j) ≠ 0
  embeddingDimensionThree : ChosenBaseCotangentBasis (k := k) D i

/-- Stable chosen-base foundation package.-/
def chosenBaseFoundation : ChosenBaseFoundation (k := k) D i where
  quotientEquiv := chosenBaseEquivApery (k := k) D i
  tailSurjective := tailPolyToChosenBase_surjective (k := k) D i
  tailSurvives := tailVariableChosenBase_ne_zero (k := k) D i
  embeddingDimensionThree := chosenBase_embeddingDimension_eq_three (k := k) D i

end

end P23.Semigroup
