import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.NormalizedRootSwap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ResidualSectionTwoPointFibreTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Fibres of the normalized residual section

The base coordinates are the retained matrix `M` and symmetric root sum
`Sb`.  The section quadratic factors through the actual root `Delta` and the
derived root `DeltaStar`.  Consequently every section point above the same
base is either the given point or its normalized-section root swap.  The two
points are asserted distinct only under the explicit branch hypothesis
`Delta ≠ DeltaStar`.

This is a coefficient-field statement about an explicit normalized section.
It is not a function-field degree, connected cover, finite-etale morphism,
global quotient, deck transformation, Albert, or physics result.
-/

namespace AlbertLean.Residual.SectionFibre

open Set
open AlbertLean.Residual.NormalizedRootSwap

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The scalar quadratic attached to a normalized section point.-/
def sectionPolynomial (s : NormalizedResidualSection K) (z : K) : K :=
  z ^ 2 - Sb s * z + Matrix.det s.M

/-- Exact factorization through the actual and derived determinant roots.
@isnad1 id=eq.0h3v.s6.ddb7b1760924 from=translated src=- shape=3863980e vocab=54a45c4c
-/
theorem sectionPolynomial_factor (s : NormalizedResidualSection K) (z : K) :
    sectionPolynomial s z = (z - s.Delta) * (z - DeltaStar s) := by
  rw [sectionPolynomial, Sb, ← Delta_mul_DeltaStar s]
  ring

/-- Every scalar root is one of the two displayed roots, with no distinctness
claim at the repeated-root locus.
@isnad1 id=iff.0h3v.s5.b323b75b3f7a from=translated src=- shape=d5036ee7 vocab=1b33bfa9
-/
theorem sectionPolynomial_eq_zero_iff
    (s : NormalizedResidualSection K) (z : K) :
    sectionPolynomial s z = 0 ↔ z = s.Delta ∨ z = DeltaStar s := by
  rw [sectionPolynomial_factor]
  simp only [mul_eq_zero, sub_eq_zero]

/-- Two normalized section points lie over the same explicit base when they
have the same matrix and the same symmetric root sum.-/
def SameBase (s t : NormalizedResidualSection K) : Prop :=
  t.M = s.M ∧ Sb t = Sb s

/-- The explicit fibre over `(M,Sb)`.-/
def sectionFibre (s : NormalizedResidualSection K) :
    Set (NormalizedResidualSection K) :=
  {t | SameBase s t}

/-- A point in the same normalized base fibre is the original point or its
section root swap.
@isnad1 id=iff.0h3v.s5.50c8da80d852 from=translated src=- shape=33629597 vocab=a62a0b44
-/
theorem sameBase_iff_eq_or_eq_rootSwap
    (s t : NormalizedResidualSection K) :
    SameBase s t ↔ t = s ∨ t = rootSwap s := by
  constructor
  · intro hbase
    have htRoot : sectionPolynomial s t.Delta = 0 := by
      have ht := Delta_root_relation t
      rw [hbase.1, hbase.2] at ht
      exact ht
    rcases (sectionPolynomial_eq_zero_iff s t.Delta).mp htRoot with h | h
    · left
      apply NormalizedResidualSection.ext
      · exact hbase.1
      · exact h
    · right
      apply NormalizedResidualSection.ext
      · simpa using hbase.1
      · simpa using h
  · rintro (rfl | rfl)
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rootSwap_Sb s⟩

/-- The complete normalized fibre is the unordered pair consisting of a
point and its section root swap.  This set may be a singleton at a repeated
root.
@isnad1 id=eq.0h2v.s5.d33c5602f588 from=translated src=- shape=f66c60a1 vocab=3a1c4f0f
-/
theorem sectionFibre_eq_pair (s : NormalizedResidualSection K) :
    sectionFibre s = {s, rootSwap s} := by
  ext t
  simp only [sectionFibre, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  exact sameBase_iff_eq_or_eq_rootSwap s t

/-- The explicit branch hypothesis makes the two displayed section points
distinct.
@isnad1 id=ne.1h2v.s4.07f35e843f09 from=translated src=- shape=09206d4c vocab=3bed4afc
-/
theorem self_ne_rootSwap (s : NormalizedResidualSection K)
    (hbranch : s.Delta ≠ DeltaStar s) :
    s ≠ rootSwap s := by
  intro h
  apply hbranch
  have hDelta := congrArg NormalizedResidualSection.Delta h
  simpa using hDelta

/-- exact two-point classification of
the normalized `(M,Sb)` fibre on the branch-free locus.
@isnad1 id=and.1h2v.s7.4c6e84a7c745 from=translated src=- shape=34497230 vocab=cece229c
-/
theorem ResidualSectionTwoPointFibreTheorem
    (s : NormalizedResidualSection K)
    (hbranch : s.Delta ≠ DeltaStar s) :
    (∀ z : K,
      sectionPolynomial s z = (z - s.Delta) * (z - DeltaStar s)) ∧
      (∀ z : K,
        sectionPolynomial s z = 0 ↔ z = s.Delta ∨ z = DeltaStar s) ∧
      sectionFibre s = {s, rootSwap s} ∧
      s ≠ rootSwap s := by
  exact ⟨sectionPolynomial_factor s, sectionPolynomial_eq_zero_iff s,
    sectionFibre_eq_pair s, self_ne_rootSwap s hbranch⟩

end

end AlbertLean.Residual.SectionFibre
