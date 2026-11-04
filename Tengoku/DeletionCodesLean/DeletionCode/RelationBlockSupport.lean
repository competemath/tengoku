import Tengoku.DeletionCodesLean.DeletionCode.RelationSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms partial_sum_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms block_restriction_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms connected_block_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms connected_block_meets_relation` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The nonzero restriction step in the relation case of bounded witness extraction.
Linear independence makes every partial combination with an active coefficient
nonzero. A whole adjacency block has disjoint gram support from its complement,
so a nonzero coordinate of that restriction survives in the full relation.
Neither survival nor a nonzero restricted vector is an input assumption.
-/

namespace DeletionCode.RelationBlockSupport

open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

/-- A finite partial combination of independent rational vectors with at least
one nonzero coefficient has an actual nonzero coordinate.
@isnad1 id=ex.2h5v.s6.2c871633030a from=translated src=- shape=8170878d vocab=d8097961
-/
theorem partial_sum_nonzero {I H : Type*} (G : I → H → ℚ)
    (hG : LinearIndependent ℚ G) (T : Finset I) (a : I → ℚ)
    (hactive : ∃ i ∈ T, a i ≠ 0) :
    ∃ g, (∑ i ∈ T, a i * G i g) ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : (∑ i ∈ T, a i • G i) = 0 := by
    funext g
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using hnone g
  obtain ⟨i, hi, hai⟩ := hactive
  exact hai ((linearIndependent_iff'.mp hG) T a hzero i hi)

/-- The commonly used nonempty, everywhere nonzero coefficient version.
@isnad1 id=ex.3h5v.s6.ca6014cf3745 from=translated src=- shape=b86f25fc vocab=fd9b5462
-/
theorem partial_sum_nonzero_of_nonempty {I H : Type*} (G : I → H → ℚ)
    (hG : LinearIndependent ℚ G) (T : Finset I) (a : I → ℚ)
    (hT : T.Nonempty) (ha : ∀ i ∈ T, a i ≠ 0) :
    ∃ g, (∑ i ∈ T, a i * G i g) ≠ 0 := by
  obtain ⟨i, hi⟩ := hT
  exact partial_sum_nonzero G hG T a ⟨i, hi, ha i hi⟩

/-- At a coordinate vanishing outside T, the full relation equals its actual
finite restriction to T.
@isnad1 id=eq.2h7v.s6.c59a6e429120 from=translated src=- shape=5fd6ce8b vocab=97c8e559
-/
theorem restriction_eq_at {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : RelationSupport.Relation G w a) (T : Finset I) (g : Gram L)
    (houtside : ∀ i, i ∉ T → G i g = 0) :
    (w g : ℚ) = ∑ i ∈ T, a i * (G i g : ℚ) := by
  classical
  rw [hrel g]
  symm
  apply Finset.sum_subset (Finset.subset_univ T)
  intro i _ hi
  simp [houtside i hi]

/-- Every nonzero partial coordinate is supported by an actual selected rule.
@isnad1 id=ex.1h6v.s6.5ec0208917a4 from=translated src=- shape=34cc6263 vocab=84e3bc1c
-/
theorem partial_support {I : Type*} {L : ℕ}
    (G : I → Gram L → ℤ) (T : Finset I) (a : I → ℚ) (g : Gram L)
    (hne : (∑ i ∈ T, a i * (G i g : ℚ)) ≠ 0) :
    ∃ i ∈ T, G i g ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  apply hne
  apply Finset.sum_eq_zero
  intro i hi
  simp [hnone i hi]

/-- An actual gram supported in a whole adjacency block is absent from every
rule outside that block. The same holds for any union of whole blocks.
@isnad1 id=eq.3h6v.s6.975549efda8f from=translated src=- shape=31ac593c vocab=ea8c687e
-/
theorem outside_block_vanishes {I : Type*} {L : ℕ}
    (G : I → Gram L → ℤ) (T : Finset I)
    (hclosed : BlockClosed G (↑T : Set I)) (g : Gram L)
    (hsupport : ∃ i ∈ T, G i g ≠ 0) :
    ∀ j, j ∉ T → G j g = 0 := by
  obtain ⟨i, hi, hgi⟩ := hsupport
  intro j hj
  by_contra hgj
  exact hj (hclosed i hi j
    (Relation.EqvGen.rel i j (common_gram_adjacent G i j g hgi hgj)))

/-- A block restriction containing an active coefficient has a nonzero actual
gram that survives in w. Whole-block closure supplies the separation premise.
@isnad1 id=ex.4h6v.s7.49e02aa51ef2 from=translated src=- shape=4354cd03 vocab=943dd49c
-/
theorem block_restriction_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (T : Finset I)
    (hactive : ∃ i ∈ T, a i ≠ 0)
    (hclosed : BlockClosed G (↑T : Set I)) :
    ∃ g, w g ≠ 0 ∧ ∃ i ∈ T, G i g ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := partial_sum_nonzero (fun i g => (G i g : ℚ)) hG T a hactive
  have hs := partial_support G T a g hg
  have heq := restriction_eq_at G w a hrel T g
    (outside_block_vanishes G T hclosed g hs)
  refine ⟨g, ?_, hs⟩
  intro hw
  apply hg
  simpa only [hw, Int.cast_zero] using heq.symm

/-- Each actual EqvGen adjacency block meeting the nonzero coefficient support
meets the nonzero support of w at a gram of a rule in that same block.
@isnad1 id=ex.3h6v.s7.800022c42b1b from=translated src=- shape=fe20b170 vocab=c9902637
-/
theorem connected_block_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (b : I)
    (hactive : ∃ i, Connected G b i ∧ a i ≠ 0) :
    ∃ g i, Connected G b i ∧ G i g ≠ 0 ∧ w g ≠ 0 := by
  classical
  let T : Finset I := Finset.univ.filter (fun i => Connected G b i)
  have hmem (i : I) : i ∈ T ↔ Connected G b i := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have hT : ∃ i ∈ T, a i ≠ 0 := by
    obtain ⟨i, hi, ha⟩ := hactive
    exact ⟨i, (hmem i).mpr hi, ha⟩
  have hclosed : BlockClosed G (↑T : Set I) := by
    intro i hi j hij
    exact (hmem j).mpr (Relation.EqvGen.trans b i j ((hmem i).mp hi) hij)
  obtain ⟨g, hw, i, hi, hgi⟩ :=
    block_restriction_nonzero G w a hG hrel T hT hclosed
  exact ⟨g, i, (hmem i).mp hi, hgi, hw⟩

/-- The surviving gram provides an actual incident support vertex shared with
w, ready for the block/component counting step.
@isnad1 id=ex.3h6v.s7.ecf5732f3772 from=translated src=- shape=9e59cead vocab=0df5fb8a
-/
theorem connected_block_meets_relation {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (b : I)
    (hactive : ∃ i, Connected G b i ∧ a i ≠ 0) :
    ∃ i, Connected G b i ∧ ∃ v, Incident {G i} v ∧ Incident {w} v := by
  obtain ⟨g, i, hi, hgi, hw⟩ := connected_block_nonzero G w a hG hrel b hactive
  exact ⟨i, hi, gramPrefix g, nonzero_incident (G i) g hgi,
    nonzero_incident w g hw⟩

end DeletionCode.RelationBlockSupport
