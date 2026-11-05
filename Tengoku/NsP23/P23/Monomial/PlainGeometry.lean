import Tengoku.Seed.Data.Finsupp.Interval
import Tengoku.Seed.Data.Finsupp.Order
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Data.Finset.Union
import Tengoku.Seed.Data.Set.Finite.Lattice
import Tengoku.Seed.Order.Interval.Finset.Nat
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordinary three-variable monomial geometry, with no tie or wrapping. -/
namespace P23.Monomial
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev PlainExp := Fin 3 →₀ ℕ
def plainUnitVector (j : Fin 3) : PlainExp := Finsupp.single j 1
def plainDivides (p q : PlainExp) : Prop := ∀ j, p j ≤ q j
def plainStandardSet (R : Finset PlainExp) : Set PlainExp :=
  {p | ∃ s ∈ R, plainDivides p s}
def PlainRootAntichain (R : Finset PlainExp) : Prop :=
  ∀ p ∈ R, ∀ q ∈ R, plainDivides p q → p = q
def PlainVariablesSurvive (R : Finset PlainExp) : Prop :=
  ∀ j : Fin 3, plainUnitVector j ∈ plainStandardSet R
def plainPredecessor (j : Fin 3) (p : PlainExp) : PlainExp := p - plainUnitVector j

theorem plainDivides_refl (p : PlainExp) : plainDivides p p := fun _ => le_rfl
theorem plainDivides_trans {p q r : PlainExp} (h : plainDivides p q)
    (h' : plainDivides q r) : plainDivides p r := fun j => le_trans (h j) (h' j)
theorem plainDivides_antisymm {p q : PlainExp} (h : plainDivides p q)
    (h' : plainDivides q p) : p = q := by
  ext j
  exact le_antisymm (h j) (h' j)

theorem plainStandard_downward (R : Finset PlainExp) {p q : PlainExp}
    (hq : q ∈ plainStandardSet R) (hpq : plainDivides p q) :
    p ∈ plainStandardSet R := by
  obtain ⟨s,hs,hqs⟩ := hq
  exact ⟨s,hs,plainDivides_trans hpq hqs⟩

theorem plain_zero_mem_standard (R : Finset PlainExp) (hR : R.Nonempty) :
    (0 : PlainExp) ∈ plainStandardSet R := by
  obtain ⟨s,hs⟩ := hR
  exact ⟨s,hs,fun j => by simp⟩

theorem plainStandardSet_finite (R : Finset PlainExp) : (plainStandardSet R).Finite := by
  have hf := R.finite_toSet.biUnion (fun s _ => Set.finite_Iic s)
  apply hf.subset
  rintro p ⟨s,hs,hps⟩
  exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨hs,hps⟩⟩

def plainStandardFinset (R : Finset PlainExp) : Finset PlainExp :=
  (plainStandardSet_finite R).toFinset

@[simp] theorem mem_plainStandardFinset (R : Finset PlainExp) (p : PlainExp) :
    p ∈ plainStandardFinset R ↔ p ∈ plainStandardSet R := Set.Finite.mem_toFinset _

@[simp] theorem plainUnitVector_apply (j r : Fin 3) :
    plainUnitVector j r = if j = r then 1 else 0 := by
  simp [plainUnitVector, Finsupp.single_apply]

@[simp] theorem plainPredecessor_apply (j : Fin 3) (p : PlainExp) (r : Fin 3) :
    plainPredecessor j p r = p r - if j = r then 1 else 0 := by
  simp [plainPredecessor, Finsupp.sub_apply]

theorem plainPredecessor_add_unitVector (j : Fin 3) (p : PlainExp)
    (hp : 0 < p j) : plainPredecessor j p + plainUnitVector j = p := by
  ext r
  by_cases hr : j = r
  · subst r
    simp only [Finsupp.add_apply, plainPredecessor_apply, plainUnitVector_apply,
      eq_self_iff_true, ite_true]
    omega
  · simp [Finsupp.add_apply, hr]

theorem plainPredecessor_divides (j : Fin 3) (p : PlainExp) :
    plainDivides (plainPredecessor j p) p := by
  intro r
  simp only [plainPredecessor_apply]
  exact Nat.sub_le _ _

theorem plainPredecessor_ne (j : Fin 3) (p : PlainExp) (hp : 0 < p j) :
    plainPredecessor j p ≠ p := by
  intro he
  have hc := congrArg (fun q : PlainExp => q j) he
  simp only [plainPredecessor_apply, eq_self_iff_true, ite_true] at hc
  omega

theorem plain_direction_active (R : Finset PlainExp) (h : PlainVariablesSurvive R)
    (j : Fin 3) : ∃ s ∈ R, 0 < s j := by
  obtain ⟨s,hs,hjs⟩ := h j
  refine ⟨s,hs,?_⟩
  have h1 : 1 ≤ s j := by simpa using hjs j
  omega

def plainBorderCriterion (R : Finset PlainExp) (p : PlainExp) : Prop :=
  p ∉ plainStandardSet R ∧
    ∀ j : Fin 3, 0 < p j → plainPredecessor j p ∈ plainStandardSet R

def plainMinimalKilled (R : Finset PlainExp) (p : PlainExp) : Prop :=
  p ∉ plainStandardSet R ∧
    ∀ q, plainDivides q p → q ≠ p → q ∈ plainStandardSet R

theorem plainBorderCriterion_iff_minimalKilled (R : Finset PlainExp) (p : PlainExp) :
    plainBorderCriterion R p ↔ plainMinimalKilled R p := by
  constructor
  · rintro ⟨hp,hpred⟩
    refine ⟨hp,?_⟩
    intro q hqp hne
    have hex : ∃ j : Fin 3, q j < p j := by
      by_contra hn
      push_neg at hn
      apply hne
      ext j
      exact le_antisymm (hqp j) (hn j)
    obtain ⟨j,hj⟩ := hex
    have hpj : 0 < p j := by omega
    apply plainStandard_downward R (hpred j hpj)
    intro r
    by_cases hr : j = r
    · subst r
      simp only [plainPredecessor_apply, eq_self_iff_true, ite_true]
      omega
    · simpa [hr] using hqp r
  · rintro ⟨hp,hmin⟩
    exact ⟨hp,fun j hj => hmin _ (plainPredecessor_divides j p)
      (plainPredecessor_ne j p hj)⟩

private def borderCandidates (R : Finset PlainExp) : Finset PlainExp :=
  insert 0 ((plainStandardFinset R).biUnion
    (fun p => Finset.univ.image (fun j : Fin 3 => p + plainUnitVector j)))

def plainBorderFinset (R : Finset PlainExp) : Finset PlainExp :=
  (borderCandidates R).filter (plainBorderCriterion R)

theorem mem_plainBorderFinset_iff (R : Finset PlainExp) (p : PlainExp) :
    p ∈ plainBorderFinset R ↔ p ∉ plainStandardSet R ∧
      ∀ j : Fin 3, 0 < p j → plainPredecessor j p ∈ plainStandardSet R := by
  classical
  change p ∈ (borderCandidates R).filter (plainBorderCriterion R) ↔ plainBorderCriterion R p
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro hp
    refine ⟨?_,hp⟩
    by_cases hzero : p = 0
    · simp [borderCandidates, hzero]
    · have hex : ∃ j : Fin 3, 0 < p j := by
        by_contra hn
        push_neg at hn
        apply hzero
        ext j
        simpa using hn j
      obtain ⟨j,hj⟩ := hex
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨plainPredecessor j p, (mem_plainStandardFinset _ _).mpr (hp.2 j hj), ?_⟩
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,plainPredecessor_add_unitVector j p hj⟩

theorem plain_border_iff_minimalKilled (R : Finset PlainExp) (p : PlainExp) :
    p ∈ plainBorderFinset R ↔ plainMinimalKilled R p :=
  (mem_plainBorderFinset_iff R p).trans (plainBorderCriterion_iff_minimalKilled R p)

def PlainDirectionalCentre (R : Finset PlainExp) (j : Fin 3) (c : PlainExp) : Prop :=
  c ∈ R ∧ ∀ s ∈ R, 0 < s j → plainDivides (plainPredecessor j s) c
def HasPlainDirectionalCentres (R : Finset PlainExp) : Prop :=
  ∀ j : Fin 3, ∃ c, PlainDirectionalCentre R j c

theorem plain_centre_other_root_coordinates (R : Finset PlainExp)
    (hR : PlainRootAntichain R) {j : Fin 3} {c s : PlainExp}
    (hc : PlainDirectionalCentre R j c) (hs : s ∈ R) (hne : s ≠ c)
    (hpos : 0 < s j) : s j = c j + 1 ∧ ∀ r, r ≠ j → s r ≤ c r := by
  have hpred := hc.2 s hs hpos
  have hother : ∀ r, r ≠ j → s r ≤ c r := by
    intro r hr
    simpa [Ne.symm hr] using hpred r
  have hnot : ¬s j ≤ c j := by
    intro hj
    apply hne
    apply hR s hs c hc.1
    intro r
    by_cases hr : r = j
    · simpa [hr] using hj
    · exact hother r hr
  have hj := hpred j
  simp only [plainPredecessor_apply, eq_self_iff_true, ite_true] at hj
  exact ⟨by omega,hother⟩
end
end P23.Monomial
