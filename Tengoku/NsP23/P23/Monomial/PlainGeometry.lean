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

/--
@isnad1 id=plaindiv.0h1v.s2.c0f77da70dcf from=translated src=- shape=b3bac8d8 vocab=843a51c6
-/
theorem plainDivides_refl (p : PlainExp) : plainDivides p p := fun _ => le_rfl
/--
@isnad1 id=plaindiv.2h3v.s4.ec079ef48845 from=translated src=- shape=0bc0c4a6 vocab=843a51c6
-/
theorem plainDivides_trans {p q r : PlainExp} (h : plainDivides p q)
    (h' : plainDivides q r) : plainDivides p r := fun j => le_trans (h j) (h' j)
/--
@isnad1 id=eq.2h2v.s4.e375fbc01326 from=translated src=- shape=5f71b5ec vocab=843a51c6
-/
theorem plainDivides_antisymm {p q : PlainExp} (h : plainDivides p q)
    (h' : plainDivides q p) : p = q := by
  ext j
  exact le_antisymm (h j) (h' j)

/--
@isnad1 id=mem.2h3v.s4.007c5d0fffa4 from=translated src=- shape=d94d1d2d vocab=9280a5b3
-/
theorem plainStandard_downward (R : Finset PlainExp) {p q : PlainExp}
    (hq : q ∈ plainStandardSet R) (hpq : plainDivides p q) :
    p ∈ plainStandardSet R := by
  obtain ⟨s,hs,hqs⟩ := hq
  exact ⟨s,hs,plainDivides_trans hpq hqs⟩

/--
@isnad1 id=mem.1h1v.s4.0b9753ac32be from=translated src=- shape=061edfc8 vocab=643aca12
-/
theorem plain_zero_mem_standard (R : Finset PlainExp) (hR : R.Nonempty) :
    (0 : PlainExp) ∈ plainStandardSet R := by
  obtain ⟨s,hs⟩ := hR
  exact ⟨s,hs,fun j => by simp⟩

/--
@isnad1 id=finite.0h1v.s2.f1a094fb3fb5 from=translated src=- shape=0ae065e3 vocab=393617e9
-/
theorem plainStandardSet_finite (R : Finset PlainExp) : (plainStandardSet R).Finite := by
  have hf := R.finite_toSet.biUnion (fun s _ => Set.finite_Iic s)
  apply hf.subset
  rintro p ⟨s,hs,hps⟩
  exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨hs,hps⟩⟩

def plainStandardFinset (R : Finset PlainExp) : Finset PlainExp :=
  (plainStandardSet_finite R).toFinset

/--
@isnad1 id=iff.0h2v.s4.3f38f942c3aa from=translated src=- shape=7b49c80c vocab=261dc23a
-/
@[simp] theorem mem_plainStandardFinset (R : Finset PlainExp) (p : PlainExp) :
    p ∈ plainStandardFinset R ↔ p ∈ plainStandardSet R := Set.Finite.mem_toFinset _

/--
@isnad1 id=eq.0h2v.s6.14dd42cf9be5 from=translated src=- shape=584e2273 vocab=14bb7e70
-/
@[simp] theorem plainUnitVector_apply (j r : Fin 3) :
    plainUnitVector j r = if j = r then 1 else 0 := by
  simp [plainUnitVector, Finsupp.single_apply]

/--
@isnad1 id=eq.0h3v.s6.a9e1c8d55d7d from=translated src=- shape=788f4b9b vocab=0458fa2c
-/
@[simp] theorem plainPredecessor_apply (j : Fin 3) (p : PlainExp) (r : Fin 3) :
    plainPredecessor j p r = p r - if j = r then 1 else 0 := by
  simp [plainPredecessor, Finsupp.sub_apply]

/--
@isnad1 id=eq.1h2v.s6.2c4d2650827c from=translated src=- shape=3688a00d vocab=63e81782
-/
theorem plainPredecessor_add_unitVector (j : Fin 3) (p : PlainExp)
    (hp : 0 < p j) : plainPredecessor j p + plainUnitVector j = p := by
  ext r
  by_cases hr : j = r
  · subst r
    simp only [Finsupp.add_apply, plainPredecessor_apply, plainUnitVector_apply,
      eq_self_iff_true, ite_true]
    omega
  · simp [Finsupp.add_apply, hr]

/--
@isnad1 id=plaindiv.0h2v.s3.8f5fa4e539c0 from=translated src=- shape=987d4990 vocab=bc54b8a9
-/
theorem plainPredecessor_divides (j : Fin 3) (p : PlainExp) :
    plainDivides (plainPredecessor j p) p := by
  intro r
  simp only [plainPredecessor_apply]
  exact Nat.sub_le _ _

/--
@isnad1 id=ne.1h2v.s5.82e511f8d557 from=translated src=- shape=b688b27b vocab=a5c04c8b
-/
theorem plainPredecessor_ne (j : Fin 3) (p : PlainExp) (hp : 0 < p j) :
    plainPredecessor j p ≠ p := by
  intro he
  have hc := congrArg (fun q : PlainExp => q j) he
  simp only [plainPredecessor_apply, eq_self_iff_true, ite_true] at hc
  omega

/--
@isnad1 id=ex.1h2v.s6.558e7caa09ce from=translated src=- shape=8538b979 vocab=2d4977f5
-/
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

/--
@isnad1 id=iff.0h2v.s3.049922196e8d from=translated src=- shape=7d7b0759 vocab=7384cfef
-/
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

/--
@isnad1 id=iff.0h2v.s6.48390dc74850 from=translated src=- shape=fd7fc2cc vocab=1bc03fa9
-/
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

/--
@isnad1 id=iff.0h2v.s4.b1e0a8a76bcd from=translated src=- shape=0fc14d99 vocab=d7981bc1
-/
theorem plain_border_iff_minimalKilled (R : Finset PlainExp) (p : PlainExp) :
    p ∈ plainBorderFinset R ↔ plainMinimalKilled R p :=
  (mem_plainBorderFinset_iff R p).trans (plainBorderCriterion_iff_minimalKilled R p)

def PlainDirectionalCentre (R : Finset PlainExp) (j : Fin 3) (c : PlainExp) : Prop :=
  c ∈ R ∧ ∀ s ∈ R, 0 < s j → plainDivides (plainPredecessor j s) c
def HasPlainDirectionalCentres (R : Finset PlainExp) : Prop :=
  ∀ j : Fin 3, ∃ c, PlainDirectionalCentre R j c

/--
@isnad1 id=and.5h4v.s7.00d55ada9db8 from=translated src=- shape=d006092e vocab=8b0e9149
-/
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
