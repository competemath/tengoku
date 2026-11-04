import Tengoku.DeletionCodesLean.DeletionCode.WalkSelection
import Tengoku.DeletionCodesLean.DeletionCode.FiniteGenerating
import Tengoku.DeletionCodesLean.DeletionCode.CatalogueAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms selected_step_injOn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms selected_independent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms selected_generatingAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms selectedSpan_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms novelty_transfer` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The finite scan selects step indices. This module transfers its conclusions to
the actual finite set of integer rules. Linear independence supplies the unique
selected occurrence of each rule, so its chronological rank is derived rather
than supplied as an additional hypothesis.
-/
namespace DeletionCode.FiniteWalkRules

open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating

variable {k m : ℕ}

def step (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    Gram (windowLength k) → ℤ := p i.succ - p i.castSucc

def rationalPath (p : Fin (m + 1) → Gram (windowLength k) → ℤ) :
    Fin (m + 1) → Gram (windowLength k) → ℚ := fun j => rational (p j)

noncomputable def selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    RuleSet k := by
  classical
  exact S.image (step p)

/--
@isnad1 id=eq.0h4v.s6.7aa0acaceb52 from=translated src=- shape=2cc3df70 vocab=fbee118c
-/
@[simp] theorem rational_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    rational (step p i) = walkStep (rationalPath p) i := by
  funext g
  simp [rational, step, walkStep, rationalPath]

/--
@isnad1 id=iff.0h5v.s6.33d62dc1d6ca from=translated src=- shape=22bfa9b1 vocab=68fb3c53
-/
@[simp] theorem mem_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : Gram (windowLength k) → ℤ) :
    u ∈ selectedRules p S ↔ ∃ i ∈ S, step p i = u := by
  classical
  exact Finset.mem_image

/--
@isnad1 id=mem.1h5v.s6.0a854d80a79a from=translated src=- shape=73fcfe1e vocab=68fb3c53
-/
theorem step_mem_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m) (hi : i ∈ S) : step p i ∈ selectedRules p S :=
  (mem_selectedRules p S _).mpr ⟨i, hi, rfl⟩

/--
@isnad1 id=eq.0h3v.s5.b1774bf05b4c from=translated src=- shape=2f89539a vocab=b847bf75
-/
@[simp] theorem selectedRules_empty
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) :
    selectedRules p ∅ = ∅ := by
  classical
  simp [selectedRules]

/--
@isnad1 id=eq.0h5v.s6.2346be933403 from=translated src=- shape=7e01b323 vocab=cf729f1d
-/
@[simp] theorem selectedRules_insert
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m) : selectedRules p (insert i S) = insert (step p i) (selectedRules p S) := by
  classical
  simp [selectedRules]

/--
@isnad1 id=injon.1h4v.s6.f5c54f009a5d from=translated src=- shape=17e32740 vocab=b1d69366
-/
theorem selected_step_injOn
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (step p) (↑S : Set (Fin m)) := by
  intro i hi j hj hij
  have heq : walkStep (rationalPath p) i = walkStep (rationalPath p) j := by
    simpa only [rational_step] using congrArg rational hij
  have hs : (⟨i, hi⟩ : S) = ⟨j, hj⟩ := hind.injective heq
  exact congrArg Subtype.val hs

private theorem selectedIndex_exists
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : ∃ i : S, step p i.val = u.val := by
  obtain ⟨i, hi, heq⟩ := (mem_selectedRules p S u.val).mp u.property
  exact ⟨⟨i, hi⟩, heq⟩

noncomputable def selectedIndex
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : S := Classical.choose (selectedIndex_exists p S u)

/--
@isnad1 id=eq.0h5v.s7.ae883da2ab99 from=translated src=- shape=7b1cc77c vocab=b10858eb
-/
theorem selectedIndex_spec
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : step p (selectedIndex p S u).val = u.val :=
  Classical.choose_spec (selectedIndex_exists p S u)

/--
@isnad1 id=injectiv.0h4v.s6.58363329e8d6 from=translated src=- shape=77b74438 vocab=d7d1bf78
-/
theorem selectedIndex_injective
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    Function.Injective (selectedIndex p S) := by
  intro u v huv
  apply Subtype.ext
  calc
    u.val = step p (selectedIndex p S u).val := (selectedIndex_spec p S u).symm
    _ = step p (selectedIndex p S v).val := by rw [huv]
    _ = v.val := selectedIndex_spec p S v

/--
@isnad1 id=eq.2h5v.s7.094fa2f5163f from=translated src=- shape=bfea34c4 vocab=fcb1cc66
-/
theorem selectedIndex_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) :
    (selectedIndex p S ⟨step p i, step_mem_selectedRules p S i hi⟩).val = i :=
  selected_step_injOn p S hind (selectedIndex p S _).property hi
    (selectedIndex_spec p S _)

/--
@isnad1 id=independ.1h4v.s6.4d2b5270ed1b from=translated src=- shape=7668d5ec vocab=0a04f8e9
-/
theorem selected_independent
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Independent (selectedRules p S) := by
  have h := hind.comp (selectedIndex p S) (selectedIndex_injective p S)
  change LinearIndependent ℚ (fun u : selectedRules p S => rational u.val)
  convert h using 1
  funext u
  change rational u.val = walkStep (rationalPath p) (selectedIndex p S u).val
  rw [← rational_step, selectedIndex_spec]

noncomputable def selectedRank
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : Gram (windowLength k) → ℤ) : ℕ := by
  classical
  exact if hu : u ∈ selectedRules p S then (selectedIndex p S ⟨u, hu⟩).val.val else 0

/--
@isnad1 id=eq.2h5v.s7.fa5d926e7e81 from=translated src=- shape=247e02e8 vocab=18d61b2a
-/
theorem selectedRank_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) : selectedRank p S (step p i) = i.val := by
  classical
  simp only [selectedRank, dite_eq_left (step_mem_selectedRules p S i hi)]
  rw [selectedIndex_step p S hind i hi]

/--
@isnad1 id=injon.1h4v.s7.b5b4ee1fe331 from=translated src=- shape=1e29fa5e vocab=4917e88c
-/
theorem selectedRank_injOn
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (selectedRank p S) (↑(selectedRules p S) : Set _) := by
  intro u hu v hv heq
  obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
  obtain ⟨j, hj, rfl⟩ := (mem_selectedRules p S v).mp hv
  rw [selectedRank_step p S hind i hi, selectedRank_step p S hind j hj] at heq
  exact congrArg (step p) (Fin.ext heq)

/--
@isnad1 id=generati.2h4v.s7.79f31355b487 from=translated src=- shape=b647284d vocab=008023e9
-/
theorem selected_generatingAt
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (hgen : GeneratingSelected (rationalPath p) S) :
    GeneratingAt (p 0) (selectedRules p S) := by
  classical
  refine ⟨selected_independent p S hind, selectedRank p S,
    selectedRank_injOn p S hind, ?_⟩
  intro u hu g hneg
  obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
  have hnegQ : walkStep (rationalPath p) i g = -1 := by
    rw [← rational_step]
    change (step p i g : ℚ) = -1
    exact_mod_cast hneg
  rcases hgen i hi g hnegQ with hbase | ⟨r, hr, hri, hrg⟩
  · left
    intro hz
    apply hbase
    simp [rationalPath, rational, hz]
  · right
    refine ⟨step p r, step_mem_selectedRules p S r hr, ?_, ?_⟩
    · simpa only [selectedRank_step p S hind r hr,
        selectedRank_step p S hind i hi] using hri
    · intro hz
      apply hrg
      rw [← rational_step]
      simp [rational, hz]

/--
@isnad1 id=eq.0h4v.s6.62d24c4044d4 from=translated src=- shape=c1debc30 vocab=ff6b6276
-/
theorem rational_image_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    rational '' (↑(selectedRules p S) : Set _) =
      walkStep (rationalPath p) '' (↑S : Set (Fin m)) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
    exact ⟨i, hi, (rational_step p i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨step p i, step_mem_selectedRules p S i hi, rational_step p i⟩

/--
@isnad1 id=eq.0h4v.s7.0f1f2b9a9e83 from=translated src=- shape=d2b11af4 vocab=ea677cbe
-/
theorem selectedSpan_eq
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    selectedSpan (walkStep (rationalPath p)) S =
      Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by
  rw [rational_image_selectedRules]
  rfl

/--
@isnad1 id=and.2h6v.s7.8370e2930fb9 from=translated src=- shape=658997ec vocab=31806d3a
-/
theorem novelty_transfer
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m)
    (hnew : ¬ SignedMember (walkStep (rationalPath p)) S (walkStep (rationalPath p) i)) :
    ∀ u ∈ selectedRules p S, step p i ≠ u ∧ step p i ≠ -u := by
  intro u hu
  obtain ⟨r, hr, rfl⟩ := (mem_selectedRules p S u).mp hu
  constructor
  · intro heq
    apply hnew
    refine ⟨r, hr, Or.inl ?_⟩
    simpa only [rational_step] using congrArg rational heq
  · intro heq
    apply hnew
    refine ⟨r, hr, Or.inr ?_⟩
    simpa only [rational_neg, rational_step] using congrArg rational heq

end DeletionCode.FiniteWalkRules
