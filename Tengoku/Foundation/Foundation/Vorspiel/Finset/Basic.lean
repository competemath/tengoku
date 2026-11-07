module

public import Tengoku.Seed.Data.Fin.VecNotation
public import Tengoku.Seed.Data.Finset.Preimage
public import Tengoku.Seed.Data.Finset.Sort
public import Tengoku.Seed.Data.Fintype.Sigma
public import Tengoku.Seed.Data.Fintype.Vector
public import Tengoku.Seed.Data.Set.Finite.Range

namespace Finset
end Finset

namespace FoundationFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace Finset
open _root_.Finset

variable {α : Type*} {a b : α} {s : Finset α}

/--
@isnad1 id=iff.0h4v.s6.fad36b142e0d from=translated src=- shape=a3f6923a vocab=7fc6ae6f
-/
@[grind =]
lemma doubleton_subset [DecidableEq α] : ({a, b} : Finset α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . intro h;
    have ⟨ha, hb⟩ := Finset.insert_subset_iff.mp h;
    tauto;
  . rintro ⟨ha, hb⟩;
    apply Finset.insert_subset_iff.mpr;
    constructor;
    . assumption;
    . simpa;

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539367015
-/
/--
@isnad1 id=not.0h2v.s5.554e2511dae8 from=translated src=- shape=974838f1 vocab=555f00d6
-/
lemma no_ssubset_descending_chain  {f : ℕ → Finset α} : ¬(∀ i, ∃ j > i, f j ⊂ f i) := by
  intro h
  have n := 0
  induction hf : f n using WellFoundedLT.fix generalizing n with subst hf | _ _ ih
  obtain ⟨m, -, hy⟩ := h n
  exact ih (f m) hy m rfl

section

noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.finite_range f)

/--
@isnad1 id=iff.0h4v.s5.464b60c06fd6 from=translated src=- shape=14c036ca vocab=2b39c7f8
-/
lemma mem_rangeOfFinite_iff  {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp [rangeOfFinite]

noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) : Finset β :=
  Finset.biUnion s (rangeOfFinite $ f ·)

/--
@isnad1 id=iff.0h5v.s6.e5e5dfa299c9 from=translated src=- shape=f9595e5b vocab=14931fb3
-/
lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp [imageOfFinset, mem_rangeOfFinite_iff]

/--
@isnad1 id=mem.1h5v.s5.feb985aa3f64 from=translated src=- shape=1d231285 vocab=14931fb3
-/
@[simp] lemma mem_imageOfFinset  [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a : α) (ha : a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simpa [mem_imageOfFinset_iff] using ⟨a, ha, rfl⟩

/--
@isnad1 id=eq.0h4v.s5.3a6330374906 from=translated src=- shape=f74db4b3 vocab=db19d44c
-/
lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp [and_or_left]

/--
@isnad1 id=eq.0h3v.s5.ac8c66c0280d from=translated src=- shape=dc31e7df vocab=c2c23ed7
-/
@[simp] lemma equiv_univ {α α'} [Fintype α] [Fintype α'] [DecidableEq α'] (e : α ≃ α') :
    (Finset.univ : Finset α).image e = Finset.univ := by ext x; simp

/--
@isnad1 id=eq.0h5v.s6.14bd2522ffa1 from=translated src=- shape=72431645 vocab=52331551
-/
@[simp] lemma sup_univ_equiv {α α'} [DecidableEq α] [Fintype α] [Fintype α'] [SemilatticeSup β] [OrderBot β] (f : α → β) (e : α' ≃ α) :
    Finset.sup Finset.univ (fun i => f (e i)) = Finset.sup Finset.univ f := by
  simpa [Function.comp] using! Eq.symm <| Finset.sup_image Finset.univ e f

/--
@isnad1 id=eq.1h4v.s6.9541e8bb253c from=translated src=- shape=99fee274 vocab=db6ecf12
-/
lemma sup_univ_cast {α : Type _} [SemilatticeSup α] [OrderBot α] {n} (f : Fin n → α) (n') {h : n' = n} :
    Finset.sup Finset.univ (fun (i : Fin n') => f (i.cast h)) = Finset.sup Finset.univ f := by rcases h with rfl; simp

end

/--
@isnad1 id=iff.0h4v.s5.a5987a6cd904 from=translated src=- shape=37dffba9 vocab=91ae880c
-/
lemma biUnion_eq_empty [DecidableEq β] {s : Finset α} {f : α → Finset β} :
    s.biUnion f = ∅ ↔ ∀ i ∈ s, f i = ∅ := by
  constructor
  · intro h a ha; ext b
    have := by simpa using congrFun (congrArg Membership.mem h) b
    simpa using this a ha
  · intro h; ext b
    suffices ∀ x ∈ s, b ∉ f x by simpa
    intro a ha; simpa using congrFun (congrArg Membership.mem (h a ha)) b

end Finset

end
