import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Function_orbitCensus_of_dihedralThree_relations

set_option autoImplicit false

namespace P2MKcOrbitCensus

variable {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
  (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))

include hb in
/--
@isnad1 id=injectiv.1h2v.s4.f5a2a008fb60 from=translated src=- shape=c63fcb28 vocab=7a5d7ebb
-/
theorem b_injective : Function.Injective b := fun x y h => by
  have := congrArg (fun z => b (b z)) h
  simpa [hb] using this

include hb hab in

/--
@isnad1 id=eq.2h4v.s5.ed8dcb9a4c63 from=translated src=- shape=b1bab6b2 vocab=e88e931a
-/
theorem abb (x : X) : a (b (b x)) = b (a x) := by
  have h := hab (b x)
  rw [hab x] at h
  rw [h, hb]

include hb hab in
/--
@isnad1 id=eq.2h4v.s5.f07eb3e62304 from=translated src=- shape=33a2dd6a vocab=e88e931a
-/
theorem ba (x : X) : b (a x) = a (b (b x)) := (abb a b hb hab x).symm

def T (x : X) : Finset X := {x, b x, b (b x)}

/--
@isnad1 id=iff.0h4v.s5.03c85040ac7e from=translated src=- shape=f8c408e4 vocab=7ab7aeed
-/
theorem mem_T {x y : X} : y ∈ T b x ↔ y = x ∨ y = b x ∨ y = b (b x) := by
  simp [T]

/--
@isnad1 id=mem.0h3v.s4.ae20d94d57f5 from=translated src=- shape=ad95ce20 vocab=7ab7aeed
-/
theorem self_mem_T (x : X) : x ∈ T b x := (mem_T b).mpr (Or.inl rfl)

include hb in
/--
@isnad1 id=eq.1h3v.s5.b428b96a5757 from=translated src=- shape=13dfdb03 vocab=ce2ec700
-/
theorem T_b (x : X) : T b (b x) = T b x := by
  ext y
  simp only [mem_T, hb]
  tauto

include hb in
/--
@isnad1 id=eq.2h4v.s5.0c0e0fe27105 from=translated src=- shape=1139a246 vocab=7ab7aeed
-/
theorem T_eq_of_mem {x y : X} (h : y ∈ T b x) : T b y = T b x := by
  rcases (mem_T b).mp h with rfl | rfl | rfl
  · rfl
  · exact T_b b hb x
  · rw [T_b b hb, T_b b hb]

include hb in

/--
@isnad1 id=or.1h4v.s5.127293d6beee from=translated src=- shape=9f3fd1c9 vocab=bfd0e01e
-/
theorem T_eq_or_disjoint (x y : X) : T b y = T b x ∨ Disjoint (T b x) (T b y) := by
  by_cases h : Disjoint (T b x) (T b y)
  · exact Or.inr h
  · left
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hzx, hzy⟩ := h
    rw [← T_eq_of_mem b hb hzy, T_eq_of_mem b hb hzx]

include hb in
/--
@isnad1 id=eq.2h3v.s5.f8d5a468bc5d from=translated src=- shape=2035f525 vocab=dda81bd4
-/
theorem card_T_of_fix {x : X} (h : b x = x) : (T b x).card = 1 := by
  have : T b x = {x} := by
    ext y; simp [mem_T, h]
  rw [this, Finset.card_singleton]

include hb in
/--
@isnad1 id=eq.2h3v.s5.e88cc8a49e9f from=translated src=- shape=1cdd5222 vocab=dda81bd4
-/
theorem card_T_of_not_fix {x : X} (h : b x ≠ x) : (T b x).card = 3 := by
  have h1 : b x ≠ x := h
  have h2 : b (b x) ≠ x := by
    intro h2
    apply h
    have := congrArg b h2
    rw [hb] at this
    exact this.symm
  have h3 : b (b x) ≠ b x := by
    intro h3
    exact h ((b_injective b hb) h3)
  rw [T, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simpa using h3.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩

include hb in
/--
@isnad1 id=or.1h3v.s6.112c7dab3d67 from=translated src=- shape=e2f6ad94 vocab=dda81bd4
-/
theorem card_T (x : X) : ((T b x).card = 1 ∧ b x = x) ∨ ((T b x).card = 3 ∧ b x ≠ x) := by
  by_cases h : b x = x
  · exact Or.inl ⟨card_T_of_fix b hb h, h⟩
  · exact Or.inr ⟨card_T_of_not_fix b hb h, h⟩

include ha hb hab in

/--
@isnad1 id=iff.3h4v.s6.d03f4a296494 from=translated src=- shape=0ff8c327 vocab=e88e931a
-/
theorem bfix_a_iff (x : X) : b (a x) = a x ↔ b x = x := by
  constructor
  · intro h

    have h' : b (a (a x)) = a (a x) := by
      rw [ba a b hb hab (a x)]
      have hbb : b (b (a x)) = a x := by rw [h, h]
      rw [hbb]
    rwa [ha] at h'
  · intro h
    rw [ba a b hb hab x, h, h]

include ha hb hab in
/--
@isnad1 id=eq.3h4v.s6.b212f7eb6e53 from=translated src=- shape=d3cec449 vocab=dda81bd4
-/
theorem card_T_a (x : X) : (T b (a x)).card = (T b x).card := by
  rcases card_T b hb x with ⟨h1, hx⟩ | ⟨h3, hx⟩
  · rw [h1, card_T_of_fix b hb ((bfix_a_iff a b ha hb hab x).mpr hx)]
  · rw [h3, card_T_of_not_fix b hb (fun h => hx ((bfix_a_iff a b ha hb hab x).mp h))]

include hb hab in

/--
@isnad1 id=iff.2h5v.s6.5ecd9f975716 from=translated src=- shape=56e17a14 vocab=7ab7aeed
-/
theorem mem_T_a_iff {x y : X} : y ∈ T b (a x) ↔ y = a x ∨ y = a (b x) ∨ y = a (b (b x)) := by
  have h1 : b (a x) = a (b (b x)) := ba a b hb hab x
  have h2 : b (b (a x)) = a (b x) := (hab x).symm
  rw [mem_T, h2, h1]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

def six (x : X) : Finset X := T b x ∪ T b (a x)

include hb hab in
/--
@isnad1 id=iff.2h5v.s6.7a2ad47aec66 from=translated src=- shape=38d2b7ec vocab=455f33e8
-/
theorem mem_six {x y : X} :
    y ∈ six a b x ↔ (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))) := by
  rw [six, Finset.mem_union, mem_T, mem_T_a_iff a b hb hab]
  tauto

include ha hb hab in

/--
@isnad1 id=or.3h4v.s7.ccbb96452997 from=translated src=- shape=859364ea vocab=56f9824b
-/
theorem card_six (x : X) :
    (T b (a x) = T b x ∧ (six a b x).card = (T b x).card) ∨
      (Disjoint (T b x) (T b (a x)) ∧ (six a b x).card = 2 * (T b x).card) := by
  rcases T_eq_or_disjoint b hb x (a x) with h | h
  · left
    refine ⟨h, ?_⟩
    rw [six, h, Finset.union_idempotent]
  · right
    refine ⟨h, ?_⟩
    rw [six, Finset.card_union_of_disjoint h, card_T_a a b ha hb hab, two_mul]

include ha hb hab in
/--
@isnad1 id=or.3h4v.s6.8b1183da779d from=translated src=- shape=d776ec28 vocab=d3dbb3b0
-/
theorem card_six_mem (x : X) :
    (six a b x).card = 1 ∨ (six a b x).card = 2 ∨ (six a b x).card = 3 ∨ (six a b x).card = 6 := by
  rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩ <;>
    rcases card_T b hb x with ⟨h1, -⟩ | ⟨h3, -⟩
  · exact Or.inl (by rw [h, h1])
  · exact Or.inr (Or.inr (Or.inl (by rw [h, h3])))
  · exact Or.inr (Or.inl (by rw [h, h1]))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, h3])))

include ha hb hab in

/--
@isnad1 id=iff.3h4v.s6.ad2d5aacf009 from=translated src=- shape=5e617161 vocab=17e232e8
-/
theorem odd_iff (x : X) :
    ((six a b x).card = 1 ∨ (six a b x).card = 3) ↔ a x ∈ T b x := by
  constructor
  · intro hodd
    rcases card_six a b ha hb hab x with ⟨h, -⟩ | ⟨-, h⟩
    · rw [← h]; exact self_mem_T b (a x)
    · exfalso
      rw [h] at hodd
      rcases hodd with h' | h' <;> omega
  · intro hmem
    have hT : T b (a x) = T b x := T_eq_of_mem b hb hmem
    have : (six a b x).card = (T b x).card := by rw [six, hT, Finset.union_idempotent]
    rw [this]
    rcases card_T b hb x with ⟨h1, -⟩ | ⟨h3, -⟩
    · exact Or.inl h1
    · exact Or.inr h3

include ha hb hab in

/--
@isnad1 id=iff.3h4v.s6.bdfef25867a7 from=translated src=- shape=8fe614ab vocab=d3dbb3b0
-/
theorem small_iff (x : X) :
    ((six a b x).card = 1 ∨ (six a b x).card = 2) ↔ b x = x := by
  constructor
  · intro hsmall
    by_contra hne
    have h3 := card_T_of_not_fix b hb hne
    rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h, h3] at hsmall <;> omega
  · intro hfix
    have h1 := card_T_of_fix b hb hfix
    rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (by rw [h, h1])
    · exact Or.inr (by rw [h, h1])

variable {ι : Type*} [DecidableEq ι] (c : X → ι)
  (hc : ∀ x y, c x = c y ↔
    (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))

include hb hab hc in
/--
@isnad1 id=eq.3h6v.s7.731d977fe9f2 from=translated src=- shape=a0d7c6cb vocab=315eca58
-/
theorem fibre_eq_six (x : X) : (Finset.univ.filter fun y => c y = c x) = six a b x := by
  ext y
  rw [Finset.mem_filter, mem_six a b hb hab]
  simp only [Finset.mem_univ, true_and]
  rw [eq_comm, hc x y]

include hb hab hc in
/--
@isnad1 id=iff.3h7v.s7.aad539c2ad8b from=translated src=- shape=ac72da99 vocab=455f33e8
-/
theorem c_eq_iff_mem_six (x y : X) : c y = c x ↔ y ∈ six a b x := by
  rw [mem_six a b hb hab, eq_comm, hc x y]

end P2MKcOrbitCensus

open P2MKcOrbitCensus in
/--
@isnad1 id=and.5h6v.s9.24c93ed4cd55 from=translated src=- shape=76374a95 vocab=7ad5e29e
-/
theorem solution
    {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))
    {ι : Type*} [DecidableEq ι] (c : X → ι)
    (hc : ∀ x y, c x = c y ↔
      (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))
    (S : Finset ι) (hS : ∀ p, p ∈ S ↔ ∃ x, c x = p) :
    (∀ x, (Finset.univ.filter fun y => c y = c x).card = 1 ∨
        (Finset.univ.filter fun y => c y = c x).card = 2 ∨
        (Finset.univ.filter fun y => c y = c x).card = 3 ∨
        (Finset.univ.filter fun y => c y = c x).card = 6) ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 ∨
        (Finset.univ.filter fun y => c y = p).card = 3).card =
      (Finset.univ.filter fun x => a x = x).card ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1).card +
        2 * (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2).card =
      (Finset.univ.filter fun x => b x = x).card := by
  have hfib := fibre_eq_six a b hb hab c hc
  refine ⟨fun x => by rw [hfib]; exact card_six_mem a b ha hb hab x, ?_, ?_⟩
  ·
    symm
    apply Finset.card_bij (fun x _ => c x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨(hS _).mpr ⟨x, rfl⟩, ?_⟩
      rw [hfib, odd_iff a b ha hb hab]
      rw [hx.2]; exact self_mem_T b x
    · intro x hx x' hx' hxx'
      rw [Finset.mem_filter] at hx hx'
      have hmem : x' ∈ six a b x := (c_eq_iff_mem_six a b hb hab c hc x x').mp hxx'.symm
      have hT : T b (a x) = T b x := by rw [hx.2]
      rw [six, hT, Finset.union_idempotent, mem_T] at hmem
      rcases hmem with h | h | h
      · exact h.symm
      ·
        have hfix : a (b x) = b x := by rw [← h]; exact hx'.2
        rw [hab x, hx.2] at hfix

        have : b x = x := b_injective b hb hfix
        rw [h, this]
      · have hfix : a (b (b x)) = b (b x) := by rw [← h]; exact hx'.2
        rw [abb a b hb hab x, hx.2] at hfix

        have h1 : x = b x := b_injective b hb hfix
        rw [h, ← h1, ← h1]
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨x, rfl⟩ := (hS p).mp hp.1
      have hodd : (six a b x).card = 1 ∨ (six a b x).card = 3 := by rw [← hfib]; exact hp.2
      have hmem : a x ∈ T b x := (odd_iff a b ha hb hab x).mp hodd
      rcases (mem_T b).mp hmem with h | h | h
      · exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩, rfl⟩
      ·
        refine ⟨b (b x), ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [abb a b hb hab x, h]
        · exact (c_eq_iff_mem_six a b hb hab c hc x _).mpr
            ((mem_six a b hb hab).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      ·
        refine ⟨b x, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hab x, h, hb]
        · exact (c_eq_iff_mem_six a b hb hab c hc x _).mpr
            ((mem_six a b hb hab).mpr (Or.inr (Or.inr (Or.inl rfl))))
  ·
    set S1 := S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 with hS1
    set S2 := S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2 with hS2
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega

    have hunion : (Finset.univ.filter fun x => b x = x) =
        (S1 ∪ S2).biUnion fun p => Finset.univ.filter fun y => c y = p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_union,
        hS1, hS2]
      constructor
      · intro hfix
        refine ⟨c x, ?_, rfl⟩
        have hsmall := (small_iff a b ha hb hab x).mpr hfix
        rw [← hfib] at hsmall
        rcases hsmall with h | h
        · exact Or.inl ⟨(hS _).mpr ⟨x, rfl⟩, h⟩
        · exact Or.inr ⟨(hS _).mpr ⟨x, rfl⟩, h⟩
      · rintro ⟨p, hp, rfl⟩
        apply (small_iff a b ha hb hab x).mp
        rw [← hfib]
        rcases hp with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
    rw [hunion, Finset.card_biUnion]
    · rw [Finset.sum_union hdisj]
      have h1 : ∑ p ∈ S1, (Finset.univ.filter fun y => c y = p).card = ∑ p ∈ S1, 1 :=
        Finset.sum_congr rfl fun p hp => by rw [hS1, Finset.mem_filter] at hp; exact hp.2
      have h2 : ∑ p ∈ S2, (Finset.univ.filter fun y => c y = p).card = ∑ p ∈ S2, 2 :=
        Finset.sum_congr rfl fun p hp => by rw [hS2, Finset.mem_filter] at hp; exact hp.2
      rw [h1, h2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    · intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_filter]
      intro x _ h1 h2
      exact hpq (h1.symm.trans h2)
