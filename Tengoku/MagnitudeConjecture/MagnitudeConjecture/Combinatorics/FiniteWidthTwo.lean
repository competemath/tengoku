import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.PosetSpaceChainFlag
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.PosetSpaceAntichainExtension
import Tengoku.Seed.Combinatorics.Hall.Basic
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite posets of width at most two

We prove the width-two case of Dilworth's theorem in the exact form needed by
the magnitude argument: a finite poset without a three-element antichain is
the union of two chains.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

variable {T : Type u} [PartialOrder T] [Fintype T]

/-- The minimal elements of a finite subset of a poset.-/
def minimalIn (A : Finset T) : Finset T := by
  classical
  exact A.filter fun x ↦ ∀ y ∈ A, ¬y < x

/-- If the ambient poset has no three-element antichain, a finite subset has
at most two minimal elements.
@isnad1 id=le.1h2v.s5.74881b542f1a from=translated src=- shape=bfc22a81 vocab=a39b8a6d
-/
theorem card_minimalIn_le_two
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c)
    (A : Finset T) :
    (minimalIn A).card ≤ 2 := by
  classical
  by_contra hnot
  have hlt : 2 < (minimalIn A).card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hlt
  apply hno a b c
  have haA := (Finset.mem_filter.mp ha).1
  have hbA := (Finset.mem_filter.mp hb).1
  have hcA := (Finset.mem_filter.mp hc).1
  have hamin := (Finset.mem_filter.mp ha).2
  have hbmin := (Finset.mem_filter.mp hb).2
  have hcmin := (Finset.mem_filter.mp hc).2
  refine
    { not_ab := ?_
      not_ba := ?_
      not_ac := ?_
      not_ca := ?_
      not_bc := ?_
      not_cb := ?_ }
  · intro hle
    exact hbmin a haA (lt_of_le_of_ne hle hab)
  · intro hle
    exact hamin b hbA (lt_of_le_of_ne hle hab.symm)
  · intro hle
    exact hcmin a haA (lt_of_le_of_ne hle hac)
  · intro hle
    exact hamin c hcA (lt_of_le_of_ne hle hac.symm)
  · intro hle
    exact hcmin b hbA (lt_of_le_of_ne hle hbc)
  · intro hle
    exact hbmin c hcA (lt_of_le_of_ne hle hbc.symm)

/-- A left vertex may be matched either to a strictly larger poset element
or to one of two terminal symbols.-/
def successorRel (x : T) : T ⊕ Fin 2 → Prop
  | Sum.inl y => x < y
  | Sum.inr _ => True

/-- Hall's theorem supplies an injective successor assignment with two
terminals.
@isnad1 id=ex.1h1v.s6.470a0b11b9bc from=translated src=- shape=b5fb2bb3 vocab=46c32666
-/
theorem exists_injective_successor
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    ∃ f : T → T ⊕ Fin 2, Function.Injective f ∧
      ∀ x, successorRel x (f x) := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (successorRel (T := T))).mp
  intro A
  let M := minimalIn A
  have hMcard : Fintype.card M ≤ Fintype.card (Fin 2) := by
    simpa [M] using card_minimalIn_le_two hno A
  let e : M ↪ Fin 2 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hMcard)
  let g : A → T ⊕ Fin 2 := fun a ↦
    if ha : a.1 ∈ M then Sum.inr (e ⟨a.1, ha⟩)
    else Sum.inl a.1
  have hg_injective : Function.Injective g := by
    intro a b hab
    by_cases ha : a.1 ∈ M <;> by_cases hb : b.1 ∈ M
    · have he : (⟨a.1, ha⟩ : M) = ⟨b.1, hb⟩ := by
        apply e.injective
        simpa [g, ha, hb] using hab
      apply Subtype.ext
      exact congrArg (fun z : M ↦ z.1) he
    · simp [g, ha, hb] at hab
    · simp [g, ha, hb] at hab
    · exact Subtype.ext (by simpa [g, ha, hb] using hab)
  have hg_mem (a : A) : ∃ x ∈ A, successorRel x (g a) := by
    by_cases ha : a.1 ∈ M
    · exact ⟨a.1, a.2, by simp [g, ha, successorRel]⟩
    · have hnonmin : ∃ x ∈ A, x < a.1 := by
        have ha' : ¬∀ x, x ∈ A → ¬x < a.1 := by
          intro h
          apply ha
          exact Finset.mem_filter.mpr ⟨a.2, fun x hx ↦ h x hx⟩
        push Not at ha'
        exact ha'
      obtain ⟨x, hxA, hxa⟩ := hnonmin
      exact ⟨x, hxA, by simpa [g, ha, successorRel] using hxa⟩
  let N : Finset (T ⊕ Fin 2) :=
    Finset.univ.filter fun z ↦ ∃ x ∈ A, successorRel x z
  let gN : A → N := fun a ↦
    ⟨g a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_mem a⟩⟩
  have hgN_injective : Function.Injective gN := by
    intro a b hab
    apply hg_injective
    exact congrArg Subtype.val hab
  have hcard : A.card ≤ N.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective gN hgN_injective
  simpa [N] using hcard

/-- Strict upper set of an element, used as a termination measure.-/
def strictUpperFinset (x : T) : Finset T := by
  classical
  exact Finset.univ.filter fun y ↦ x < y

/-- Moving strictly upward strictly decreases the cardinality of the strict
upper set.
@isnad1 id=lt.1h3v.s5.c8eeb289557a from=translated src=- shape=d54a0562 vocab=5ae46e44
-/
theorem card_strictUpperFinset_lt_of_lt {x y : T} (hxy : x < y) :
    (strictUpperFinset y).card < (strictUpperFinset x).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨y, by simp [strictUpperFinset, hxy],
      by simp [strictUpperFinset]⟩
  · intro z hz
    simp only [strictUpperFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz ⊢
    exact lt_trans hxy hz

/-- An injective successor assignment whose only non-poset outputs are two
terminal symbols.-/
structure TwoSuccessor (T : Type u) [PartialOrder T] where
  next : T → T ⊕ Fin 2
  next_injective : Function.Injective next
  related : ∀ x, successorRel x (next x)

namespace TwoSuccessor

variable (F : TwoSuccessor T)

/--
@isnad1 id=lt.1h4v.s5.a64a97e0fbce from=translated src=- shape=0ffc6988 vocab=1ce02c71
-/
theorem lt_of_next_eq_inl {S : Type u} [PartialOrder S]
    (F : TwoSuccessor S) {x y : S} (h : F.next x = Sum.inl y) :
    x < y := by
  have hr := F.related x
  rw [h] at hr
  exact hr

/-- Terminal label and number of successor steps remaining.-/
def trace {S : Type u} [PartialOrder S] [Fintype S]
    (F : TwoSuccessor S) (x : S) : Fin 2 × ℕ :=
  match h : F.next x with
  | Sum.inr d => (d, 0)
  | Sum.inl y =>
      let p := trace F y
      (p.1, p.2 + 1)
termination_by (strictUpperFinset x).card
decreasing_by
  exact card_strictUpperFinset_lt_of_lt (F.lt_of_next_eq_inl h)

/--
@isnad1 id=eq.1h4v.s6.0fdb1189dd5a from=translated src=- shape=76f19694 vocab=aef1b0e6
-/
@[simp]
theorem trace_of_next_eq_inr {x : T} {d : Fin 2}
    (h : F.next x = Sum.inr d) :
    F.trace x = (d, 0) := by
  rw [trace.eq_1, h]

/--
@isnad1 id=eq.1h4v.s6.148fc7ca04d5 from=translated src=- shape=68e5e6a8 vocab=ec95eba3
-/
@[simp]
theorem trace_of_next_eq_inl {x y : T}
    (h : F.next x = Sum.inl y) :
    F.trace x = ((F.trace y).1, (F.trace y).2 + 1) := by
  rw [trace.eq_1, h]

/-- The terminal label together with the remaining path length uniquely
determines a vertex.-/
theorem eq_of_trace_eq {S : Type u} [PartialOrder S] [Fintype S]
    (F : TwoSuccessor S) {x y : S}
    (htrace : F.trace x = F.trace y) : x = y := by
  cases hx : F.next x with
  | inl x' =>
      cases hy : F.next y with
      | inl y' =>
          rw [F.trace_of_next_eq_inl hx,
            F.trace_of_next_eq_inl hy] at htrace
          have hfst := congrArg Prod.fst htrace
          have hsnd := congrArg Prod.snd htrace
          have htail : F.trace x' = F.trace y' := by
            apply Prod.ext
            · exact hfst
            · exact Nat.add_right_cancel hsnd
          have hxy : x' = y' := eq_of_trace_eq F htail
          apply F.next_injective
          rw [hx, hy, hxy]
      | inr d =>
          rw [F.trace_of_next_eq_inl hx,
            F.trace_of_next_eq_inr hy] at htrace
          have hsnd := congrArg Prod.snd htrace
          omega
  | inr d =>
      cases hy : F.next y with
      | inl y' =>
          rw [F.trace_of_next_eq_inr hx,
            F.trace_of_next_eq_inl hy] at htrace
          have hsnd := congrArg Prod.snd htrace
          omega
      | inr e =>
          rw [F.trace_of_next_eq_inr hx,
            F.trace_of_next_eq_inr hy] at htrace
          have hde : d = e := congrArg Prod.fst htrace
          apply F.next_injective
          rw [hx, hy, hde]
termination_by (strictUpperFinset x).card
decreasing_by
  exact card_strictUpperFinset_lt_of_lt (F.lt_of_next_eq_inl hx)

/-- The full two-terminal trace is injective.
@isnad1 id=injectiv.0h2v.s4.e321d21182d7 from=translated src=- shape=bb58814c vocab=e5d12dba
-/
theorem trace_injective (F : TwoSuccessor T) :
    Function.Injective F.trace := by
  intro x y h
  exact eq_of_trace_eq F h

/-- Along one terminal fiber, greater remaining path length means a smaller
poset element.
@isnad1 id=le.2h4v.s6.80d0cf9d3bb4 from=translated src=- shape=261ef04b vocab=cf23f396
-/
theorem le_of_trace_fst_eq_of_snd_le
    {S : Type u} [PartialOrder S] [Fintype S]
    (F : TwoSuccessor S) {x y : S}
    (hfst : (F.trace x).1 = (F.trace y).1)
    (hsnd : (F.trace y).2 ≤ (F.trace x).2) :
    x ≤ y := by
  cases hx : F.next x with
  | inl x' =>
      rw [F.trace_of_next_eq_inl hx] at hfst hsnd
      by_cases htail : (F.trace y).2 ≤ (F.trace x').2
      · exact (F.lt_of_next_eq_inl hx).le.trans
          (le_of_trace_fst_eq_of_snd_le F hfst htail)
      · have hfirst : (F.trace x).1 = (F.trace y).1 := by
          rw [F.trace_of_next_eq_inl hx]
          exact hfst
        have hsecond : (F.trace x).2 = (F.trace y).2 := by
          rw [F.trace_of_next_eq_inl hx]
          omega
        exact (F.eq_of_trace_eq (Prod.ext hfirst hsecond)).le
  | inr d =>
      rw [F.trace_of_next_eq_inr hx] at hfst hsnd
      have hfirst : (F.trace x).1 = (F.trace y).1 := by
        rw [F.trace_of_next_eq_inr hx]
        exact hfst
      have hsecond : (F.trace x).2 = (F.trace y).2 := by
        rw [F.trace_of_next_eq_inr hx]
        omega
      exact (F.eq_of_trace_eq (Prod.ext hfirst hsecond)).le
termination_by (strictUpperFinset x).card
decreasing_by
  exact card_strictUpperFinset_lt_of_lt (F.lt_of_next_eq_inl hx)

/-- Vertices with the same terminal label are comparable.
@isnad1 id=or.1h4v.s6.b7e1d841ddef from=translated src=- shape=a2092319 vocab=9a8a4b0a
-/
theorem comparable_of_trace_fst_eq (F : TwoSuccessor T) {x y : T}
    (hfst : (F.trace x).1 = (F.trace y).1) :
    x ≤ y ∨ y ≤ x := by
  rcases le_total (F.trace y).2 (F.trace x).2 with h | h
  · exact Or.inl (F.le_of_trace_fst_eq_of_snd_le hfst h)
  · exact Or.inr (F.le_of_trace_fst_eq_of_snd_le hfst.symm h)

/-- Fiber of the successor trace over one of the two terminal labels.-/
def terminalFiber (F : TwoSuccessor T) (d : Fin 2) : Set T :=
  {x | (F.trace x).1 = d}

/-- Each terminal fiber is a chain.
@isnad1 id=ischain.0h3v.s5.738c7925174a from=translated src=- shape=d77b2009 vocab=044fc94d
-/
theorem isChain_terminalFiber (F : TwoSuccessor T) (d : Fin 2) :
    IsChain (· ≤ ·) (terminalFiber F d) := by
  intro x hx y hy hxy
  exact F.comparable_of_trace_fst_eq (hx.trans hy.symm)

/-- The two terminal fibers cover the whole poset.
@isnad1 id=eq.0h2v.s6.2d5eac86e86d from=translated src=- shape=9d80445b vocab=70633161
-/
theorem terminalFiber_zero_union_one (F : TwoSuccessor T) :
    terminalFiber F 0 ∪ terminalFiber F 1 = Set.univ := by
  ext x
  simp only [Set.mem_union, terminalFiber, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  generalize hd : (F.trace x).1 = d
  fin_cases d <;> simp_all

end TwoSuccessor

/-- The Hall assignment as a bundled successor structure.
@isnad1 id=nonempty.1h1v.s4.848d51ae65a9 from=translated src=- shape=7dd860bb vocab=4956be64
-/
theorem exists_twoSuccessor
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    Nonempty (TwoSuccessor T) := by
  obtain ⟨f, hf, hrel⟩ := exists_injective_successor hno
  exact ⟨⟨f, hf, hrel⟩⟩

/-- Width-two Dilworth: a finite poset without a three-element antichain is
covered by two chains.
@isnad1 id=ex.1h1v.s6.01635e58b51a from=translated src=- shape=0b240e27 vocab=86034697
-/
theorem exists_two_chain_cover_of_no_threeAntichain
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    ∃ A B : Set T,
      A ∪ B = Set.univ ∧
        IsChain (· ≤ ·) A ∧ IsChain (· ≤ ·) B := by
  let F := Classical.choice (exists_twoSuccessor hno)
  exact ⟨F.terminalFiber 0, F.terminalFiber 1,
    F.terminalFiber_zero_union_one,
    F.isChain_terminalFiber 0, F.isChain_terminalFiber 1⟩

section Schur

variable {k : Type u} [Field k]

/-- If the indexing poset has width at most two, every Schur poset space is
one-dimensional.
@isnad1 id=eq.2h3v.s6.9e1a90bf5911 from=translated src=- shape=d39b1af9 vocab=ae7a0431
-/
theorem finrank_eq_one_of_isSchur_of_no_threeAntichain
    (X : Obj k T) (hschur : IsSchur k T X)
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    Module.finrank k X = 1 := by
  obtain ⟨A, B, hcover, hA, hB⟩ :=
    exists_two_chain_cover_of_no_threeAntichain hno
  exact finrank_eq_one_of_isSchur_of_two_chain_cover
    X hschur A B hcover hA hB

/-- Consequently, every Schur poset space of dimension at least two forces a
three-element antichain in the indexing poset.
@isnad1 id=ex.2h3v.s6.3baff2f88309 from=translated src=- shape=9d3c046c vocab=aedfc970
-/
theorem exists_threeAntichain_of_isSchur_of_two_le_finrank
    (X : Obj k T) (hschur : IsSchur k T X)
    (hrank : 2 ≤ Module.finrank k X) :
    ∃ a b c : T, IsThreeAntichain a b c := by
  by_contra hnot
  simp only [not_exists] at hnot
  have hone := finrank_eq_one_of_isSchur_of_no_threeAntichain
    X hschur hnot
  omega

end Schur

end MagnitudeConjecture.PosetSpace
