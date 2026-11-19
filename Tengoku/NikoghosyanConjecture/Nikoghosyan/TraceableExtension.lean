/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.InducedCutTransport
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.Profiles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/TraceableExtension.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Manuscript `prof:prop:traceable`: toughness of a Hamiltonian block extended
by a disjoint traceable induced subgraph, using actual original cross-edges
and actual nonempty rows contained in no tight set of the cycle support.

This does not assume a complete join, pair-toughness, protected paths, or
one-vertex insertion. Hamiltonian prefix insertion is not claimed.
-/


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Actual H-profile of an outside vertex: original neighbours in `H`.-/
noncomputable def rowProfile (H : Finset V) (v : V) : Finset V :=
  H.filter fun x => G.Adj v x

/--
@isnad1 id=iff.0h5v.s5.aeb691aadf2f from=translated src=- shape=395e3153 vocab=f98b6eec
-/
lemma mem_rowProfile_iff {H : Finset V} {v x : V} :
    x ∈ rowProfile (G := G) H v ↔ x ∈ H ∧ G.Adj v x := by
  simp [rowProfile]

/--
@isnad1 id=le.0h4v.s5.da049ff4dfb4 from=translated src=- shape=a532f79f vocab=71a6b8ad
-/
lemma rowProfile_subset (H : Finset V) (v : V) :
    rowProfile (G := G) H v ⊆ H :=
  filter_subset _ _

/-- `A` is contained in no tight set of the Hamiltonian support `H`.-/
def NoTightContainer (G : SimpleGraph V) (H A : Finset V) : Prop :=
  ∀ S : Finset V,
    S ⊆ H →
      componentCount G (H \ S) = S.card →
        ¬ A ⊆ S

/--
@isnad1 id=not.1h4v.s5.9e30959b702a from=translated src=- shape=faae39dc vocab=fe9b8e62
-/
lemma NoTightContainer.not_exists {H A : Finset V}
    (h : NoTightContainer G H A) :
    ¬ ∃ S : Finset V, Cograph.Tight (G := G) H S ∧ A ⊆ S := by
  intro ⟨S, hT, hA⟩
  exact h S hT.1 hT.2 hA

/--
@isnad1 id=or.11h8v.s7.5b4454fd8ac9 from=translated src=- shape=2af4a004 vocab=d5180111
-/
lemma NoInducedP4UnionP1On_of {J : Finset V}
    (h : NoInducedP4UnionP1 G) :
    ∀ ⦃a b c d x : V⦄,
      a ∈ J → b ∈ J → c ∈ J → d ∈ J → x ∈ J →
      InducedP4 G a b c d →
      x ≠ a → x ≠ b → x ≠ c → x ≠ d →
        G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d :=
  fun _ _ _ _ _ _ _ _ _ _ hp hxa hxb hxc hxd => h hp hxa hxb hxc hxd

/-- An induced `P₄` in `H` minus the profile of an outside vertex `v`,
together with `v`, would be an induced `P₄ ∪ P₁` in `H ∪ R`.
@isnad1 id=iscograp.3h5v.s7.704eb2c7530e from=translated src=- shape=79a98e1f vocab=f82ad82b
-/
lemma isCograph_sdiff_rowProfile {H R : Finset V} {v : V}
    (hdisj : Disjoint H R) (hv : v ∈ R)
    (hOn : ∀ ⦃a b c d x : V⦄,
      a ∈ H ∪ R → b ∈ H ∪ R → c ∈ H ∪ R → d ∈ H ∪ R → x ∈ H ∪ R →
      InducedP4 G a b c d →
      x ≠ a → x ≠ b → x ≠ c → x ≠ d →
        G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d) :
    IsCograph G (H \ rowProfile (G := G) H v) := by
  intro a b c d ha hb hc hd hp
  have hA : a ∈ H := (mem_sdiff.1 ha).1
  have hB : b ∈ H := (mem_sdiff.1 hb).1
  have hC : c ∈ H := (mem_sdiff.1 hc).1
  have hD : d ∈ H := (mem_sdiff.1 hd).1
  have nAdj {y : V} (hy : y ∈ H \ rowProfile (G := G) H v) : ¬ G.Adj v y := by
    have : y ∉ rowProfile (G := G) H v := (mem_sdiff.1 hy).2
    intro hadj
    exact this ((mem_rowProfile_iff (G := G)).2 ⟨(mem_sdiff.1 hy).1, hadj⟩)
  have hvH : v ∉ H := disjoint_right.1 hdisj hv
  have hne {y : V} (hyH : y ∈ H) : v ≠ y := fun h => hvH (h ▸ hyH)
  have : ¬ (G.Adj v a ∨ G.Adj v b ∨ G.Adj v c ∨ G.Adj v d) := by
    simp [nAdj ha, nAdj hb, nAdj hc, nAdj hd]
  exact this <|
    hOn (mem_union.2 (Or.inl hA)) (mem_union.2 (Or.inl hB))
      (mem_union.2 (Or.inl hC)) (mem_union.2 (Or.inl hD))
      (mem_union.2 (Or.inr hv)) hp (hne hA) (hne hB) (hne hC) (hne hD)

/--
@isnad1 id=eq.0h3v.s4.256bc55ac615 from=translated src=- shape=792fc85c vocab=8c4d068f
-/
lemma componentCount_cycle_eq_one (c : GraphCycle G) :
    componentCount G c.support = 1 := by
  obtain ⟨p, hp, _⟩ := Cograph.exists_spanning_path_from c c.start_mem_support
  simpa [hp] using componentCount_eq_one_of_path p

/--
@isnad1 id=le.2h4v.s5.3a42b15513d5 from=translated src=- shape=43356326 vocab=ec2e52ec
-/
lemma componentCount_cycle_sdiff_le (c : GraphCycle G) {S : Finset V}
    (hS : S ⊆ c.support) (hSne : S.Nonempty) :
    componentCount G (c.support \ S) ≤ S.card := by
  obtain ⟨x, hxS⟩ := hSne
  obtain ⟨p, hp, hs, _hadj⟩ := Cograph.exists_spanning_path_from c (hS hxS)
  have hE : Eligible G c.support x := by
    have hends := Cograph.Eligible_of_support_ends p hp
    simpa [hs] using hends.1
  have hpU : pathCoverNumber G c.support = 1 :=
    Cograph.pathCoverNumber_eq_one_of_support p hp
  have hle := componentCount_sdiff_le_of_eligible (G := G) hS hxS hE
  have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.2 ⟨x, hxS⟩)
  omega

/-- Manuscript `prof:prop:traceable`, first assertion: the induced union of
a genuine original cycle support and a disjoint original path support is
1-tough on that union, given nonempty rows contained in no tight set.
@isnad1 id=onetough.2h4v.s6.6c34d9418860 from=translated src=- shape=1987f218 vocab=5b095993
-/
theorem oneToughOn_of_traceable_extension
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v)) :
    OneToughOn G (c.support ∪ r.support) := by
  intro ST hST h2
  set H := c.support
  set R := r.support
  set S := ST ∩ H
  set T := ST ∩ R
  have hS : S ⊆ H := inter_subset_right
  have hT : T ⊆ R := inter_subset_right
  have hcard : ST.card = S.card + T.card := card_cut_split hdisj hST
  have hrem : (H ∪ R) \ ST = (H \ S) ∪ (R \ T) := by
    nth_rw 1 [inter_union_eq_of_subset_union hST]
    exact union_sdiff_of_disjoint hdisj hS hT
  rw [hrem] at h2 ⊢
  have hpath : componentCount G (R \ T) ≤ T.card + 1 :=
    componentCount_path_sdiff_le r hT
  by_cases hSempty : S = ∅
  · have hHS : H \ S = H := by simp [hSempty]
    rw [hHS] at h2 ⊢
    have hH : componentCount G H = 1 := componentCount_cycle_eq_one c
    have hatt : ∀ w ∈ R \ T, ∃ u ∈ H, G.Adj w u := by
      intro w hw
      have hwR : w ∈ R := (mem_sdiff.1 hw).1
      obtain ⟨u, hu⟩ := (hrow w hwR).1
      exact ⟨u, (mem_rowProfile_iff (G := G)).1 hu⟩
    have hle : componentCount G (H ∪ (R \ T)) ≤ 1 :=
      (componentCount_union_le_of_adj hatt).trans hH.le
    omega
  · have hSne : S.Nonempty := nonempty_iff_ne_empty.2 hSempty
    have hcycle : componentCount G (H \ S) ≤ S.card :=
      componentCount_cycle_sdiff_le c hS hSne
    by_cases hSeq : S = H
    · have hHS : H \ S = ∅ := by simp [hSeq]
      have hrem' : (H \ S) ∪ (R \ T) = R \ T := by simp [hHS]
      have hScard : 3 ≤ S.card := by
        have h3 : 3 ≤ H.card := c.three_le_card_support
        simpa [hSeq] using h3
      rw [hrem'] at h2 ⊢
      omega
    · by_cases hstrict : componentCount G (H \ S) < S.card
      · have hunion := componentCount_union_le G (H \ S) (R \ T)
        omega
      · have heq : componentCount G (H \ S) = S.card := by omega
        have hatt : ∀ w ∈ R \ T, ∃ u ∈ H \ S, G.Adj w u := by
          intro w hw
          have hwR : w ∈ R := (mem_sdiff.1 hw).1
          obtain ⟨_, hnt⟩ := hrow w hwR
          have hnot : ¬ rowProfile (G := G) H w ⊆ S := hnt S hS heq
          obtain ⟨u, huA, huS⟩ := not_subset.1 hnot
          have huH : u ∈ H := ((mem_rowProfile_iff (G := G)).1 huA).1
          have hadj : G.Adj w u := ((mem_rowProfile_iff (G := G)).1 huA).2
          exact ⟨u, mem_sdiff.2 ⟨huH, huS⟩, hadj⟩
        have hle : componentCount G ((H \ S) ∪ (R \ T)) ≤
            componentCount G (H \ S) :=
          componentCount_union_le_of_adj hatt
        omega

/-- `OneTough` of the actual induced union, via the support-cut bridge.
@isnad1 id=onetough.2h4v.s7.0ff6f04ae8b2 from=translated src=- shape=497b38c2 vocab=45afebb7
-/
theorem oneTough_induce_of_traceable_extension
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v)) :
    OneTough (G.induce ((c.support ∪ r.support : Finset V) : Set V)) :=
  (OneToughOn_iff_OneTough_induce (c.support ∪ r.support)).1
    (oneToughOn_of_traceable_extension c r hdisj hrow)

/-- If the host support is induced-`(P₄ ∪ P₁)`-free, each remainder
`H - A_v` is a cograph, and the no-tight-container hypothesis is
equivalent to the strict path-cover inequality `p(H - A_v) < |A_v|`.
@isnad1 id=iff.4h5v.s8.560a9352daf4 from=translated src=- shape=9149fa15 vocab=16298d9b
-/
theorem noTightContainer_iff_strict_pathCover
    (c : GraphCycle G) (r : GraphPath G) {v : V}
    (hdisj : Disjoint c.support r.support) (hv : v ∈ r.support)
    (hAne : (rowProfile (G := G) c.support v).Nonempty)
    (hJ : ∀ ⦃a b c' d x : V⦄,
      a ∈ c.support ∪ r.support →
        b ∈ c.support ∪ r.support →
          c' ∈ c.support ∪ r.support →
            d ∈ c.support ∪ r.support →
              x ∈ c.support ∪ r.support →
      InducedP4 G a b c' d →
      x ≠ a → x ≠ b → x ≠ c' → x ≠ d →
        G.Adj x a ∨ G.Adj x b ∨ G.Adj x c' ∨ G.Adj x d) :
    NoTightContainer G c.support (rowProfile (G := G) c.support v) ↔
      pathCoverNumber G (c.support \ rowProfile (G := G) c.support v) <
        (rowProfile (G := G) c.support v).card := by
  set H := c.support
  set A := rowProfile (G := G) c.support v
  have hAsub : A ⊆ H := rowProfile_subset (G := G) H v
  have hK : IsCograph G (H \ A) :=
    isCograph_sdiff_rowProfile (H := H) (R := r.support) hdisj hv hJ
  have hiff :=
    Cograph.canonical_saturated_container_of_canonical (G := G) c rfl hAsub hAne hK
  have hle : pathCoverNumber G (H \ A) ≤ A.card :=
    Cograph.pathCoverNumber_sdiff_le_card_of_cycle c rfl hAsub hAne
  constructor
  · intro hnt
    have hnotSat : ¬ Cograph.Saturated (G := G) H A := by
      intro hSat
      exact hnt.not_exists (hiff.2 hSat)
    have hne : pathCoverNumber G (H \ A) ≠ A.card := by
      intro h
      exact hnotSat h
    exact Nat.lt_of_le_of_ne hle hne
  · intro hlt S hS heq hAS
    have hSat : Cograph.Saturated (G := G) H A :=
      hiff.1 ⟨S, ⟨hS, heq⟩, hAS⟩
    have heq' : pathCoverNumber G (H \ A) = A.card := hSat
    have hlt' : pathCoverNumber G (H \ A) < A.card := hlt
    exact (lt_irrefl _ (heq' ▸ hlt'))

/--
@isnad1 id=iff.4h5v.s7.1d737f7bf274 from=translated src=- shape=7dc62d9f vocab=c9fbaf3a
-/
theorem noTightContainer_iff_strict_pathCover_of_host
    (c : GraphCycle G) (r : GraphPath G) {v : V}
    (hdisj : Disjoint c.support r.support) (hv : v ∈ r.support)
    (hAne : (rowProfile (G := G) c.support v).Nonempty)
    (hG : NoInducedP4UnionP1 G) :
    NoTightContainer G c.support (rowProfile (G := G) c.support v) ↔
      pathCoverNumber G (c.support \ rowProfile (G := G) c.support v) <
        (rowProfile (G := G) c.support v).card :=
  noTightContainer_iff_strict_pathCover c r hdisj hv hAne
    (fun _ _ _ _ _ _ _ _ _ _ hp hxa hxb hxc hxd => hG hp hxa hxb hxc hxd)

end Nikoghosyan
