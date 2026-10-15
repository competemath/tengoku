/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
module

public import Tengoku.LeanPool.LeanPool.NashWilliams.Combinatorics.Front.Defs
public import Tengoku

/-!
# The tree of a front is well-founded

The *tree* of a front `F` is the set of all prefixes (initial segments) of elements of `F`, ordered
by *proper end-extension* (`treeExt F a b` : `a` properly extends `b`). This file proves that this
relation is **well-founded**, so a front has an ordinal `rank`.

Well-foundedness is proved directly, by showing there is no infinite descending chain. A
descending chain is an ascending tower `f 0 ⊏ f 1 ⊏ ⋯` of proper extensions inside the tree.
Its lengths grow without bound, so the tower has a limit `b : ℕ → ℕ`, a strictly increasing
subsequence of `M`. By Density some `t ∈ F` is an initial segment of `b`; extending it by one
more entry of `b` lands inside some `u ∈ F` with `t <+: u`, so Incomparability forces `t = u` —
impossible, as `u` is
strictly longer.

## Main results

* `Front.exists_strictMono_comp`: a strictly monotone `b` with `range b ⊆ range M` is a
  subsequence `M ∘ g` of `M` (the enumeration bridge).
* `Front.IsFront.wellFounded_treeExt`: proper end-extension is well-founded on the tree of a front.
* `Front.IsFront.rank`: the ordinal rank of a front.
* `Front.powK_rank`: the uniform front `[M]^k` has rank `k`.
* `Front.schreier_rank`: the Schreier front has rank `ω`.
-/

@[expose] public section

open Set List Ordinal

universe u

noncomputable section

namespace Front

/-- The tree of a front `F`: all prefixes (initial segments) of elements of `F`. -/
def tree (F : Set (List ℕ)) : Set (List ℕ) :=
  {s | ∃ t ∈ F, s <+: t}

/-- Proper end-extension inside the tree of `F`: `treeExt F a b` holds when `a` properly extends
`b` and both lie in the tree. Its well-foundedness is what allows ranking a front. Note the
recursion direction: `WellFounded.rank (treeExt F) s` is the supremum of `succ (rank s')` over
the proper extensions `s'` of `s`, matching the usual rank of a front. -/
def treeExt (F : Set (List ℕ)) (a b : List ℕ) : Prop :=
  a ∈ tree F ∧ b ∈ tree F ∧ b <+: a ∧ b ≠ a

/-- If every finite initial segment of `b` is strictly increasing, then `b` is strictly
monotone.
@isnad1 id=strictmo.1h1v.s4.0a57095eca29 from=translated src=- shape=f84ba96e vocab=c8326ab4
-/
theorem strictMono_of_pairwise_map {b : ℕ → ℕ}
    (h : ∀ n, ((List.range n).map b).Pairwise (· < ·)) : StrictMono b := by
  intro i j hij
  have hlen : ((List.range (j + 1)).map b).length = j + 1 := by simp
  have hp := (List.pairwise_iff_getElem.mp (h (j + 1))) i j (by omega) (by omega) hij
  simpa using hp

/-- **Enumeration bridge.** A strictly monotone `b` whose range is contained in that of a
strictly monotone `M` is a subsequence `M ∘ g` of `M`, for a unique strictly monotone `g`.
@isnad1 id=ex.3h2v.s6.b5284ee43954 from=translated src=- shape=fd765489 vocab=ab250355
-/
theorem exists_strictMono_comp {M b : ℕ → ℕ} (hM : StrictMono M) (hb : StrictMono b)
    (hsub : ∀ i, b i ∈ Set.range M) : ∃ g : ℕ → ℕ, StrictMono g ∧ M ∘ g = b := by
  choose g hg using hsub
  refine ⟨g, ?_, funext hg⟩
  intro i j hij
  have : M (g i) < M (g j) := by rw [hg, hg]; exact hb hij
  exact hM.lt_iff_lt.mp this

/-- **Proper end-extension is well-founded on the tree of a front.** Proved directly: there is no
infinite descending chain.
@isnad1 id=wellfoun.1h2v.s4.2a7fdf979e25 from=translated src=- shape=178dfd20 vocab=35704a3a
-/
theorem IsFront.wellFounded_treeExt {F : Set (List ℕ)} {M : ℕ → ℕ} (hF : IsFront F M) :
    WellFounded (treeExt F) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  -- `hf n : treeExt F (f (n+1)) (f n)`, i.e. `f 0 ⊏ f 1 ⊏ ⋯` is an ascending tower.
  have hmem : ∀ n, f n ∈ tree F := fun n => (hf n).2.1
  have hpre : ∀ n, f n <+: f (n + 1) := fun n => (hf n).2.2.1
  have hne : ∀ n, f n ≠ f (n + 1) := fun n => (hf n).2.2.2
  -- The lengths strictly increase, so `n ≤ |f n|`.
  have hlt : ∀ n, (f n).length < (f (n + 1)).length := by
    intro n
    rcases lt_or_eq_of_le (hpre n).length_le with h | h
    · exact h
    · exact absurd ((hpre n).eq_of_length h) (hne n)
  have hlen_ge : ∀ n, n ≤ (f n).length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hlt k; omega
  -- The tower is nested.
  have hnest : ∀ {n m : ℕ}, n ≤ m → f n <+: f m := by
    intro n m h
    induction h with
    | refl => exact List.prefix_rfl
    | step _ ih => exact ih.trans (hpre _)
  -- Each node is strictly increasing (a sublist of an element of `F`).
  have hsorted : ∀ n, (f n).Pairwise (· < ·) := by
    intro n
    obtain ⟨u, hu, hpu⟩ := hmem n
    exact List.Pairwise.sublist hpu.sublist (hF.sorted u hu)
  -- The limit `b` of the tower.
  have hlen1 : ∀ i, i < (f (i + 1)).length := fun i =>
    lt_of_lt_of_le (Nat.lt_succ_self i) (hlen_ge (i + 1))
  set b : ℕ → ℕ := fun i => (f (i + 1))[i]'(hlen1 i) with hb_def
  -- `b` agrees with every node long enough to reach the index.
  have hagree : ∀ {i m : ℕ}, i + 1 ≤ m → (h : i < (f m).length) → (f m)[i] = b i := by
    intro i m hm _
    exact ((hnest hm).getElem (hlen1 i)).symm
  -- Every initial segment of `b` is a prefix of a sufficiently long node.
  have hb_pre : ∀ {n m : ℕ}, n ≤ m → (List.range n).map b <+: f m := by
    intro n m hnm
    have hnlen : n ≤ (f m).length := le_trans hnm (hlen_ge m)
    have heq : (List.range n).map b = (f m).take n := by
      apply List.ext_getElem
      · simp [Nat.min_eq_left hnlen]
      · intro i h1 _
        have hi : i < n := by simpa using h1
        rw [List.getElem_take, getElem_map, getElem_range]
        exact (hagree (by omega) (lt_of_lt_of_le hi hnlen)).symm
    rw [heq]
    exact List.take_prefix n (f m)
  -- `b` is strictly increasing with entries in `M`.
  have hbmono : StrictMono b := strictMono_of_pairwise_map fun n =>
    List.Pairwise.sublist (hb_pre (le_refl n)).sublist (hsorted n)
  have hbmem : ∀ i, b i ∈ Set.range M := by
    intro i
    obtain ⟨u, hu, hpu⟩ := hmem (i + 1)
    exact hF.subM u hu (b i) (hpu.subset (List.getElem_mem (hlen1 i)))
  -- Apply Density: some `t ∈ F` is an initial segment of `b`.
  obtain ⟨g, hg, hgb⟩ := exists_strictMono_comp hF.mono hbmono hbmem
  obtain ⟨t, ht, hInit⟩ := hF.dense g hg
  rw [hgb] at hInit
  -- Extend `t` by one entry of `b`; it lands inside some `u ∈ F`.
  obtain ⟨u, hu, hpu⟩ := hmem (t.length + 1)
  have htpre : t <+: (List.range (t.length + 1)).map b := by
    conv_lhs => rw [hInit]
    exact (range_prefix_range (Nat.le_succ _)).map b
  have hbu : (List.range (t.length + 1)).map b <+: f (t.length + 1) := hb_pre (le_refl _)
  have hEq : t = u := hF.incomp t ht u hu ((htpre.trans hbu).trans hpu)
  -- But then `u = t` is a prefix of the strictly longer `f (|t|+1)`.
  have h1 : t.length + 1 ≤ (f (t.length + 1)).length := hlen_ge _
  have h2 : (f (t.length + 1)).length ≤ u.length := hpu.length_le
  have h3 : u.length = t.length := by rw [hEq]
  omega

variable {F : Set (List ℕ)} {M : ℕ → ℕ}

/-- The root `[]` is in the tree of any front (fronts are nonempty by Density).
@isnad1 id=mem.1h2v.s4.2f42404a48d7 from=translated src=- shape=3aa1e196 vocab=8eb29e41
-/
theorem IsFront.nil_mem_tree (hF : IsFront F M) : [] ∈ tree F := by
  obtain ⟨t, ht, _⟩ := hF.dense id strictMono_id
  exact ⟨t, ht, List.nil_prefix⟩

/-- `M` being a strictly monotone enumeration, there is an element of `M` above any bound.
@isnad1 id=ex.1h2v.s5.55ce96c2f9a4 from=translated src=- shape=29bdf6b8 vocab=450f0145
-/
theorem exists_gt_range (hM : StrictMono M) (n : ℕ) : ∃ x ∈ Set.range M, n < x :=
  (Set.infinite_range_of_injective hM.injective).exists_gt n

/-- An increasing list contained in `M` can be extended by one further element of `M`.
@isnad1 id=ex.1h2v.s5.19d11ade17f5 from=translated src=- shape=47dbedf6 vocab=2976e9df
-/
theorem exists_extend_gt (hM : StrictMono M) (s : List ℕ) :
    ∃ x ∈ Set.range M, ∀ y ∈ s, y < x := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_range hM (s.toFinset.sup id)
  refine ⟨x, hx, fun y hy => ?_⟩
  exact lt_of_le_of_lt (Finset.le_sup (f := id) (List.mem_toFinset.mpr hy)) hlt

/-- Any increasing list in `M` extends to an increasing list in `M` of any prescribed length.
@isnad1 id=ex.4h3v.s6.d2638863dd02 from=translated src=- shape=e82da753 vocab=5aaef189
-/
theorem exists_extend_len (hM : StrictMono M) (L : ℕ) :
    ∀ (s : List ℕ), s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L := by
  suffices H : ∀ d s, s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      L - s.length = d → s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L by
    intro s hs hsM hL; exact H _ s hs hsM rfl hL
  intro d
  induction d with
  | zero => intro s hs hsM hd hL; exact ⟨s, List.prefix_rfl, hs, hsM, by omega⟩
  | succ e ih =>
    intro s hs hsM hd hL
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s
    have hs' : (s ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt a ha
    have hs'M : ∀ z ∈ s ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    obtain ⟨t, hpre, ht, htM, htlen⟩ := ih (s ++ [x]) hs' hs'M (by simp; omega) (by simp; omega)
    exact ⟨t, (List.prefix_append s [x]).trans hpre, ht, htM, htlen⟩

/-- Membership in the tree of `[M]^k`: increasing lists in `M` of length at most `k`.
@isnad1 id=iff.1h3v.s6.527727926d88 from=translated src=- shape=ebef6e7e vocab=afa26c24
-/
theorem mem_tree_powK (hM : StrictMono M) {k : ℕ} {s : List ℕ} :
    s ∈ tree (powK M k) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧ s.length ≤ k := by
  constructor
  · rintro ⟨t, ⟨htlen, htp, htM⟩, hpre⟩
    exact ⟨List.Pairwise.sublist hpre.sublist htp, fun x hx => htM x (hpre.subset hx),
      le_trans hpre.length_le (le_of_eq htlen)⟩
  · rintro ⟨hs, hsM, hlen⟩
    obtain ⟨t, hpre, ht, htM, htlen⟩ := exists_extend_len hM k s hs hsM hlen
    exact ⟨t, ⟨htlen, ht, htM⟩, hpre⟩

/-- Membership in the tree of the Schreier front.
@isnad1 id=iff.1h2v.s6.d8d3fad4fa0d from=translated src=- shape=4b08009e vocab=0a65ef70
-/
theorem mem_tree_schreier (hM : StrictMono M) {s : List ℕ} :
    s ∈ tree (schreier M) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧
        (∀ a, s.head? = some a → s.length ≤ a + 1) := by
  constructor
  · rintro ⟨u, ⟨⟨c, huc, hulen⟩, hup, huM⟩, hpre⟩
    refine ⟨List.Pairwise.sublist hpre.sublist hup, fun x hx => huM x (hpre.subset hx), ?_⟩
    intro a hsa
    have hsne : s ≠ [] := by rintro rfl; simp at hsa
    have huhead : u.head? = some a := by rw [hpre.head_eq hsne]; exact hsa
    have hca : c = a := Option.some.inj (huc.symm.trans huhead)
    calc s.length ≤ u.length := hpre.length_le
      _ = c + 1 := hulen
      _ = a + 1 := by rw [hca]
  · rintro ⟨hs, hsM, hcase⟩
    rcases eq_or_ne s [] with rfl | hne
    · exact (isFront_schreier hM).nil_mem_tree
    · obtain ⟨a, hsa⟩ : ∃ a, s.head? = some a := by
        cases s with
        | nil => exact absurd rfl hne
        | cons c t => exact ⟨c, rfl⟩
      have hlen : s.length ≤ a + 1 := hcase a hsa
      obtain ⟨t, hpre, ht, htM, htlen⟩ := exists_extend_len hM (a + 1) s hs hsM hlen
      have hthead : t.head? = some a := by rw [hpre.head_eq hne]; exact hsa
      exact ⟨t, ⟨⟨a, hthead, htlen⟩, ht, htM⟩, hpre⟩

end Front
