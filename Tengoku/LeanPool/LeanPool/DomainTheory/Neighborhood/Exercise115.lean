/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Basic
public import Tengoku

/-!
# Exercise 1.15 (Scott 1981, PRG-19, §1) — non-isomorphic "finite-only" domains

"Construct non-isomorphic infinite domains where all elements are finite but where
there are no
infinite chains `⟨xₙ⟩` of elements with `xₙ ⊏ xₙ₊₁` for all `n`."

We give two neighbourhood systems over `Δ = ℕ`:

* **`flat`** — `𝒟 = {ℕ} ∪ {{n} ∣ n ∈ ℕ}` (the *flat* domain). Its elements are
exactly `⊥` and the
  pairwise-incomparable atoms `↑{n}` (`flat_classify`), so **all elements are
  finite/principal**
  (`flat_all_finite`), every atom is **maximal** (`flat_atom_maximal`), there is
  **no 3-chain**
  (`flat_no_three_chain`) and hence **no infinite ascending chain**
  (`flat_no_infinite_chain`). It is
  infinite (`flat_infinite`).

* **`stem`** — `𝒟 = {ℕ, {0,1}} ∪ {{n} ∣ n ∈ ℕ}` (a flat domain with one length-3
"stem"). It
  contains a strict **3-chain** `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` (`stem_three_chain`). It too
  has only finite
  elements and no infinite ascending chain (same flat-with-stem classification;
  the formally decisive
  difference from `flat` is the 3-chain).

Since an order-isomorphism transports strict chains, the 3-chain in `stem` would
force a 3-chain in
`flat`, which has none: hence `¬ (flat ≅ᴰ stem)` (`not_isomorphic`). Two infinite,
finite-element,
chain-bounded domains that are *not* isomorphic.

The classification results are *classical* (they decide whether an element
contains some atom); the
constructions and the non-isomorphism argument are otherwise elementary.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise115

open Domain.Neighborhood NeighborhoodSystem

/-- `{n} ∩ {m} = ∅` for `n ≠ m`.
@isnad1 id=eq.1h2v.s5.9f8d110d68b4 from=translated src=- shape=93dee3ae vocab=ea1dd626
-/
theorem singleton_disjoint {n m : ℕ} (h : n ≠ m) : ({n} : Set ℕ) ∩ {m} = ∅ := by
  simp_all

/-! ## The flat domain `flat`. -/

/-- Neighbourhoods of the flat domain: `Δ = ℕ` together with all singletons. -/
def flatMem (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

/--
@isnad1 id=nestedor.0h0v.s1.2b603a9e06ca from=translated src=- shape=25b03439 vocab=07d4c557
-/
theorem flatNOD : NestedOrDisjoint flatMem := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

/-- **Exercise 1.15 — the flat domain.** `𝒟 = {ℕ} ∪ {{n}}`. -/
def flat : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint flatMem Set.univ (Or.inl rfl) flatNOD (fun _ => Set.subset_univ _)

/--
@isnad1 id=iff.0h1v.s4.ce6acc8275bf from=translated src=- shape=aaa99f80 vocab=b5e64c89
-/
@[simp] theorem flat_mem {X : Set ℕ} : flat.mem X ↔ X = Set.univ ∨ ∃ n, X = {n} := Iff.rfl

/--
@isnad1 id=eq.0h0v.s3.9e6dbf8fcbb7 from=translated src=- shape=d672ce25 vocab=e747de8d
-/
@[simp] theorem flat_master : flat.master = Set.univ := rfl

/--
@isnad1 id=not.0h0v.s3.29d46a2aadd8 from=translated src=- shape=7fa2a4d3 vocab=801195c0
-/
theorem flat_empty_not_mem : ¬ flat.mem (∅ : Set ℕ) := by
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty n)

/-- The atom `↑{n}` (a finite element).
@isnad1 id=mem.0h1v.s3.f2d7337368d0 from=translated src=- shape=4c8e040a vocab=48f05727
-/
theorem flat_mem_singleton (n : ℕ) : flat.mem {n} := Or.inr ⟨n, rfl⟩

/-- **Flat classification.** Every element is `⊥` or an atom `↑{n}`. *Classical.*
@isnad1 id=or.0h1v.s5.bc0e8cfe3b42 from=translated src=- shape=bbe19864 vocab=f69c13b9
-/
theorem flat_classify (x : flat.Element) :
    x = flat.bot ∨ ∃ n, x = flat.principal (flat_mem_singleton n) := by
  classical
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    have huniq : ∀ m, x.mem {m} → m = n := by
      intro m hm
      by_contra hmn
      have hi : x.mem (({m} : Set ℕ) ∩ {n}) := x.inter_mem hm hn
      rw [singleton_disjoint hmn] at hi
      exact flat_empty_not_mem (x.sub hi)
    apply Element.ext
    intro W
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · exact ⟨Or.inl rfl, Set.subset_univ _⟩
      · simp_all
    · rintro ⟨hWmem, hsub⟩
      exact x.up_mem hn hWmem hsub
  · refine Or.inl ?_
    apply Element.ext
    intro W
    rw [flat.mem_bot]
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd ⟨k, hx⟩ h
    · rintro rfl
      exact x.master_mem

/-- **Flat: every atom is maximal (total).**
@isnad1 id=eq.1h2v.s5.611f3174577e from=translated src=- shape=eb41788a vocab=2336e48b
-/
theorem flat_atom_maximal (n : ℕ) (y : flat.Element)
    (hle : flat.principal (flat_mem_singleton n) ≤ y) :
    y = flat.principal (flat_mem_singleton n) := by
  rcases flat_classify y with rfl | ⟨m, rfl⟩
  · exfalso
    have hmem : flat.bot.mem {n} := hle {n} ⟨flat_mem_singleton n, subset_rfl⟩
    simp_all
  · have hsub : ({m} : Set ℕ) ⊆ {n} :=
      (flat.principal_le_iff (flat_mem_singleton n) (flat_mem_singleton m)).mp hle
    simp_all

/-- **Flat has no strict 3-chain** (`a ⊏ b ⊏ c` is impossible): `⊥` is least and
atoms are
maximal.
@isnad1 id=not.0h0v.s5.4487ae15ab35 from=translated src=- shape=8bfcea47 vocab=22fd5d81
-/
theorem flat_no_three_chain : ¬ ∃ a b c : flat.Element, a < b ∧ b < c := by
  rintro ⟨a, b, c, hab, hbc⟩
  rcases flat_classify b with rfl | ⟨n, rfl⟩
  · exact absurd (le_antisymm hab.le (flat.bot_le a)) (ne_of_lt hab)
  · exact (ne_of_lt hbc) (flat_atom_maximal n c hbc.le).symm

/-- **Flat has no infinite ascending chain.**
@isnad1 id=not.0h0v.s4.532d993be593 from=translated src=- shape=4d6c0965 vocab=fdd1e524
-/
theorem flat_no_infinite_chain : ¬ ∃ f : ℕ → flat.Element, StrictMono f := by
  rintro ⟨f, hf⟩
  exact flat_no_three_chain
    ⟨f 0, f 1, f 2, hf (by norm_num), hf (by norm_num)⟩

/-- **All elements of `flat` are finite** (principal).
@isnad1 id=ex.0h1v.s4.a6e6e8393723 from=translated src=- shape=be70e30e vocab=f54101fb
-/
theorem flat_all_finite (x : flat.Element) :
  ∃ (X : Set ℕ) (h : flat.mem X), x = flat.principal h := by
  rcases flat_classify x with rfl | ⟨n, rfl⟩
  · exact ⟨flat.master, flat.master_mem, rfl⟩
  · exact ⟨{n}, flat_mem_singleton n, rfl⟩

/-- `flat` is infinite: the atoms `↑{n}` are pairwise distinct.
@isnad1 id=injectiv.0h0v.s4.a98698cbd2f1 from=translated src=- shape=d20d29b0 vocab=51243232
-/
theorem flat_infinite : Function.Injective (fun n => flat.principal (flat_mem_singleton n)) := by
  intro n m h
  have := flat.principal_injective (flat_mem_singleton n) (flat_mem_singleton m) h
  exact Set.singleton_injective this

/-! ## The "stem" domain `stem`. -/

/-- Neighbourhoods of the stem domain: `Δ = ℕ`, the pair `{0,1}`, and all
singletons. -/
def stemMem (X : Set ℕ) : Prop := X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n}

/--
@isnad1 id=nestedor.0h0v.s1.9aa996df5f7a from=translated src=- shape=25b03439 vocab=c0c58f49
-/
theorem stemNOD : NestedOrDisjoint stemMem := by
  have pair_single : ∀ m : ℕ, ({m} : Set ℕ) ⊆ {0, 1} ∨ ({0, 1} : Set ℕ) ∩ {m} = ∅ := by
    intro m
    by_cases h : m = 0 ∨ m = 1
    · simp_all
    · simp_all
  rintro X Y (rfl | rfl | ⟨n, rfl⟩) (rfl | rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · exact Or.inl (subset_refl _)
  · simp_all
  · exact Or.inl (Set.subset_univ _)
  · rcases pair_single n with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

/-- **Exercise 1.15 — the stem domain.** `𝒟 = {ℕ, {0,1}} ∪ {{n}}`. -/
def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

/--
@isnad1 id=iff.0h1v.s5.188471417712 from=translated src=- shape=21e32988 vocab=d0ca8717
-/
@[simp] theorem stem_mem {X : Set ℕ} :
    stem.mem X ↔ X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n} := Iff.rfl

/--
@isnad1 id=mem.0h0v.s2.3053bda1190f from=translated src=- shape=f463f024 vocab=74720aef
-/
theorem stem_mem_univ : stem.mem Set.univ := Or.inl rfl
/--
@isnad1 id=mem.0h0v.s4.d130fa716a60 from=translated src=- shape=03ed56d2 vocab=6f52cebf
-/
theorem stem_mem_pair : stem.mem {0, 1} := Or.inr (Or.inl rfl)
/--
@isnad1 id=mem.0h0v.s3.fc4c2339541e from=translated src=- shape=805367dd vocab=e0096763
-/
theorem stem_mem_zero : stem.mem {0} := Or.inr (Or.inr ⟨0, rfl⟩)

/-- A strict step between principal filters of `stem`: `Y ⊊ X` (proper) gives `↑X
⊏ ↑Y`.
@isnad1 id=lt.4h2v.s5.dea866fa3bc8 from=translated src=- shape=ede61b0e vocab=6c182f73
-/
theorem stem_principal_lt {X Y : Set ℕ} (hX : stem.mem X) (hY : stem.mem Y)
    (hYX : Y ⊆ X) (hne : X ≠ Y) : stem.principal hX < stem.principal hY := by
  rw [lt_iff_le_and_ne]
  refine ⟨(stem.principal_le_iff hX hY).mpr hYX, ?_⟩
  intro he
  exact hne (stem.principal_injective hX hY he)

/-- **Stem contains a strict 3-chain** `⊥ = ↑ℕ ⊏ ↑{0,1} ⊏ ↑{0}` — the structural
feature that
distinguishes it from `flat`.
@isnad1 id=ex.0h0v.s5.43ab65b4669c from=translated src=- shape=21c3d438 vocab=236f46aa
-/
theorem stem_three_chain : ∃ a b c : stem.Element, a < b ∧ b < c := by
  refine ⟨stem.principal stem_mem_univ, stem.principal stem_mem_pair,
    stem.principal stem_mem_zero, ?_, ?_⟩
  · refine stem_principal_lt stem_mem_univ stem_mem_pair (Set.subset_univ _) ?_
    intro h
    have : (2 : ℕ) ∈ ({0, 1} : Set ℕ) := h ▸ Set.mem_univ 2
    simp at this
  · refine stem_principal_lt stem_mem_pair stem_mem_zero
      (Set.singleton_subset_iff.mpr (by simp)) ?_
    intro h
    have : (1 : ℕ) ∈ ({0} : Set ℕ) := h ▸ (by simp : (1 : ℕ) ∈ ({0, 1} : Set ℕ))
    simp at this

/-! ## Non-isomorphism. -/

/-- **Exercise 1.15.** `flat` and `stem` are *not* isomorphic: an
order-isomorphism would transport
`stem`'s strict 3-chain `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` back to a strict 3-chain in `flat`,
which has none.
@isnad1 id=not.0h0v.s2.53c4cd2b0992 from=translated src=- shape=d444f804 vocab=1b344a58
-/
theorem not_isomorphic : ¬ (flat ≅ᴰ stem) := by
  rintro ⟨e⟩
  obtain ⟨a, b, c, hab, hbc⟩ := stem_three_chain
  exact flat_no_three_chain
    ⟨e.symm a, e.symm b, e.symm c, e.symm.lt_iff_lt.mpr hab, e.symm.lt_iff_lt.mpr hbc⟩

end Domain.Neighborhood.Exercise115
