import Tengoku.Erdos278.Erdos278.FixedGraph
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Data.Fintype.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

abbrev SeparationMask (r : ℕ) := Finset (PairIndex r)

/-- The actual pair set separated by one coordinate.-/
def separationMask {r : ℕ} {α : Type*} [DecidableEq α]
    (V : Finset (Fin r)) (f : Fin r → α) : SeparationMask r :=
  univ.filter (fun e => e.1.1 ∈ V ∧ e.1.2 ∈ V ∧ f e.1.1 ≠ f e.1.2)

/-- Recode the colors used on a finite support into any sufficiently large
finite alphabet, preserving exactly the equality pattern and its block count.
@isnad1 id=ex.2h5v.s7.ca23d3b94823 from=translated src=- shape=f8add1b0 vocab=f8cc5bcb
-/
theorem finite_support_relabel {r b : ℕ} {α : Type*} [DecidableEq α]
    (V : Finset (Fin r)) (f : Fin r → α) (hb : 0 < b)
    (hcard : (V.image f).card ≤ b) :
    ∃ g : Fin r → Fin b,
      (∀ i ∈ V, ∀ j ∈ V, g i = g j ↔ f i = f j) ∧
      (V.image g).card = (V.image f).card := by
  classical
  let T := V.image f
  obtain ⟨e⟩ : Nonempty (T ↪ Fin b) :=
    Function.Embedding.nonempty_of_card_le (by simpa [T] using hcard)
  let g : Fin r → Fin b := fun i =>
    if hi : i ∈ V then e ⟨f i, mem_image.mpr ⟨i, hi, rfl⟩⟩ else ⟨0, hb⟩
  have hg (i : Fin r) (hi : i ∈ V) :
      g i = e ⟨f i, mem_image.mpr ⟨i, hi, rfl⟩⟩ := by simp [g, hi]
  refine ⟨g, ?_, ?_⟩
  · intro i hi j hj
    rw [hg i hi, hg j hj, e.injective.eq_iff, Subtype.mk.injEq]
  · have himage : V.image g = (univ : Finset T).image e := by
      ext y
      constructor
      · rintro hy
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
        exact mem_image.mpr ⟨⟨f i, mem_image.mpr ⟨i, hi, rfl⟩⟩,
          mem_univ _, (hg i hi).symm⟩
      · intro hy
        obtain ⟨z, _, rfl⟩ := mem_image.mp hy
        obtain ⟨i, hi, hfi⟩ := mem_image.mp z.2
        refine mem_image.mpr ⟨i, hi, ?_⟩
        rw [hg i hi]
        congr 1
        exact Subtype.ext hfi
    rw [himage, card_image_of_injective _ e.injective]
    simp [T]

/--
@isnad1 id=eq.1h6v.s6.225ac24c6435 from=translated src=- shape=525b8b10 vocab=26bd7459
-/
theorem separationMask_eq_of_pattern {r : ℕ} {α β : Type*}
    [DecidableEq α] [DecidableEq β] (V : Finset (Fin r))
    (f : Fin r → α) (g : Fin r → β)
    (h : ∀ i ∈ V, ∀ j ∈ V, f i = f j ↔ g i = g j) :
    separationMask V f = separationMask V g := by
  ext e
  simp only [separationMask, mem_filter, mem_univ, true_and]
  exact and_congr_right (fun hi => and_congr_right (fun hj => not_congr (h _ hi _ hj)))

/-- Enumerate bounded-block partitions by at most r labels. Digits outside the
support do not matter; equal separation masks are deduplicated by Finset.image.-/
def localSeparationMasks {r : ℕ} (V : Finset (Fin r)) (b : ℕ) :
    Finset (SeparationMask r) :=
  ((univ : Finset (Fin r → Fin r)).filter
    (fun f => (V.image f).card ≤ b)).image (separationMask V)

/--
@isnad1 id=iff.2h4v.s6.b09e253b2d05 from=translated src=- shape=02552b3c vocab=ae76b806
-/
theorem local_masks_exact {r b : ℕ} (hr : 0 < r) (hb : 0 < b)
    (V : Finset (Fin r)) (H : SeparationMask r) :
    H ∈ localSeparationMasks V b ↔
      ∃ f : Fin r → Fin b, separationMask V f = H := by
  classical
  constructor
  · intro h
    obtain ⟨c, hc, rfl⟩ := mem_image.mp h
    obtain ⟨f, hf, _⟩ := finite_support_relabel V c hb (mem_filter.mp hc).2
    exact ⟨f, separationMask_eq_of_pattern V f c hf⟩
  · rintro ⟨f, rfl⟩
    have hc : (V.image f).card ≤ r :=
      (card_image_le).trans (by simpa using V.card_le_univ)
    obtain ⟨c, hpat, hcard⟩ := finite_support_relabel V f hr hc
    refine mem_image.mpr ⟨c, mem_filter.mpr ⟨mem_univ _, ?_⟩,
      separationMask_eq_of_pattern V c f hpat⟩
    rw [hcard]
    simpa using (V.image f).card_le_univ

/--
@isnad1 id=le.0h3v.s5.15470179b747 from=translated src=- shape=95794d4d vocab=f6422ec3
-/
theorem local_masks_card_bound {r : ℕ} (V : Finset (Fin r)) (b : ℕ) :
    (localSeparationMasks V b).card ≤ r ^ r := by
  calc
    _ ≤ ((univ : Finset (Fin r → Fin r)).filter
        (fun f => (V.image f).card ≤ b)).card := card_image_le
    _ ≤ (univ : Finset (Fin r → Fin r)).card := card_filter_le _ _
    _ = r ^ r := by simp

/-- One finite-state transition: combine previous separated pairs with those
separated in this coordinate.-/
def separationStep {r : ℕ} (R T : Finset (SeparationMask r)) :
    Finset (SeparationMask r) :=
  (R ×ˢ T).image (fun p => p.1 ∪ p.2)

def separationDP {r : ℕ} (choices : ℕ → Finset (SeparationMask r)) :
    ℕ → Finset (SeparationMask r)
  | 0 => {∅}
  | k + 1 => separationStep (separationDP choices k) (choices k)

/--
@isnad1 id=iff.0h4v.s7.e831a4c327d0 from=translated src=- shape=11dffee5 vocab=5b8e29fe
-/
theorem separation_step_mem {r : ℕ} (R T : Finset (SeparationMask r))
    (H : SeparationMask r) :
    H ∈ separationStep R T ↔ ∃ U ∈ R, ∃ V ∈ T, U ∪ V = H := by
  simp only [separationStep, mem_image, mem_product, Prod.exists]
  aesop

/--
@isnad1 id=eq.0h3v.s5.ffd588f0d5a6 from=translated src=- shape=f7b32bd7 vocab=2d88228e
-/
theorem prefix_biUnion_succ {α : Type*} [DecidableEq α]
    (f : ℕ → Finset α) (k : ℕ) :
    (range (k+1)).biUnion f = (range k).biUnion f ∪ f k := by
  rw [Finset.range_add_one, biUnion_insert, union_comm]

/-- Every state has a full sequence of choices witnesses, and every sequence
of choices witnesses appears. This is the DP invariant and reconstruction lemma.
@isnad1 id=iff.0h4v.s7.3fe83ddfc629 from=translated src=- shape=12a6ef8c vocab=a404758e
-/
theorem separation_dp_exact {r : ℕ} (choices : ℕ → Finset (SeparationMask r))
    (k : ℕ) (H : SeparationMask r) :
    H ∈ separationDP choices k ↔
      ∃ f : ℕ → SeparationMask r,
        (∀ t < k, f t ∈ choices t) ∧ H = (range k).biUnion f := by
  induction k generalizing H with
  | zero =>
    simp only [separationDP, mem_singleton, range_zero, biUnion_empty]
    exact ⟨fun h => ⟨fun _ => ∅, by simp, h⟩, fun ⟨_, _, h⟩ => h⟩
  | succ k ih =>
    rw [separationDP, separation_step_mem]
    constructor
    · rintro ⟨U, hU, V, hV, rfl⟩
      obtain ⟨f, hf, rfl⟩ := (ih U).mp hU
      let g : ℕ → SeparationMask r := fun t => if t = k then V else f t
      have hg : (range k).biUnion g = (range k).biUnion f := by
        apply biUnion_congr rfl
        intro t ht
        simp [g, (mem_range.mp ht).ne]
      refine ⟨g, ?_, ?_⟩
      · intro t ht
        by_cases he : t = k
        · subst t; simpa [g] using hV
        · simpa [g, he] using hf t (by omega)
      · rw [prefix_biUnion_succ, hg]
        simp [g]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨(range k).biUnion f, (ih _).mpr ⟨f, fun t ht =>
        hf t (by omega), rfl⟩, f k, hf k (by omega), ?_⟩
      exact (prefix_biUnion_succ f k).symm

/--
@isnad1 id=eq.0h1v.s6.908159ce70c9 from=translated src=- shape=cb8a2332 vocab=6783b5a8
-/
theorem separation_mask_universe_card (r : ℕ) :
    Fintype.card (SeparationMask r) = 2 ^ (r * (r-1) / 2) := by
  have hp := twice_pair_count r
  have hcard : Fintype.card (PairIndex r) = r * (r-1) / 2 := by omega
  simp [SeparationMask, Fintype.card_finset, hcard]

/--
@isnad1 id=le.0h3v.s6.d4dcf821ecf6 from=translated src=- shape=cf37b24a vocab=e7692e70
-/
theorem separation_dp_state_bound {r : ℕ}
    (choices : ℕ → Finset (SeparationMask r)) (k : ℕ) :
    (separationDP choices k).card ≤ 2 ^ (r * (r-1) / 2) := by
  simpa only [separation_mask_universe_card] using (separationDP choices k).card_le_univ

/--
@isnad1 id=le.0h4v.s6.a7dc44d88ec1 from=translated src=- shape=64e31f70 vocab=161b3c20
-/
theorem separation_step_candidate_bound {r : ℕ}
    (R : Finset (SeparationMask r)) (V : Finset (Fin r)) (b : ℕ) :
    (R ×ˢ localSeparationMasks V b).card ≤
      2 ^ (r * (r-1) / 2) * r ^ r := by
  rw [card_product]
  apply Nat.mul_le_mul
  · simpa only [separation_mask_universe_card] using R.card_le_univ
  · exact local_masks_card_bound V b

end Erdos278
