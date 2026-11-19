import Tengoku.Erdos278.Erdos278.RadixModel
import Tengoku.Erdos278.Erdos278.FiniteDP
import Tengoku.Erdos278.Erdos278.Density

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

abbrev RadixCoordinate {r : ℕ} {β : Type*} [Fintype β]
    (e : Fin r → β → ℕ) := (j : β) × Fin (univ.sup (fun i => e i j))

def radixSupport {r : ℕ} {β : Type*} [Fintype β]
    (e : Fin r → β → ℕ) (c : RadixCoordinate e) : Finset (Fin r) :=
  univ.filter (fun i => c.2.val < e i c.1)

noncomputable def radixDP {r : ℕ} {β : Type*} [Fintype β]
    (b : β → ℕ) (e : Fin r → β → ℕ) : Finset (SeparationMask r) :=
  finiteSeparationDP (fun c : RadixCoordinate e =>
    localSeparationMasks (radixSupport e c) (b c.1))

def radixSeparation {r : ℕ} {β : Type*} [Fintype β]
    (b : β → ℕ) (e : Fin r → β → ℕ)
    (u : ∀ j, ℕ → Fin r → Fin (b j)) : SeparationMask r :=
  univ.biUnion (fun c : RadixCoordinate e =>
    separationMask (radixSupport e c) (u c.1 c.2.val))

theorem radix_dp_digits {r : ℕ} {β : Type*} [Fintype β]
    (hr : 0 < r) (b : β → ℕ) (e : Fin r → β → ℕ)
    (hb : ∀ j, 0 < b j) (H : SeparationMask r) :
    H ∈ radixDP b e ↔ ∃ u : ∀ j, ℕ → Fin r → Fin (b j),
      H = radixSeparation b e u := by
  classical
  rw [radixDP, coordinate_dp_exact hr (radixSupport e)
    (fun c : RadixCoordinate e => b c.1) (fun c => hb c.1)]
  constructor
  · rintro ⟨v, rfl⟩
    let u : ∀ j, ℕ → Fin r → Fin (b j) := fun j t i =>
      if ht : t < univ.sup (fun i => e i j) then v ⟨j, ⟨t, ht⟩⟩ i else ⟨0, hb j⟩
    refine ⟨u, ?_⟩
    apply biUnion_congr rfl
    intro c _
    congr 1
    funext i
    simp only [u, dite_eq_left c.2.isLt]
  · rintro ⟨u, rfl⟩
    exact ⟨fun c => u c.1 c.2.val, rfl⟩

def incompatibilityMask {r : ℕ} (n : Fin r → ℕ) (a : Fin r → ℤ) :
    SeparationMask r := univ.filter (fun p => ¬ Compatible n a p.1.1 p.1.2)

theorem radix_separation_eq_mask {r : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (b : β → ℕ) (e : Fin r → β → ℕ) (hb : ∀ j, 0 < b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k)))
    (u : ∀ j, ℕ → Fin r → Fin (b j)) (a : Fin r → ℤ)
    (ha : ∀ i j, a i ≡ (radixPrefix (b j) (fun t => u j t i) (e i j) : ℤ)
      [ZMOD (b j)^(e i j)]) :
    radixSeparation b e u = incompatibilityMask (fun i => radixModulus b (e i)) a := by
  classical
  ext p
  simp only [radixSeparation, mem_biUnion, mem_univ, true_and,
    separationMask, radixSupport, mem_filter, incompatibilityMask]
  rw [radix_compatible_iff b e hb hc u a ha]
  push Not
  constructor
  · rintro ⟨c, hi, hh, hne⟩
    exact ⟨c.1, c.2.val, hi, hh, hne⟩
  · rintro ⟨j, t, hi, hh, hne⟩
    have ht : t < univ.sup (fun i => e i j) :=
      lt_of_lt_of_le hi (Finset.le_sup (f := fun i => e i j) (mem_univ p.1.1))
    exact ⟨⟨j, ⟨t, ht⟩⟩, hi, hh, hne⟩

/-- End-to-end realizable-state theorem for the finite coprime radix representation.
Both directions construct their witnesses; realizability is not a hypothesis.-/
theorem radix_dp_realizable_exact {r : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (hr : 0 < r) (b : β → ℕ) (e : Fin r → β → ℕ) (hb : ∀ j, 0 < b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k))) (H : SeparationMask r) :
    H ∈ radixDP b e ↔
      ∃ a : Fin r → ℤ, H = incompatibilityMask (fun i => radixModulus b (e i)) a := by
  rw [radix_dp_digits hr b e hb]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, ha⟩ := radix_digits_reconstruct b e hb hc u
    exact ⟨a, radix_separation_eq_mask b e hb hc u a ha⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨u, ha⟩ := radix_residues_encode b e hb a
    exact ⟨u, (radix_separation_eq_mask b e hb hc u a ha).symm⟩

end Erdos278
