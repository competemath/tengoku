/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Hyperconcentrator.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Bound

/-!
# Proofs for hyperconcentrators

Let `G` be an `N`-hyperconcentrator and `h = ⌊N/2⌋`.

* **The cut lemma** (`exists_le_card_cut`). In a linear order of the vertices, take a lower
  set `L` with exactly `h` inputs, and let `c` of the first `h` outputs lie in `L`. The `h`
  inputs in `L` are joined to the first `h` outputs; at most `c` of the walks end in `L`, and
  each of the others leaves `L` along an edge of its own. The `N - h ≥ h` inputs outside `L` are
  joined to the first `N - h` outputs, among them the first `h`, and each of the `c` walks ending
  in `L` enters it along an edge of its own. So the cut of `L` has at least `h` edges.
* **Connectivity** (`reflTransGen_root`). Every input is joined to the first output, and every
  output is reached when all inputs are routed, so all terminals lie in one component.
* The split graph of that component is again a hyperconcentrator (`split_hyperconcentrator`),
  and the core inequalities of `Superconcentrator.Internal` give
  `h ≤ (A + η) (M - 2 N)⁺ + 3 log₂ (2 M) + C`, and, when the inputs are sources and every vertex
  has in-degree at most two, `h ≤ (A + η) ((V - N) - N)⁺ + 3 log₂ (4 (V - N)) + C`.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Hyperconcentrator.Internal

open Multigraph Relation Filter Superconcentrator.Internal

variable {V E : Type} {G : Multigraph V E} {N : ℕ} {input output : Fin N → V}

/-- Every superconcentrator is a hyperconcentrator.
@isnad1 id=hypercon.1h6v.s5.fdc0530bb247 from=translated src=- shape=c6b0aa70 vocab=c59396c6
-/
theorem hyperconcentrator_of_superconcentrator (h : G.Superconcentrator input output) :
    G.Hyperconcentrator input output where
  input_injective := h.input_injective
  output_injective := h.output_injective
  input_ne_output := h.input_ne_output
  exists_walks X := by
    have hcard : (Finset.univ.filter fun j : Fin N => (j : ℕ) < X.card).card = X.card := by
      have hX : X.card ≤ N := by simpa using Finset.card_le_univ X
      have : (Finset.univ.filter fun j : Fin N => (j : ℕ) < X.card) =
          (Finset.range X.card).attachFin fun j hj => by
            rw [Finset.mem_range] at hj
            omega := by
        ext j
        simp
      rw [this, Finset.card_attachFin, Finset.card_range]
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X _ hcard.symm
    exact ⟨target, walk, fun i hi => ⟨(Finset.mem_filter.1 (hwalk i hi).1).2, (hwalk i hi).2⟩,
      hdisj⟩

/-! ### The cut lemma -/

/-- The first `k` labels number at most `k`.
@isnad1 id=le.0h2v.s5.2719f9155cbe from=translated src=- shape=926d19b2 vocab=a5c30053
-/
theorem card_filter_lt_le (k : ℕ) : (Finset.univ.filter fun j : Fin N => (j : ℕ) < k).card ≤ k :=
  (Finset.card_le_card_of_injOn (t := Finset.range k) (fun j : Fin N => (j : ℕ)) (fun j hj => by
    simpa using (Finset.mem_filter.1 hj).2) Fin.val_injective.injOn).trans (by simp)

/-- **The cut lemma.** Every linear order of the vertices of an `N`-hyperconcentrator has a
lower set whose cut has at least `⌊N/2⌋` edges.
@isnad1 id=ex.1h6v.s6.9d6486bd88a4 from=translated src=- shape=85db22fd vocab=1a9d326a
-/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V]
    (h : G.Hyperconcentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ N / 2 ≤ (G.cut L).card := by
  set k := N / 2 with hk
  obtain ⟨L, hL, hcard⟩ := exists_isLowerSet_card_filter (Finset.univ.image input) (k := k)
    (by
      rw [Finset.card_image_of_injective _ h.input_injective, Finset.card_univ,
        Fintype.card_fin]
      omega)
  refine ⟨L, hL, ?_⟩
  set X := Finset.univ.filter fun i => input i ∈ L with hXdef
  have hX : X.card = k := by
    rw [← hcard, Finset.filter_image, Finset.card_image_of_injective _ h.input_injective]
  -- the inputs in `L` are joined to the first `k` outputs
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X
  have hfwd := card_le_card_outCut_add_card_filter (L : Set V)
    (Y := Finset.univ.filter fun j : Fin N => (j : ℕ) < k) (fun i hi => (hwalk i hi).2) hdisj
    (fun i hi => (Finset.mem_filter.1 hi).2)
    fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hX ▸ (hwalk i hi).1⟩
  -- the inputs outside `L` are joined to the first `N - k` outputs
  obtain ⟨target', walk', hwalk', hdisj'⟩ := h.exists_walks Xᶜ
  have hXc : Xᶜ.card = N - k := by rw [Finset.card_compl, Fintype.card_fin, hX]
  have hbwd := card_filter_le_card_outCut_compl (L : Set V)
    (Y := Finset.univ.filter fun j : Fin N => (j : ℕ) < Xᶜ.card) (fun i hi => (hwalk' i hi).2)
    hdisj' (fun i hi => by simpa [X] using hi)
    (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (hwalk' i hi).1⟩)
    (card_filter_lt_le _)
  calc k = X.card := hX.symm
    _ ≤ _ := hfwd
    _ ≤ (outCut G L).card + (outCut G (L : Set V)ᶜ).card := by
        refine Nat.add_le_add_left (le_trans ?_ hbwd) _
        refine Finset.card_le_card fun j hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨by omega, hj.2⟩
    _ ≤ (G.cut L).card := card_outCut_add_card_outCut_compl_le L

/-! ### The terminals lie in one component -/

/-- Every input is joined to the first output by a directed walk.
@isnad1 id=ex.2h7v.s6.3ef3932dff03 from=translated src=- shape=a62d6bb7 vocab=181f9dea
-/
theorem exists_isDirWalk_first (h : G.Hyperconcentrator input output) (hN : 0 < N)
    (i : Fin N) : ∃ p, G.IsDirWalk p (input i) (output ⟨0, hN⟩) := by
  obtain ⟨target, walk, hwalk, -⟩ := h.exists_walks {i}
  obtain ⟨hlt, hw⟩ := hwalk i (Finset.mem_singleton_self i)
  rw [Finset.card_singleton] at hlt
  have : target i = ⟨0, hN⟩ := Fin.ext (by simp only; omega)
  exact ⟨walk i, this ▸ hw⟩

/-- Every output is reached from some input by a directed walk.
@isnad1 id=ex.1h7v.s5.5a3c132827ef from=translated src=- shape=4fdc51c1 vocab=f07a2105
-/
theorem exists_isDirWalk_output (h : G.Hyperconcentrator input output) (j : Fin N) :
    ∃ i p, G.IsDirWalk p (input i) (output j) := by
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks Finset.univ
  obtain ⟨i, hi, rfl⟩ := exists_target_eq_of_walks (fun i hi => (hwalk i hi).2) hdisj
    (Y := Finset.univ) (fun _ _ => Finset.mem_univ _) le_rfl (Finset.mem_univ j)
  exact ⟨i, walk i, (hwalk i hi).2⟩

/-- **All terminals lie in one component.** Every input and every output of an
`N`-hyperconcentrator with `N > 0` is joined to the first input by an undirected walk.
@isnad1 id=and.2h6v.s6.c8886324ca0d from=translated src=- shape=c4016e0e vocab=52e519ce
-/
theorem reflTransGen_root (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    (∀ i, ReflTransGen G.Adj (input i) (input ⟨0, hN⟩)) ∧
      ∀ j, ReflTransGen G.Adj (output j) (input ⟨0, hN⟩) := by
  have hin : ∀ i, ReflTransGen G.Adj (input i) (input ⟨0, hN⟩) := fun i => by
    obtain ⟨p, hp⟩ := exists_isDirWalk_first h hN i
    obtain ⟨q, hq⟩ := exists_isDirWalk_first h hN ⟨0, hN⟩
    exact (reflTransGen_of_isDirWalk hp).trans
      (reflTransGen_adj_symm (reflTransGen_of_isDirWalk hq))
  refine ⟨hin, fun j => ?_⟩
  obtain ⟨i, p, hp⟩ := exists_isDirWalk_output h j
  exact (reflTransGen_adj_symm (reflTransGen_of_isDirWalk hp)).trans (hin i)

/-! ### The split graph -/

variable [Fintype E]

/-- Every input has a kept edge leaving it.
@isnad1 id=lt.2h7v.s6.29b6ae7a493d from=translated src=- shape=9c754fe4 vocab=ac9f0880
-/
theorem slots_input_pos (h : G.Hyperconcentrator input output) (hN : 0 < N) (i : Fin N) :
    0 < slots G (compEdges G (input ⟨0, hN⟩)) (input i) := by
  obtain ⟨p, hp⟩ := exists_isDirWalk_first h hN i
  exact slots_pos_of_isDirWalk_left hp (h.input_ne_output _ _) ((reflTransGen_root h hN).1 i)

/-- Every output has a kept edge entering it.
@isnad1 id=lt.2h7v.s6.9cda101369aa from=translated src=- shape=db09b0c0 vocab=ac9f0880
-/
theorem slots_output_pos (h : G.Hyperconcentrator input output) (hN : 0 < N) (j : Fin N) :
    0 < slots G (compEdges G (input ⟨0, hN⟩)) (output j) := by
  obtain ⟨i, p, hp⟩ := exists_isDirWalk_output h j
  exact slots_pos_of_isDirWalk_right hp (h.input_ne_output _ _) ((reflTransGen_root h hN).1 i)

/-- **The split graph of a hyperconcentrator.** If all inputs lie in the component of `r`,
every input has a slot, and every output has a slot, then the split graph of the component is
a hyperconcentrator with inputs at first slots and outputs at last slots.
@isnad1 id=hypercon.4h7v.s7.5bd762f12646 from=translated src=- shape=154eef0f vocab=293fc54a
-/
theorem split_hyperconcentrator (h : G.Hyperconcentrator input output) {r : V}
    (hr : ∀ i, ReflTransGen G.Adj (input i) r)
    (hin : ∀ i, 0 < slots G (compEdges G r) (input i))
    (hout : ∀ j, 0 < slots G (compEdges G r) (output j)) :
    (split G (compEdges G r)).Hyperconcentrator (fun i => ⟨input i, ⟨0, hin i⟩⟩)
      (fun j => ⟨output j, ⟨slots G (compEdges G r) (output j) - 1,
        Nat.sub_lt (hout j) one_pos⟩⟩) where
  input_injective _ _ hij := h.input_injective (sigma_fin_eq_iff.1 hij).1
  output_injective _ _ hij := h.output_injective (sigma_fin_eq_iff.1 hij).1
  input_ne_output i j hij := h.input_ne_output i j (sigma_fin_eq_iff.1 hij).1
  exists_walks X := by
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X
    obtain ⟨walk', hwalk', hdisj'⟩ := exists_lift_walks hr hin hout (X := X) (target := target)
      (fun i hi => (hwalk i hi).2) hdisj
    exact ⟨target, walk', fun i hi => ⟨(hwalk i hi).1, hwalk' i hi⟩, hdisj'⟩

variable [Fintype V]

omit [Fintype E] [Fintype V] in
/-- The `2 N` terminals are distinct vertices.
@isnad1 id=eq.1h6v.s6.61c7a7879f8e from=translated src=- shape=1db62502 vocab=09855782
-/
theorem card_terminals (h : G.Hyperconcentrator input output) :
    (Finset.univ.image input ∪ Finset.univ.image output).card = 2 * N := by
  have hdisj : Disjoint (Finset.univ.image input) (Finset.univ.image output) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact h.input_ne_output i j hj.symm
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ h.input_injective,
    Finset.card_image_of_injective _ h.output_injective, Finset.card_univ, Fintype.card_fin]
  ring

omit [Fintype E] in
/-- A hyperconcentrator has at least `2 N` vertices.
@isnad1 id=le.1h6v.s5.34d654b76f66 from=translated src=- shape=5ac28724 vocab=4fbaf5cd
-/
theorem two_mul_le_card_vertices (h : G.Hyperconcentrator input output) :
    2 * N ≤ Fintype.card V := by
  rw [← card_terminals h]
  exact Finset.card_le_univ _

/-- The `2 N` terminals have a slot.
@isnad1 id=le.2h6v.s7.04b9ce20c45a from=translated src=- shape=7328c709 vocab=0a9b08d6
-/
theorem two_mul_le_card_slotted (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    2 * N ≤ (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card := by
  rw [← card_terminals h]
  refine Finset.card_le_card fun w hw => ?_
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hw with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact (slots_input_pos h hN i).ne'
  · exact (slots_output_pos h hN j).ne'

/-- **The edge baseline.** An `N`-hyperconcentrator has at least `2 N - 1` edges.
@isnad1 id=le.2h6v.s6.cef8422a7a40 from=translated src=- shape=9a1b04b0 vocab=4471105a
-/
theorem two_mul_le_card_add_one (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    2 * N ≤ Fintype.card E + 1 :=
  le_card_add_one_of_le_slotted (slots_input_pos h hN _) (two_mul_le_card_slotted h hN)

/-! ### Asymptotics -/

omit [Fintype E] [Fintype V] in
/-- `⌊N/2⌋/A` is at least `N/(2A)` minus `ε N/2` once `N ≥ 1/(A ε)`.
@isnad1 id=le.3h3v.s7.337a144ca391 from=translated src=- shape=50b5a622 vocab=64bfd4fd
-/
theorem half_div_ge {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) {n : ℕ}
    (hn : ⌈1 / (A * ε)⌉₊ ≤ n) :
    1 / (2 * A) * n - ε / 2 * n ≤ ((n / 2 : ℕ) : ℝ) / A := by
  have hhalf : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hn' : 1 / (A * ε) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn'' : 1 ≤ A * ε * n := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hn'
  have hdiv : ((n : ℝ) - 1) / 2 / A ≤ ((n / 2 : ℕ) : ℝ) / A :=
    div_le_div_of_nonneg_right hhalf hA.le
  have e : ((n : ℝ) - 1) / 2 / A = 1 / (2 * A) * n - 1 / (2 * A) := by
    field_simp
  have h₁ : 1 / (2 * A) ≤ ε / 2 * n := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Algebraic.Cutwidth.Hyperconcentrator.Internal
