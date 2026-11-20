/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.RepresentativeMap
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.Transport
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.MajorityAssembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Displaced-coordinate edit transport

Transport of a model along a representative map, and its edit cost.

* `FiniteRelModel.transportAlong M r := M.pullback r.rep` — the truth table of `M` read at the
  representatives (`RegularityLemmata/Relational/Transport.lean`'s pullback, frozen direction
  `(M.transportAlong r).Holds S x ↔ M.Holds S (r.rep ∘ x)`). Since `r.rep` is constant on the
  parts of the new partition `Q`, the transported model is indivisible for `Q`
  (`transportAlong_isIndivisibleFor`), and nullary symbols are copied exactly
  (`nullaryCompatible_transportAlong`).
* **Edit cost.** If `M` is indivisible for the old partition `P` (constant on old part
  products), then `M` and its transport agree on every tuple of `s^k` avoiding the displaced set
  `D` (`transportAlong_holds_iff_of_not_displaced`): the representatives of a non-displaced
  tuple lie in the same old parts. Hence the edit set is contained in the tuples meeting `D`
  (`editSet_transportAlong_subset`), and for arity `k = n + 1 ≥ 1`
  `editDistance ≤ (n+1) · |D| · |s|^n` (`editDistance_transportAlong_le`, counting the tuples
  meeting `D` by `card_filter_exists_apply_mem_le` of `RegularityLemmata/Finite/Tuple.lean`),
  normalized
  `≤ (n+1) · |D| / |s|` when `|s| > 0`. Repeated coordinates and repeated part labels need no
  hypothesis; the empty host has an empty box for `k ≥ 1` (edit `0`), and arity `0` is exact.
* **Composition with the majority assembly** (`exists_equitable_isIndivisibleFor`): from any
  model `M` and old partition `P`, one equipartition `Q` with a requested number `t` of parts and
  **one** model `N`, indivisible for `Q`, nullary-compatible with `M`, such that for every
  symbol of arity `n + 1` satisfying the decency hypotheses of `editDistance_majorityRound_le`,
  `edit(M, N) ≤ (n+1)·|s|^(n+1)·(2θ + γ/2 + λ/2) + (n+1)·((#P.parts − 1)·⌊|s|/t⌋)·|s|^n`. The
  partition `Q` and the model `N` are chosen before any symbol is; the displacement term is the
  `+ k·κ·N^k` of the coordinate-defect programme with `κ = (#P.parts − 1)·⌊|s|/t⌋/|s|` (the free
  old part `t₀` costs nothing).

`RegularityLemmata/Relational/Transport.lean` is pullback, restriction, relabeling; the quantitative estimate is
this file's.
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {P Q : Finpartition s}

/-- Transport of `M` along a representative map: the pullback along `r.rep`.-/
def FiniteRelModel.transportAlong (M : FiniteRelModel L V) (r : RepresentativeMap P Q) :
    FiniteRelModel L V :=
  M.pullback r.rep

namespace FiniteRelModel

variable (M : FiniteRelModel L V) (r : RepresentativeMap P Q)

/--
@isnad1 id=iff.0h10v.s6.336599ada503 from=translated src=- shape=8b775a08 vocab=03ed7713
-/
@[simp] theorem transportAlong_holds {n : ℕ} (S : L.Relations n) (x : Fin n → V) :
    (M.transportAlong r).Holds S x ↔ M.Holds S (r.rep ∘ x) :=
  Iff.rfl

/-- The transport is indivisible for the new partition: the representative map is constant
on its parts.
@isnad1 id=isindivi.0h7v.s5.8fb712338975 from=translated src=- shape=38b841f3 vocab=52bf3e77
-/
theorem transportAlong_isIndivisibleFor : (M.transportAlong r).IsIndivisibleFor Q := by
  intro n S x y hx hy hpart
  simp only [transportAlong_holds]
  have : r.rep ∘ x = r.rep ∘ y := funext fun i ↦ r.rep_const _ (hx i) _ (hy i) (hpart i)
  rw [this]

/-- Nullary symbols are copied exactly.
@isnad1 id=nullaryc.0h7v.s5.0cd8be243e60 from=translated src=- shape=d886b626 vocab=8e2f1802
-/
theorem nullaryCompatible_transportAlong : NullaryCompatible M (M.transportAlong r) := by
  intro S
  simp only [transportAlong_holds]
  rw [show r.rep ∘ Fin.elim0 = Fin.elim0 from funext fun i ↦ i.elim0]

/-- On a tuple of `s^n` avoiding `D`, the transport agrees with an old-indivisible `M`.
@isnad1 id=iff.3h10v.s7.20084dbebfe8 from=translated src=- shape=fd5bc4a4 vocab=0c144e79
-/
theorem transportAlong_holds_iff_of_not_displaced (hM : M.IsIndivisibleFor P) {n : ℕ}
    (S : L.Relations n) {x : Fin n → V} (hx : ∀ i, x i ∈ s) (hD : ∀ i, x i ∉ r.displaced) :
    (M.transportAlong r).Holds S x ↔ M.Holds S x := by
  simp only [transportAlong_holds]
  exact hM n S (r.rep ∘ x) x (fun i ↦ r.rep_mem _ (hx i)) hx
    fun i ↦ r.part_rep _ (hx i) (hD i)

/-- Differences can occur only on tuples meeting the displaced set.
@isnad1 id=le.1h9v.s7.3d0163cbcf6b from=translated src=- shape=7fb195fe vocab=fb917888
-/
theorem editSet_transportAlong_subset (hM : M.IsIndivisibleFor P) {n : ℕ} (S : L.Relations n) :
    editSet (M.Holds S) ((M.transportAlong r).Holds S) (fun _ : Fin n ↦ s)
      ⊆ (Fintype.piFinset fun _ : Fin n ↦ s).filter fun x ↦ ∃ i, x i ∈ r.displaced := by
  intro x hx
  rw [mem_editSet] at hx
  rw [Finset.mem_filter]
  refine ⟨hx.1, ?_⟩
  by_contra hnone
  push Not at hnone
  exact hx.2 (M.transportAlong_holds_iff_of_not_displaced r hM S
    (Fintype.mem_piFinset.mp hx.1) hnone).symm

end FiniteRelModel

namespace FiniteRelModel

variable (M : FiniteRelModel L V) (r : RepresentativeMap P Q)

/-- **Displaced-coordinate edit bound.** For an old-indivisible `M` and a symbol of arity
`n + 1`, the edit distance to the transport on `s^(n+1)` is at most `(n+1) · |D| · |s|^n`.
@isnad1 id=le.1h9v.s8.c311949261c2 from=translated src=- shape=ea8b1d48 vocab=9320a5ef
-/
theorem editDistance_transportAlong_le (hM : M.IsIndivisibleFor P) {n : ℕ}
    (S : L.Relations (n + 1)) :
    editDistance (M.Holds S) ((M.transportAlong r).Holds S) (fun _ : Fin (n + 1) ↦ s)
      ≤ (n + 1) * r.displaced.card * s.card ^ n :=
  (Finset.card_le_card (M.editSet_transportAlong_subset r hM S)).trans
    (card_filter_exists_apply_mem_le r.displaced_subset n)

/-- The normalized form: at most `(n+1) · |D| / |s|` when `|s| > 0`.
@isnad1 id=le.2h9v.s8.d23a52514bc7 from=translated src=- shape=f61cb6b0 vocab=fa222ecf
-/
theorem editDistance_transportAlong_div_le (hM : M.IsIndivisibleFor P) {n : ℕ}
    (S : L.Relations (n + 1)) (hs : 0 < s.card) :
    (editDistance (M.Holds S) ((M.transportAlong r).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
        / (s.card : ℝ) ^ (n + 1)
      ≤ (n + 1) * r.displaced.card / s.card := by
  have hs' : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hpow : (0 : ℝ) < (s.card : ℝ) ^ (n + 1) := pow_pos hs' _
  rw [div_le_div_iff₀ hpow hs']
  have h := M.editDistance_transportAlong_le r hM S
  calc (editDistance (M.Holds S) ((M.transportAlong r).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
        * s.card
      ≤ ((n + 1) * r.displaced.card * s.card ^ n : ℕ) * s.card := by
        gcongr
    _ = (n + 1) * r.displaced.card * (s.card : ℝ) ^ (n + 1) := by push_cast; ring

/-- Arity `0` is copied exactly.
@isnad1 id=eq.0h8v.s7.2cb510185d78 from=translated src=- shape=ddf7ed23 vocab=81c39f6f
-/
theorem editDistance_transportAlong_nullary (S : L.Relations 0) :
    editDistance (M.Holds S) ((M.transportAlong r).Holds S) (fun _ : Fin 0 ↦ s) = 0 :=
  editDistance_const_eq_zero_of_nullaryCompatible (M.nullaryCompatible_transportAlong r) s rfl S

end FiniteRelModel

/-! ### Composition with the majority assembly -/

/-- **One shared equitable partition and one rounded, transported model for all symbols.**
Given `M`, an old partition `P` with a designated part `t₀`, and a requested part count
`0 < t ≤ |s|`: an equipartition `Q` with exactly `t` parts and a model `N` indivisible for `Q`
and nullary-compatible with `M`, such that every symbol of arity `n + 1` meeting the decency
hypotheses of `editDistance_majorityRound_le` (at `P`) has
`edit(M, N) ≤ (n+1)·|s|^(n+1)·(2θ + γ/2 + λ/2) + (n+1)·((#P.parts − 1)·⌊|s|/t⌋)·|s|^n`; the
designated old part `t₀` is free.
@isnad1 id=ex.3h7v.s9.8bd793307112 from=translated src=- shape=1197cbbb vocab=83c4aa7a
-/
theorem exists_equitable_isIndivisibleFor (M : FiniteRelModel L V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel L V), Q.IsEquipartition ∧ Q.parts.card = t ∧
      N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      ∀ {n : ℕ} (S : L.Relations (n + 1)) {θ γ lam : ℝ}, 0 ≤ θ → 0 ≤ γ →
        ∀ (E : Finset (Finset V)), E ⊆ P.parts → (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card →
        (∀ (j : Fin (n + 1)), ∀ l ∈ P.parts, l ∉ E →
          (((Fintype.piFinset (fun _ : Fin n ↦ s)).filter fun rest ↦
              InclusiveMixed θ (densityOn l fun a ↦ M.Holds S (Fin.insertNth j a rest))).card : ℝ)
            ≤ γ * (Fintype.piFinset (fun _ : Fin n ↦ s)).card) →
        (editDistance (M.Holds S) (N.Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
          ≤ (n + 1) * (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2)
            + (n + 1) * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) * (s.card : ℝ) ^ n := by
  obtain ⟨Q, r, hQ, hcard, hD⟩ := exists_equitable_representativeMap P ht₀ ht hts
  refine ⟨Q, (M.majorityRound P).transportAlong r, hQ, hcard,
    (M.majorityRound P).transportAlong_isIndivisibleFor r, ?_, ?_⟩
  · intro S
    exact (nullaryCompatible_majorityRound M P S).trans
      ((M.majorityRound P).nullaryCompatible_transportAlong r S)
  · intro n S θ γ lam hθ hγ E hE hlam hdec
    have h1 := editDistance_majorityRound_le M P S hθ hγ E hE hlam hdec
    have h2 := (M.majorityRound P).editDistance_transportAlong_le r
      (majorityRound_isIndivisibleFor M P) S
    have htri := editDistance_triangle (R₁ := M.Holds S) (R₂ := (M.majorityRound P).Holds S)
      (R₃ := ((M.majorityRound P).transportAlong r).Holds S) (A := fun _ : Fin (n + 1) ↦ s)
    have h2' : (editDistance ((M.majorityRound P).Holds S)
        (((M.majorityRound P).transportAlong r).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
        ≤ (n + 1) * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) * (s.card : ℝ) ^ n := by
      calc (editDistance ((M.majorityRound P).Holds S)
            (((M.majorityRound P).transportAlong r).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
          ≤ ((n + 1) * r.displaced.card * s.card ^ n : ℕ) := by exact_mod_cast h2
        _ ≤ ((n + 1) * ((P.parts.card - 1) * (s.card / t)) * s.card ^ n : ℕ) := by
            exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hD)
        _ = (n + 1) * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) * (s.card : ℝ) ^ n := by
            push_cast; ring
    calc (editDistance (M.Holds S) (((M.majorityRound P).transportAlong r).Holds S)
          (fun _ : Fin (n + 1) ↦ s) : ℝ)
        ≤ (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
          + (editDistance ((M.majorityRound P).Holds S)
              (((M.majorityRound P).transportAlong r).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ) := by
          exact_mod_cast htri
      _ ≤ _ := add_le_add h1 h2'

/-! ### Tests -/

section Tests

-- **Empty host.** For arity `≥ 1` the box is empty, so the edit distance is `0` with no
-- hypothesis; arity `0` is exact by `editDistance_transportAlong_nullary`.

end Tests

end RegularityLemmata
