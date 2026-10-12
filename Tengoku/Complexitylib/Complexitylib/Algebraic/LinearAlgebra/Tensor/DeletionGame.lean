/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Internal

/-!
# The deletion game

The global, purely combinatorial step of a border-rank lower bound of about
`(1 + 2D/3) m` for tight tensors with `m = 2k + 1` slices `Fin (2 * k + 1)`; for
`D = (2p + 1) / (p + 1)` this is `(7/3 - 2 / (3 (p + 1))) m`, so `19/9 m` at `p = 2`. Border
substitution (`Algebraic.Tensor3.Tight.exists_list_add_borderRank_le`) gives an ordering of the
slices along which deleting the first `q` slices lowers the border rank by at least `q`. The
deletion game shows that for *every* ordering some stage `q` has `q` plus a lower bound `LB` on
the border rank of the surviving slices at least `(1 + 2D/3) m - D E - (8 L + R m / L + 2)`.
The local input is the paired-cluster hypothesis `DeletionGame.PairedClusterBound` on `LB`
(see `Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs`), which this file takes
as a hypothesis: whenever a positive and a negative block of length `L` each keep `R`
survivors, `LB` is at least `D (Φ_m(r, s) - E)` for offsets `r` and `-s` in the two blocks.

* **The width function.** `Φ_n(r, s) = Φ_n(s, r)` (`DeletionGame.phi_comm`),
  `Φ_n(r, s) ≥ 2n/3` (`DeletionGame.two_mul_le_three_mul_phi`), and `Φ_n` is `2`-Lipschitz in
  each argument (`DeletionGame.phi_le_add`).
* **Two-interval lemma** (`DeletionGame.filter_phi_le_subset`,
  `DeletionGame.two_mul_card_filter_phi_le`). For `n = 2k + 1` and `s ≥ 0`, the positions
  `r ∈ [1, k]` with `Φ_n(r, s) ≤ T` lie in two integer intervals and number at most
  `(3T - 2n + 3) / 2`.
* **The count at the stopping time** (`DeletionGame.le_sub_card_add_of_lost`). If one side
  keeps a good block while the other loses its last good block at the next deletion, the
  survivors number at most about `3T/2 - m + O(L + R m / L)`, where `D (T - E)` is the
  paired-cluster bound; with `T ≥ 2m/3` and `D ≥ 3/2` this gives the bound.
* **The deletion game** (`DeletionGame.PairedClusterBound.exists_stage`). Stop at the last
  stage at which both signs have a good block. The first blocks are full before any deletion,
  so this needs `1 ≤ R ≤ L ≤ k`.
* **Combined with border substitution** (`Tight.le_borderRank_of_pairedClusterBound`,
  `Tight.not_borderRankLE_of_pairedClusterBound`). A tight tensor with nonzero slices,
  satisfying the paired-cluster hypothesis for the border ranks of its slice restrictions,
  has border rank at least `(1 + 2D/3) m - D E - (8 L + R m / L + 2)`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset

namespace DeletionGame

/-! ### The width function -/

/-- `Φ_n` is symmetric in the two offsets.
@isnad1 id=eq.0h3v.s4.0cbd6451b0cb from=translated src=- shape=7eed5a8a vocab=37773d2e
-/
theorem phi_comm (n r s : ℤ) : phi n r s = phi n s r :=
  Internal.phi_comm n r s

/-- `Φ_n(r, s) ≥ 2n/3`, since `(n - r) + (n - s) + (r + s) = 2n`.
@isnad1 id=le.0h3v.s5.4051dd87b85c from=translated src=- shape=591182d0 vocab=b2a4c9f4
-/
theorem two_mul_le_three_mul_phi (n r s : ℤ) : 2 * n ≤ 3 * phi n r s :=
  Internal.two_mul_le_three_mul_phi n r s

/-- `Φ_n` is `2`-Lipschitz in each offset.
@isnad1 id=le.2h7v.s6.9e08e0f5253e from=translated src=- shape=27e74d96 vocab=118cd356
-/
theorem phi_le_add {n r s r' s' d e : ℤ} (hr : |r - r'| ≤ d) (hs : |s - s'| ≤ e) :
    phi n r s ≤ phi n r' s' + 2 * d + 2 * e :=
  Internal.phi_le_add hr hs

/-! ### The two-interval lemma -/

/-! ### The deletion game -/

/-- The paired-cluster hypothesis passes to any larger function.
@isnad1 id=pairedcl.2h7v.s6.8880bb68089c from=translated src=- shape=9d8d5873 vocab=74e6bc66
-/
theorem PairedClusterBound.mono {k L R : ℕ} {D E : ℝ} {LB LB' : Finset (Fin (2 * k + 1)) → ℕ}
    (h : PairedClusterBound k L R D E LB) (hle : ∀ S, LB S ≤ LB' S) :
    PairedClusterBound k L R D E LB' :=
  Internal.pairedClusterBound_mono h hle

/-- **The count at the stopping time.** Let `f` be injective with values in `[-k, k]`. Its
blocks `sideBlock f L i` form the winning side and the blocks `sideBlock (-f) L j` the losing
side. Suppose that after deleting at most one element of `S`, leaving `S'`, no losing block is
good, that the winning block `i₁` is good for `S`, and that every good winning block `i` for
`S` pairs with a fixed losing block `j₀` as in the paired-cluster hypothesis, with value `V`.
Then `(1 + 2D/3) n - D E - (8 L + R n / L + 2) ≤ (n - card S) + V` for `n = 2k + 1`.
@isnad1 id=le.9h12v.s9.12da7c3712bd from=translated src=- shape=33b2b01d vocab=cd60ebdd
-/
theorem le_sub_card_add_of_lost {α : Type*} [Fintype α] [DecidableEq α] {k L R : ℕ}
    {D E V : ℝ} {f : α → ℤ} (hf : Function.Injective f) (hfk : ∀ a, -(k : ℤ) ≤ f a ∧ f a ≤ k)
    (hR : 1 ≤ R) (hRL : R ≤ L) (hD : 3 / 2 ≤ D) {S S' : Finset α} (hSS' : (S \ S').card ≤ 1)
    (hlost : ∀ j, (S' ∩ sideBlock (fun a => -f a) L j).card < R) {i₁ j₀ : ℕ}
    (hi₁ : R ≤ (S ∩ sideBlock f L i₁).card)
    (hH : ∀ i, R ≤ (S ∩ sideBlock f L i).card → ∃ a ∈ sideBlock f L i,
      ∃ b ∈ sideBlock (fun a => -f a) L j₀,
        D * ((phi (2 * k + 1) (f a) (-f b) : ℝ) - E) ≤ V) :
    (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E - (8 * L + R * (2 * k + 1) / L + 2) ≤
      (2 * k + 1 : ℝ) - S.card + V :=
  Internal.le_sub_card_add_of_lost hf hfk hR hRL hD hSS' hlost hi₁ hH

/-- **The deletion game.** Assume the paired-cluster hypothesis for `LB` with `D ≥ 3/2`, and
`1 ≤ R ≤ L ≤ k`. Then for every ordering `l` of the `m = 2k + 1` slices (`l.Nodup` and
`l.toFinset = univ`), some stage `q ≤ m` satisfies
`(1 + 2D/3) m - D E - (8 L + R m / L + 2) ≤ q + LB S_q`, where `S_q` is the set of slices
left after deleting the first `q` elements of `l`.
@isnad1 id=ex.7h7v.s9.f2be8b812612 from=translated src=- shape=0c22290a vocab=2c6a685b
-/
theorem PairedClusterBound.exists_stage {k L R : ℕ} {D E : ℝ}
    {LB : Finset (Fin (2 * k + 1)) → ℕ} (hLB : PairedClusterBound k L R D E LB) (hR : 1 ≤ R)
    (hRL : R ≤ L) (hLk : L ≤ k) (hD : 3 / 2 ≤ D) {l : List (Fin (2 * k + 1))} (hl : l.Nodup)
    (hlu : l.toFinset = univ) :
    ∃ q ≤ 2 * k + 1, (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E -
      (8 * L + R * (2 * k + 1) / L + 2) ≤ q + LB (univ \ (l.take q).toFinset) :=
  Internal.exists_stage hLB hR hRL hLk hD hl hlu

end DeletionGame

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

end Algebraic.Tensor3
