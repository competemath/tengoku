/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Internal

/-!
# Border substitution for tight tensors

Let `T ∈ A ⊗ B ⊗ C` with `A = ℂ^α`. Border substitution lowers the border rank by deleting
`A`-slices: if `T` has border rank at most `r + 1`, then projecting `A` along a suitable line
gives border rank at most `r`. For a tight tensor the line can be taken to be a coordinate axis,
so that the projection zeroes one slice. Iterating gives the coordinate-subspace form of
Landsberg and Michałek, *Towards finding hay in a haystack* (Theory of Computing 2025),
Proposition 2.3, by a one-parameter-subgroup limit instead of the Borel fixed-point theorem. Here
tightness (`Tensor3.Tight`) asks only the weights on `A` to be injective, and nonzero slices
replace `A`-conciseness; their restrictions `T(q)` to coordinate subspaces of `A^*` are the
slice restrictions `Tensor3.restrictSlices` (see
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs`).

* **Only the kernel matters** (`Tensor3.BorderRankLE.map_of_ker`). If `(P ⊗ Y ⊗ Z) T` has border
  rank at most `ρ` and `ker P ⊆ ker P'`, then so does `(P' ⊗ Y ⊗ Z) T`, since `P' = G P`.
* **One step** (`Tensor3.BorderRankLE.exists_map_orthProj`). If `T` has border rank at most
  `r + 1` (and `α` is nonempty), some `u ≠ 0` has `(orthProj u ⊗ 1 ⊗ 1) T` of border rank at
  most `r`, where `orthProj u` is the orthogonal projection onto `u^⊥`. No conciseness is
  assumed.
* **Torus limit** (`Tensor3.Tight.exists_borderRankLE_restrictSlices_erase`). If `T` is tight
  and `(orthProj u ⊗ 1 ⊗ 1) T` has border rank at most `ρ` with `u ≠ 0`, then for some `i` in
  the support of `u` (the proof uses the one minimizing the weight `τA i`), `T` with slice `i`
  zeroed has border rank at most `ρ`.
* **One deletion** (`Tensor3.Tight.exists_mem_borderRankLE_restrictSlices_erase`). If `T` is
  tight, `S` is nonempty, and `T` restricted to the slices in `S` has border rank at most
  `r + 1`, then deleting some `i ∈ S` leaves border rank at most `r`.
* **Deletion order** (`Tensor3.Tight.exists_list_borderRankLE_restrictSlices_sdiff`). For some
  ordering `l` of `S₀`, deleting the first `q` elements of `l` leaves border rank at most
  `r - q` (truncated subtraction), for every `q`. If every slice in `S₀` is nonzero, then `card S₀ ≤ r`
  (`Tensor3.Tight.card_le_of_borderRankLE_restrictSlices`), so for a tight tensor all of whose
  `A`-slices are nonzero, `card α ≤ borderRank T` (`Tensor3.Tight.card_le_borderRank`). In
  terms of `borderRank`, `q + borderRank T(q) ≤ borderRank T(0)` along the ordering
  (`Tensor3.Tight.exists_list_add_borderRank_le`), which is Proposition 2.3 for filtrations by
  coordinate subspaces.
* **Lower-bound form** (`Tensor3.Tight.not_borderRankLE_restrictSlices_of_forall_list`). If `LB`
  is a lower bound for the border rank of every restriction to a subset of `S₀`, and every
  ordering of `S₀` has a stage `q` where `q + LB` of the surviving slices exceeds `r`, then the
  restriction to `S₀` does not have border rank at most `r`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset Matrix

variable {α β γ α' β' γ' α'' : Type*}

section Restrict

variable [DecidableEq α]

/--
@isnad1 id=eq.0h8v.s6.ac87a63ec38b from=translated src=- shape=dc2640de vocab=78c92855
-/
theorem restrictSlices_apply (T : Tensor3 α β γ) (S : Finset α) (i : α) (j : β) (k : γ) :
    T.restrictSlices S i j k = if i ∈ S then T i j k else 0 :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.467122a6bd4f from=translated src=- shape=405b1e33 vocab=e787be8e
-/
theorem restrictSlices_restrictSlices (T : Tensor3 α β γ) (S S' : Finset α) :
    (T.restrictSlices S).restrictSlices S' = T.restrictSlices (S' ∩ S) :=
  Internal.restrictSlices_restrictSlices T S S'

/--
@isnad1 id=eq.0h4v.s5.cab893b6dc07 from=translated src=- shape=34bceb52 vocab=ac31215a
-/
theorem restrictSlices_univ [Fintype α] (T : Tensor3 α β γ) : T.restrictSlices univ = T :=
  Internal.restrictSlices_univ T

/--
@isnad1 id=eq.0h4v.s6.30c11489ee9a from=translated src=- shape=4254a296 vocab=d63f3467
-/
theorem restrictSlices_empty (T : Tensor3 α β γ) : T.restrictSlices ∅ = 0 :=
  Internal.restrictSlices_empty T

/-- Restricting to the slices in `S` is the linear map `D ⊗ 1 ⊗ 1` for the diagonal `0/1`
matrix `D` with `D i i = 1` exactly when `i ∈ S`.
@isnad1 id=eq.0h5v.s6.b2cad20278ca from=translated src=- shape=5f94226d vocab=fa5a80ec
-/
theorem restrictSlices_eq_map [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] (T : Tensor3 α β γ) (S : Finset α) :
    T.restrictSlices S =
      map (diagonal fun i => if i ∈ S then 1 else 0) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T :=
  Internal.restrictSlices_eq_map T S

/-- Zeroing slices does not increase border rank.
@isnad1 id=borderra.1h6v.s5.b9fcb7fcc3f1 from=translated src=- shape=e5790a4d vocab=bc9b7327
-/
theorem BorderRankLE.restrictSlices [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] {T : Tensor3 α β γ} {ρ : ℕ} (h : T.BorderRankLE ρ) (S : Finset α) :
    (T.restrictSlices S).BorderRankLE ρ :=
  Internal.borderRankLE_restrictSlices h S

/-- Zeroing further slices does not increase border rank.
@isnad1 id=borderra.2h7v.s6.e8dbf25fbc8d from=translated src=- shape=7098d5f6 vocab=7b8b2835
-/
theorem BorderRankLE.restrictSlices_of_subset [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {T : Tensor3 α β γ} {S S' : Finset α} {ρ : ℕ}
    (h : (T.restrictSlices S).BorderRankLE ρ) (hS : S' ⊆ S) :
    (T.restrictSlices S').BorderRankLE ρ :=
  Internal.borderRankLE_restrictSlices_of_subset h hS

/-- Zeroing slices keeps a tensor tight, with the same weights.
@isnad1 id=tight.1h5v.s5.5ff40d88846f from=translated src=- shape=3f298822 vocab=d0094061
-/
theorem Tight.restrictSlices {T : Tensor3 α β γ} (hT : T.Tight) (S : Finset α) :
    (T.restrictSlices S).Tight :=
  Internal.tight_restrictSlices hT S

end Restrict

section OrthProj

variable [Fintype α] [DecidableEq α]

/--
@isnad1 id=eq.0h3v.s7.14026b15dfe8 from=translated src=- shape=02755ba4 vocab=3a3e6476
-/
theorem orthProj_mulVec (u v : α → ℂ) :
    orthProj u *ᵥ v = v - ((star u ⬝ᵥ u)⁻¹ * (star u ⬝ᵥ v)) • u :=
  Internal.orthProj_mulVec u v

/--
@isnad1 id=eq.0h2v.s5.0bef63d291ab from=translated src=- shape=2bfd947a vocab=b2e23652
-/
theorem orthProj_mulVec_self (u : α → ℂ) : orthProj u *ᵥ u = 0 :=
  Internal.orthProj_mulVec_self u

/-- The kernel of `orthProj u` is the line through `u`.
@isnad1 id=iff.0h3v.s6.29d14f764137 from=translated src=- shape=554ee29b vocab=e9ea27af
-/
theorem orthProj_mulVec_eq_zero_iff {u v : α → ℂ} :
    orthProj u *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • u :=
  Internal.orthProj_mulVec_eq_zero_iff

/-- `orthProj` is continuous away from `0`.
@isnad1 id=continuo.1h2v.s6.178d0d921a8c from=translated src=- shape=69a121d8 vocab=570128df
-/
theorem continuousAt_orthProj {u : α → ℂ} (hu : u ≠ 0) :
    ContinuousAt (orthProj : (α → ℂ) → Matrix α α ℂ) u :=
  Internal.continuousAt_orthProj hu

end OrthProj

section Substitution

variable [Fintype α] [Fintype β] [Fintype γ]

/-- **Only the kernel matters.** If `(P ⊗ Y ⊗ Z) T` has border rank at most `ρ` and every vector
killed by `P` is killed by `P'`, then `(P' ⊗ Y ⊗ Z) T` has border rank at most `ρ`.
@isnad1 id=borderra.2h13v.s7.b8e06a1e5645 from=translated src=- shape=a5551048 vocab=29e2d955
-/
theorem BorderRankLE.map_of_ker [Fintype α'] [Fintype β'] [Fintype γ'] {P : Matrix α' α ℂ}
    {P' : Matrix α'' α ℂ} {Y : Matrix β' β ℂ} {Z : Matrix γ' γ ℂ} {T : Tensor3 α β γ} {ρ : ℕ}
    (h : (Tensor3.map P Y Z T).BorderRankLE ρ) (hker : ∀ v, P *ᵥ v = 0 → P' *ᵥ v = 0) :
    (Tensor3.map P' Y Z T).BorderRankLE ρ :=
  Internal.borderRankLE_map_of_ker Y Z h hker

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Border substitution, one step.** If `T` has border rank at most `r + 1`, then for some
`u ≠ 0` the projection `(orthProj u ⊗ 1 ⊗ 1) T` of the first factor onto `u^⊥` has border rank
at most `r`.
@isnad1 id=ex.1h5v.s7.ad3207b368d8 from=translated src=- shape=f8739c14 vocab=38ed8399
-/
theorem BorderRankLE.exists_map_orthProj [Nonempty α] {T : Tensor3 α β γ} {r : ℕ}
    (h : T.BorderRankLE (r + 1)) :
    ∃ u : α → ℂ, u ≠ 0 ∧
      (Tensor3.map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE r :=
  Internal.exists_borderRankLE_map_orthProj h

/-- **Border substitution, one step**, for a nonzero tensor.
@isnad1 id=ex.2h5v.s7.6c3fcf5f6f53 from=translated src=- shape=e5c9745a vocab=8f32b672
-/
theorem BorderRankLE.exists_map_orthProj_of_ne_zero {T : Tensor3 α β γ} (hT : T ≠ 0) {r : ℕ}
    (h : T.BorderRankLE (r + 1)) :
    ∃ u : α → ℂ, u ≠ 0 ∧
      (Tensor3.map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE r := by
  obtain ⟨i, -⟩ := Function.ne_iff.mp hT
  have : Nonempty α := ⟨i⟩
  exact h.exists_map_orthProj

end Substitution

end Algebraic.Tensor3
