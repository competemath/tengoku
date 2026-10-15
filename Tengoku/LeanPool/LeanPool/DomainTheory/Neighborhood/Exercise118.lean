/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Basic
public import Tengoku

/-!
# Exercise 1.18 (Scott 1981, PRG-19, §1) — consistent subsets and filter
intersections

Scott calls a subset `C ⊆ 𝒟` *consistent* iff every finite subset of `C` is
consistent in `𝒟`.
This file formalizes (representing finite subsets as finite sequences drawn from
`C`):

* `FinitelyConsistent C` — every finite sequence from `C` is `Consistent`;
* a concrete `C = {A, B, Cc}` (over `Δ = {0,1,2}`, all-non-empty-subsets system)
with three
  members, pairwise consistent (`family_pairwise_nonempty`) but **not** consistent
  (`not_finitelyConsistent`) — `A ∩ B ∩ Cc = ∅`;
* `sInf F hF` — the intersection of a non-empty family `F` of filters is a filter,
the greatest
  lower bound (`sInf_le`, `le_sInf`);
* `leastFilter C hCsub hC` — the **least** filter containing a consistent `C`,
with
  `subset_leastFilter` (`C ⊆` it) and `leastFilter_le` (it is least). The
  intersection law uses
  the *append* of two finite sequences (`interUpTo_appendSeq`).

Constructive (`[propext, Quot.sound]`) except the counterexample's finite
case-analysis.
-/

@[expose] public section

namespace Domain.Neighborhood

/-- Concatenation of two finite sequences: the first `n1` entries are `X1 0, …, X1
(n1-1)`,
then `X2 0, X2 1, …`. -/
def appendSeq {α : Type*} (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) : ℕ → Set α :=
  fun i => if i < n1 then X1 i else X2 (i - n1)

/-- Each entry of `appendSeq X1 n1 X2` below `n1 + n2` is drawn from `C`.
@isnad1 id=mem.3h7v.s6.4ed93b993aca from=translated src=- shape=ca71a3eb vocab=577a7c07
-/
theorem appendSeq_mem {α : Type*} {C : Set (Set α)} {X1 : ℕ → Set α} {n1 : ℕ}
    {X2 : ℕ → Set α} {n2 : ℕ} (h1 : ∀ i, i < n1 → X1 i ∈ C) (h2 : ∀ i, i < n2 → X2 i ∈ C) :
    ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := by
  intro i hi
  simp only [appendSeq]
  by_cases h : i < n1
  · rw [ite_eq_left h]; exact h1 i h
  · rw [ite_eq_right h]; exact h2 (i - n1) (by omega)

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is contained in the master neighbourhood (its first
factor).
@isnad1 id=le.0h4v.s4.762899973ada from=translated src=- shape=cecc29a6 vocab=ec6f92ad
-/
theorem interUpTo_subset_master (X : ℕ → Set α) : ∀ n, V.interUpTo X n ⊆ V.master := by
  intro n
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact Set.inter_subset_left.trans ih

/-- For a prefix length `k ≤ n1`, `interUpTo` of the appended sequence agrees with
`interUpTo`
of the first sequence.
@isnad1 id=eq.1h6v.s5.ddf61ac1ccef from=translated src=- shape=3c8241cf vocab=02a37264
-/
theorem interUpTo_appendSeq_left (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {k : ℕ}, k ≤ n1 → V.interUpTo (appendSeq X1 n1 X2) k = V.interUpTo X1 k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [interUpTo_succ, interUpTo_succ, ih (Nat.le_of_succ_le hk)]
    have happ : appendSeq X1 n1 X2 k = X1 k := by
      simp only [appendSeq, ite_eq_left (Nat.lt_of_succ_le hk)]
    rw [happ]

/-- The key identity: `⋂_{i<n1+n2} (X1 ++ X2)ᵢ = (⋂_{i<n1} X1ᵢ) ∩ (⋂_{i<n2} X2ᵢ)`.
@isnad1 id=eq.0h6v.s5.d94103346bff from=translated src=- shape=0544c095 vocab=a8ecbb0a
-/
theorem interUpTo_appendSeq (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {j : ℕ}, V.interUpTo (appendSeq X1 n1 X2) (n1 + j)
      = V.interUpTo X1 n1 ∩ V.interUpTo X2 j := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, V.interUpTo_appendSeq_left X1 n1 X2 (le_refl n1), interUpTo_zero]
    exact (Set.inter_eq_left.mpr (V.interUpTo_subset_master X1 n1)).symm
  | succ j ih =>
    rw [Nat.add_succ, interUpTo_succ, ih]
    have happ : appendSeq X1 n1 X2 (n1 + j) = X2 j := by
      simp only [appendSeq, ite_eq_right (by omega : ¬ n1 + j < n1)]
      simp_all
    rw [happ, interUpTo_succ, Set.inter_assoc]

/-! ### Finite consistency. -/

/-- **Exercise 1.18 — consistent subset.** `C ⊆ 𝒟` is *finitely consistent* iff
every finite
sequence drawn from `C` is `Consistent` in `𝒟`. -/
def FinitelyConsistent (C : Set (Set α)) : Prop :=
  ∀ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) → V.Consistent X n

/-! ### Intersection of a non-empty family of filters (Scott's last claim). -/

/-- **Exercise 1.18 — the intersection of a non-empty family of filters is a
filter.**
`sInf F = {X ∣ ∀ x ∈ F, X ∈ x}`. -/
def sInf (F : Set V.Element) (hF : F.Nonempty) : V.Element where
  mem X := ∀ x ∈ F, x.mem X
  sub h := hF.elim (fun x hx => x.sub (h x hx))
  master_mem := fun x _ => x.master_mem
  inter_mem h1 h2 := fun x hx => x.inter_mem (h1 x hx) (h2 x hx)
  up_mem h hY hXY := fun x hx => x.up_mem (h x hx) hY hXY

/-- `sInf F ⊑ x` for every `x ∈ F`.
@isnad1 id=le.2h4v.s5.00ba68ec77ba from=translated src=- shape=17e0641d vocab=88028d62
-/
theorem sInf_le (F : Set V.Element) (hF : F.Nonempty) {x : V.Element} (hx : x ∈ F) :
    V.sInf F hF ≤ x :=
  fun _ h => h x hx

/-- `sInf F` is the **greatest** lower bound of `F`.
@isnad1 id=le.2h4v.s6.909f88d1f312 from=translated src=- shape=383dda32 vocab=88028d62
-/
theorem le_sInf (F : Set V.Element) (hF : F.Nonempty) (y : V.Element) (h : ∀ x ∈ F, y ≤ x) :
    y ≤ V.sInf F hF :=
  fun _ hX x hx => h x hx _ hX

/-! ### The least filter containing a consistent `C`. -/

/-- **Exercise 1.18 — the least filter containing a consistent `C`.**
`leastFilter C = {Y ∈ 𝒟 ∣ ⋂_{i<n} Xᵢ ⊆ Y for some finite sequence ⟨Xᵢ⟩ from C}`.
The
intersection law concatenates two finite sequences (`interUpTo_appendSeq`) and
uses finite
consistency to keep their combined intersection in `𝒟`. -/
def leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) : V.Element where
  mem Y := V.mem Y ∧ ∃ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) ∧ V.interUpTo X n ⊆ Y
  sub h := h.1
  master_mem :=
    ⟨V.master_mem, 0, (fun _ => V.master), (fun i hi => absurd hi (Nat.not_lt_zero i)),
      V.interUpTo_subset_master _ 0⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n1, X1, hX1C, hX1sub⟩ ⟨hYmem, n2, X2, hX2C, hX2sub⟩
    have hmemC : ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := appendSeq_mem hX1C hX2C
    have hintermem : V.mem (V.interUpTo (appendSeq X1 n1 X2) (n1 + n2)) :=
      (V.consistent_iff_interUpTo_mem _ (fun i hi => hCsub _ (hmemC i hi))).mp
        (hC _ _ hmemC)
    have hsub : V.interUpTo (appendSeq X1 n1 X2) (n1 + n2) ⊆ X ∩ Y := by
      rw [V.interUpTo_appendSeq X1 n1 X2]
      exact Set.inter_subset_inter hX1sub hX2sub
    exact ⟨V.inter_mem hXmem hYmem hintermem hsub, n1 + n2, appendSeq X1 n1 X2, hmemC, hsub⟩
  up_mem := by
    rintro X Y ⟨_, n, Xs, hXC, hsub⟩ hY hXY
    exact ⟨hY, n, Xs, hXC, hsub.trans hXY⟩

/-- `C ⊆ leastFilter C`: every member of `C` is in the least filter.
@isnad1 id=mem.3h4v.s5.6adbed9151f8 from=translated src=- shape=a5531aef vocab=8e4b1815
-/
theorem subset_leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) {W : Set α} (hW : W ∈ C) :
    (V.leastFilter C hCsub hC).mem W := by
  refine ⟨hCsub W hW, 1, (fun _ => W), (fun _ _ => hW), ?_⟩
  simp_all

/-- **Exercise 1.18 — `leastFilter` is least.** Any filter `z` with `C ⊆ z`
contains
`leastFilter C`.
@isnad1 id=le.3h4v.s6.d8ef3cc195b2 from=translated src=- shape=13e4fa8d vocab=cc044182
-/
theorem leastFilter_le (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) (z : V.Element) (hz : ∀ W ∈ C, z.mem W) :
    V.leastFilter C hCsub hC ≤ z := by
  rintro Y ⟨hYmem, n, X, hXC, hsub⟩
  exact z.up_mem (z.mem_interUpTo X (fun i hi => hz (X i) (hXC i hi))) hYmem hsub

end NeighborhoodSystem

/-! ### A 3-element pairwise-consistent but not consistent set. -/

/-- All non-empty subsets of `Δ = {0,1,2}` (a positive neighbourhood system). -/
def triSys : NeighborhoodSystem (Fin 3) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (⟨0, Set.mem_univ 0⟩) (fun {_} _ => Set.subset_univ _) (fun _ _ _ _ => Iff.rfl)

/--
@isnad1 id=eq.0h0v.s4.5bb35d03fdaa from=translated src=- shape=6eb0f8bf vocab=f2b06000
-/
theorem triSys_master : triSys.master = (Set.univ : Set (Fin 3)) := rfl

namespace triSys

/-- `A = {0,1}`. -/
def A : Set (Fin 3) := {0, 1}
/-- `B = {1,2}`. -/
def B : Set (Fin 3) := {1, 2}
/-- `Cc = {0,2}`. -/
def Cc : Set (Fin 3) := {0, 2}

/-- The three-member family `C = {A, B, Cc}`. -/
def family : Set (Set (Fin 3)) := {A, B, Cc}

/-- Every pair of members of `family` has non-empty intersection, hence (in the
all-non-empty
system `triSys`) every pair is consistent.
@isnad1 id=nonempty.2h2v.s6.1736cc789127 from=translated src=- shape=fd69a325 vocab=99dffc90
-/
theorem family_pairwise_nonempty :
    ∀ X ∈ family, ∀ Y ∈ family, (X ∩ Y).Nonempty := by
  intro X hX Y hY
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp [A]⟩
  · exact ⟨1, by simp [A, B]⟩
  · exact ⟨0, by simp [A, Cc]⟩
  · exact ⟨1, by simp [A, B]⟩
  · exact ⟨1, by simp [B]⟩
  · exact ⟨2, by simp [B, Cc]⟩
  · exact ⟨0, by simp [A, Cc]⟩
  · exact ⟨2, by simp [B, Cc]⟩
  · exact ⟨0, by simp [Cc]⟩

/-- The triple `A, B, Cc` as a finite sequence. -/
def triple : ℕ → Set (Fin 3) := fun i => if i = 0 then A else if i = 1 then B else Cc

/--
@isnad1 id=mem.1h1v.s5.619a673f2bf2 from=translated src=- shape=8075b509 vocab=efb0ccdf
-/
theorem triple_mem : ∀ i, i < 3 → triple i ∈ family := by
  intro i hi
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/--
@isnad1 id=eq.0h0v.s5.7e0f25512bb3 from=translated src=- shape=9668e145 vocab=4d947db5
-/
theorem triple_interUpTo_empty : triSys.interUpTo triple 3 = (∅ : Set (Fin 3)) := by
  simp only [NeighborhoodSystem.interUpTo_succ, NeighborhoodSystem.interUpTo_zero, triSys_master]
  ext x
  fin_cases x <;> simp [triple, A, B, Cc]

/-- **Exercise 1.18 — `family` is pairwise consistent but not consistent.** Its
full triple has
empty intersection, so no `Z ∈ 𝒟` (i.e. no non-empty `Z`) lies below it.
@isnad1 id=not.0h0v.s3.38ffb3007fc3 from=translated src=- shape=431a17b9 vocab=bfdd27f6
-/
theorem not_finitelyConsistent : ¬ triSys.FinitelyConsistent family := by
  intro h
  obtain ⟨Z, hZmem, hZsub⟩ := h 3 triple triple_mem
  have hZne : Z.Nonempty := hZmem
  rw [triple_interUpTo_empty, Set.subset_empty_iff] at hZsub
  simp_all

end triSys

end Domain.Neighborhood
