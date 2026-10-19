/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku.LeanPool.LeanPool.BlockSpectralSensitivity.LLL.Prob
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Powerset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The asymmetric Lovász local lemma

Mathlib does not contain the Lovász local lemma, so we prove the version we need from
scratch, for the finite counting probability space of `BSLambda.LLL.Prob`.

Events are given by a family `Ev : I → Finset (Cfg β)`, each `Ev i` being determined by the
coordinate set `supp i`.  Two events are *dependent* when their supports meet.  `nbr supp i`
collects the indices of the events other than `i` that are dependent with `Ev i`.

The main results are `pr_avoid_pos` (the general asymmetric local lemma of Section 10 of
`bs_lambda.txt`) and `pr_avoid_pos_two_type` (the two-type statement of Section 10.2).

The last section is independent of the local lemma: `pr_le_prod_of_pinned` and its
constant-alphabet form `pr_le_pow_of_pinned` bound the probability of an event that pins a set
of coordinates to targets read off a disjoint set of coordinates.  They supply the hypothesis
`hcond` above at the places where the local lemma is applied.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda.LLL

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Dependency neighbourhoods and avoidance events -/

/-- The dependency neighbourhood: other events whose supports meet ours. -/
def nbr (supp : I → Finset A) (i : I) : Finset I :=
  Finset.univ.filter fun j ↦ j ≠ i ∧ ¬ Disjoint (supp i) (supp j)

omit [Fintype A] in
/-- Membership in the dependency neighbourhood. -/
@[simp] theorem mem_nbr {supp : I → Finset A} {i j : I} :
    j ∈ nbr supp i ↔ j ≠ i ∧ ¬ Disjoint (supp i) (supp j) := by
  simp [nbr]

omit [Fintype A] in
/-- The events indexed outside the dependency neighbourhood of `i` are supported away from
`supp i`. -/
theorem disjoint_supp_sup_sdiff_nbr {supp : I → Finset A} {i : I} {S : Finset I} (hi : i ∉ S) :
    Disjoint (supp i) ((S \ nbr supp i).sup supp) := by
  rw [Finset.disjoint_sup_right]
  intro j hj
  rw [Finset.mem_sdiff] at hj
  by_contra hc
  exact hj.2 (mem_nbr.mpr ⟨fun e ↦ hi (e ▸ hj.1), hc⟩)

/-- The event that none of the bad events indexed by `S` occurs. -/
def avoid (Ev : I → Finset (Cfg β)) (S : Finset I) : Finset (Cfg β) :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ Ev i

section AvoidBasic

omit [∀ (a : A), Nonempty (β a)] in
/-- Membership in `avoid`. -/
@[simp] theorem mem_avoid {Ev : I → Finset (Cfg β)} {S : Finset I} {ω : Cfg β} :
    ω ∈ avoid Ev S ↔ ∀ i ∈ S, ω ∉ Ev i := by
  simp [avoid]

omit [∀ (a : A), Nonempty (β a)] in
/-- Avoiding no events is the sure event. -/
@[simp] theorem avoid_empty (Ev : I → Finset (Cfg β)) :
    avoid Ev ∅ = (Finset.univ : Finset (Cfg β)) := by
  ext ω
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- Avoiding every event is avoiding all of them. -/
theorem avoid_univ (Ev : I → Finset (Cfg β)) :
    avoid Ev (Finset.univ : Finset I) = Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i := by
  ext ω
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- Avoiding more events is a smaller event. -/
theorem avoid_anti {Ev : I → Finset (Cfg β)} {S T : Finset I} (h : S ⊆ T) :
    avoid Ev T ⊆ avoid Ev S :=
  fun _ hω ↦ mem_avoid.mpr fun i hi ↦ mem_avoid.mp hω i (h hi)

omit [∀ (a : A), Nonempty (β a)] in
/-- Peeling one event off `avoid`. -/
theorem avoid_insert (Ev : I → Finset (Cfg β)) (i : I) (S : Finset I) :
    avoid Ev (insert i S) = (Ev i)ᶜ ∩ avoid Ev S := by
  ext ω
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- `avoid Ev S` is determined by the union of the supports of the events indexed by `S`. -/
theorem determined_avoid {Ev : I → Finset (Cfg β)} {supp : I → Finset A}
    (hdet : ∀ i, Determined (supp i) (Ev i)) (S : Finset I) :
    Determined (S.sup supp) (avoid Ev S) := fun ω ω' h ↦ by
  simp only [mem_avoid]
  exact forall₂_congr fun i hi ↦
    not_congr (hdet i ω ω' fun a ha ↦ h a (Finset.le_sup (f := supp) hi ha))

end AvoidBasic

/-! ## The local lemma -/

section Telescope

end Telescope

section Main

variable (Ev : I → Finset (Cfg β)) (supp : I → Finset A) (x : I → ℝ)

end Main

/-! ## The two-type form -/

section TwoType

end TwoType

/-! ## Pinning coordinates whose targets depend on other coordinates -/

section Fibre

variable {G : Finset A}

/-- The event that a configuration agrees on `G` with the partial configuration `c`. -/
def fibre (G : Finset A) (c : (a : A) → a ∈ G → β a) : Finset (Cfg β) :=
  Finset.univ.filter fun ω : Cfg β ↦ ∀ a, ∀ ha : a ∈ G, ω a = c a ha

omit [∀ (a : A), Nonempty (β a)] in
/-- Membership in a fibre. -/
@[simp] theorem mem_fibre {c : (a : A) → a ∈ G → β a} {ω : Cfg β} :
    ω ∈ fibre G c ↔ ∀ a, ∀ ha : a ∈ G, ω a = c a ha := by
  simp [fibre]

omit [∀ (a : A), Nonempty (β a)] in
/-- Every configuration lies in the fibre over its own restriction to `G`. -/
theorem mem_fibre_restrict (ω : Cfg β) : ω ∈ fibre G fun a _ ↦ ω a := by
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- A fibre over `G` is determined by `G`. -/
theorem determined_fibre (c : (a : A) → a ∈ G → β a) : Determined G (fibre G c) :=
  determined_filter_univ _ fun _ _ h ↦
    forall_congr' fun a ↦ forall_congr' fun ha ↦ by rw [h a ha]

omit [∀ (a : A), Nonempty (β a)] in
/-- Distinct partial configurations have disjoint fibres. -/
theorem disjoint_fibre {c c' : (a : A) → a ∈ G → β a} (h : c ≠ c') :
    Disjoint (fibre G c) (fibre G c') := by
  simp only [Finset.disjoint_left, mem_fibre]
  exact fun ω h1 h2 ↦ h (funext fun a ↦ funext fun ha ↦ (h1 a ha).symm.trans (h2 a ha))

/-- The fibres over `G` partition the configuration space, so their probabilities sum to `1`. -/
theorem sum_pr_fibre (G : Finset A) :
    ∑ c ∈ G.pi fun a ↦ (Finset.univ : Finset (β a)), pr (fibre G c) = 1 := by
  have hcover : (G.pi fun a ↦ (Finset.univ : Finset (β a))).biUnion (fibre G)
      = (Finset.univ : Finset (Cfg β)) :=
    Finset.eq_univ_of_forall fun ω ↦ Finset.mem_biUnion.mpr
      ⟨fun a _ ↦ ω a, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _, mem_fibre_restrict ω⟩
  rw [← pr_biUnion fun c _ c' _ hne ↦ disjoint_fibre hne, hcover, pr_univ]

end Fibre

section Pinned

omit [∀ a, DecidableEq (β a)] in
/-- **Pinning with targets read off other coordinates.**  If, on the event `E`, every
coordinate of `T` lands in a target set of size at most `m` that depends only on the
coordinates of a set `G` disjoint from `T`, then `E` has probability at most
`∏ a ∈ T, m / |β a|`.  This is the counting form of "condition on `G`; the coordinates of
`T` are still independent and uniform". -/
theorem pr_le_prod_of_pinned {G T : Finset A} (hGT : Disjoint G T)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
  classical
  set C : Finset ((a : A) → a ∈ G → β a) := G.pi fun a ↦ (Finset.univ : Finset (β a))
  set P : ((a : A) → a ∈ G → β a) → Finset (Cfg β) :=
    fun c ↦ Finset.univ.filter fun ω : Cfg β ↦ ∀ a ∈ T, ω a ∈ tgt c a
  have hsub : E ⊆ C.biUnion fun c ↦ fibre G c ∩ P c := fun ω hω ↦
    Finset.mem_biUnion.mpr ⟨fun a _ ↦ ω a, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨mem_fibre_restrict ω, (Finset.mem_filter_univ ω).mpr (hE ω hω)⟩⟩
  calc pr E ≤ ∑ c ∈ C, pr (fibre G c ∩ P c) := pr_le_of_subset_biUnion C _ hsub
    _ = ∑ c ∈ C, pr (fibre G c) * pr (P c) := Finset.sum_congr rfl fun c _ ↦
        pr_inter_of_disjoint_support (determined_fibre c) (determined_pin T (tgt c)) hGT
    _ ≤ ∑ c ∈ C, pr (fibre G c) * ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) :=
        Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (pr_pin_le T (tgt c) m (hm c)) (pr_nonneg _)
    _ = ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
        rw [← Finset.sum_mul, sum_pr_fibre, one_mul]

omit [∀ a, DecidableEq (β a)] in
/-- The constant-alphabet form of `pr_le_prod_of_pinned`, as used in Sections 8.1 and 9. -/
theorem pr_le_pow_of_pinned {G T : Finset A} (hGT : Disjoint G T) (N : ℕ)
    (hN : ∀ a ∈ T, Fintype.card (β a) = N)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ((m : ℝ) / N) ^ T.card := by
  classical
  exact
  (pr_le_prod_of_pinned hGT tgt m hm hE).trans_eq <|
    (Finset.prod_congr rfl fun a ha ↦ by rw [hN a ha]).trans (Finset.prod_const _)

end Pinned

end BSLambda.LLL
