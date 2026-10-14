/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku

/-!
# A finite product probability space

The probabilistic input to the Lovász local lemma of Section 10 of `bs_lambda.txt` is a
uniformly random assignment of a label to each of finitely many independent coordinates.
We model this by plain counting over the finite product type `Cfg β = ∀ a, β a`; no measure
theory is involved.

An event `E : Finset (Cfg β)` is *determined* by a coordinate set `S` when membership in `E`
only depends on the restriction of a configuration to `S`.  Two events determined by disjoint
coordinate sets are independent (`pr_inter_of_disjoint_support`); this is the only
probabilistic input the local lemma needs.

`pr E` is `E.dens`, the density of `E` in the space of all configurations, viewed as a real
number; `pr_eq_div` is the corresponding quotient of cardinalities.

Besides independence the file provides finite additivity (`pr_biUnion`), the union bound
(`pr_biUnion_le`) and the counting probabilities of the *pinning* events "coordinate `a` lands
in `s a` for every `a ∈ T`" (`pr_coord_mem`, `pr_pin_eq`, `pr_pin_le`).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda.LLL

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]

/-- A configuration: an assignment of a value to every coordinate. -/
abbrev Cfg (β : A → Type*) : Type _ := ∀ a, β a

/-- The uniform counting probability of an event: its density in the space of all
configurations. -/
noncomputable def pr (E : Finset (Cfg β)) : ℝ := E.dens

section Basic

omit [(a : A) → DecidableEq (β a)]

/-- `pr` as a quotient of cardinalities.
@isnad1 id=eq.0h3v.s5.6cf732e931e7 from=translated src=- shape=a663e281 vocab=0af30520
-/
theorem pr_eq_div (E : Finset (Cfg β)) :
    pr E = (E.card : ℝ) / (Fintype.card (Cfg β) : ℝ) := Finset.nnratCast_dens E

/-- Probabilities are nonnegative.
@isnad1 id=le.0h3v.s5.8ab3ad4c468f from=translated src=- shape=28e6b5a7 vocab=8f344a7a
-/
theorem pr_nonneg (E : Finset (Cfg β)) : 0 ≤ pr E := NNRat.cast_nonneg _

/-- The empty event has probability zero.
@isnad1 id=eq.0h2v.s5.e2de97f7b177 from=translated src=- shape=4d744fd6 vocab=98f4e120
-/
@[simp] theorem pr_empty : pr (∅ : Finset (Cfg β)) = 0 := by simp [pr]

/-- An event has positive probability exactly when it is nonempty.
@isnad1 id=iff.0h3v.s5.7efffe9fa6a4 from=translated src=- shape=914f1def vocab=223765a1
-/
theorem pr_pos_iff {E : Finset (Cfg β)} : 0 < pr E ↔ E.Nonempty := by simp [pr]

/-- Probability is monotone in the event.
@isnad1 id=le.1h4v.s6.0cae97658cb0 from=translated src=- shape=dfedaa97 vocab=8f344a7a
-/
theorem pr_mono {E F : Finset (Cfg β)} (h : E ⊆ F) : pr E ≤ pr F := by
  simpa [pr] using Finset.dens_le_dens h

/-- Probabilities are at most one.
@isnad1 id=le.0h3v.s5.fa4988497982 from=translated src=- shape=1cc40211 vocab=8f344a7a
-/
theorem pr_le_one (E : Finset (Cfg β)) : pr E ≤ 1 := by simp [pr]

variable [∀ a, Nonempty (β a)]

/-- The number of configurations is positive, so the counting probability is well defined.
@isnad1 id=lt.0h2v.s5.ccf89edaa880 from=translated src=- shape=796c7c69 vocab=b639b179
-/
theorem card_cfg_pos_real : (0 : ℝ) < (Fintype.card (Cfg β) : ℝ) :=
  Nat.cast_pos.mpr Fintype.card_pos

/-- The whole space has probability one.
@isnad1 id=eq.0h2v.s5.c7b27989ec09 from=translated src=- shape=87af877d vocab=cacd15c4
-/
@[simp] theorem pr_univ : pr (Finset.univ : Finset (Cfg β)) = 1 := by simp [pr]

end Basic

section Additivity

/-- **Finite additivity.**  The probability of a union of pairwise disjoint events is the sum
of the probabilities.
@isnad1 id=eq.1h5v.s7.40cf089353a6 from=translated src=- shape=010dfebe vocab=41e22c2d
-/
theorem pr_biUnion {κ : Type*} {T : Finset κ} {E : κ → Finset (Cfg β)}
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (E i) (E j)) :
    pr (T.biUnion E) = ∑ i ∈ T, pr (E i) := by
  simp only [pr_eq_div]
  rw [Finset.card_biUnion hdisj, Nat.cast_sum, Finset.sum_div]

/-- Splitting an event according to whether `E` occurs.
@isnad1 id=eq.0h4v.s7.1caac130ae43 from=translated src=- shape=1bce5720 vocab=30e94b5b
-/
theorem pr_inter_add_pr_compl_inter (E F : Finset (Cfg β)) :
    pr (E ∩ F) + pr (Eᶜ ∩ F) = pr F := by
  rw [Finset.inter_comm E F, Finset.inter_comm Eᶜ F, ← Finset.sdiff_eq_inter_compl, pr, pr, pr,
    ← NNRat.cast_add, Finset.dens_inter_add_dens_sdiff]

/-- The complementary form of `pr_inter_add_pr_compl_inter`.
@isnad1 id=eq.0h4v.s7.ae7b62ae101c from=translated src=- shape=410fbf2f vocab=7e238307
-/
theorem pr_compl_inter (E F : Finset (Cfg β)) : pr (Eᶜ ∩ F) = pr F - pr (E ∩ F) :=
  eq_sub_of_add_eq' (pr_inter_add_pr_compl_inter E F)

variable [∀ a, Nonempty (β a)]

/-- **The union bound.**  The probability of a finite union is at most the sum of the
probabilities.
@isnad1 id=le.0h5v.s6.dcea796124df from=translated src=- shape=b9b81d44 vocab=57621c77
-/
theorem pr_biUnion_le {κ : Type*} (T : Finset κ) (E : κ → Finset (Cfg β)) :
    pr (T.biUnion E) ≤ ∑ i ∈ T, pr (E i) := by
  simp only [pr_eq_div]
  rw [div_le_iff₀ card_cfg_pos_real, ← Finset.sum_div, div_mul_cancel₀ _ card_cfg_pos_real.ne']
  exact_mod_cast Finset.card_biUnion_le (s := T) (t := E)

/-- The union bound in the form used to cover an event by an enumeration of cases.
@isnad1 id=le.1h6v.s6.ee227597e4bb from=translated src=- shape=5a819872 vocab=57621c77
-/
theorem pr_le_of_subset_biUnion {κ : Type*} {E : Finset (Cfg β)}
    (T : Finset κ) (f : κ → Finset (Cfg β)) (h : E ⊆ T.biUnion f) :
    pr E ≤ ∑ i ∈ T, pr (f i) := (pr_mono h).trans (pr_biUnion_le T f)

end Additivity

/-- `E` depends only on the coordinates in `S`. -/
def Determined (S : Finset A) (E : Finset (Cfg β)) : Prop :=
  ∀ ω ω' : Cfg β, (∀ a ∈ S, ω a = ω' a) → (ω ∈ E ↔ ω' ∈ E)

section Determined

omit [Fintype A] [DecidableEq A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)] in
/-- An event determined by `S` is determined by any larger coordinate set.
@isnad1 id=determin.2h5v.s5.3411e5309873 from=translated src=- shape=22e60b6f vocab=71ae59a6
-/
theorem Determined.mono {S T : Finset A} {E : Finset (Cfg β)} (hST : S ⊆ T)
    (hE : Determined S E) : Determined T E :=
  fun ω ω' h ↦ hE ω ω' fun a ha ↦ h a (hST ha)

omit [(a : A) → Fintype (β a)] in
/-- The intersection of two determined events is determined by the union of the supports.
@isnad1 id=determin.2h6v.s6.6fd5df5c3fe1 from=translated src=- shape=188932f2 vocab=7c430b1e
-/
theorem Determined.inter {S T : Finset A} {E F : Finset (Cfg β)} (hE : Determined S E)
    (hF : Determined T F) : Determined (S ∪ T) (E ∩ F) := by
  intro ω ω' h
  simp only [Finset.mem_inter]
  exact and_congr (hE ω ω' fun a ha ↦ h a (Finset.mem_union_left _ ha))
    (hF ω ω' fun a ha ↦ h a (Finset.mem_union_right _ ha))

/-- The complement of a determined event is determined by the same coordinates.
@isnad1 id=determin.1h4v.s6.f4adb3d6405d from=translated src=- shape=f1865697 vocab=f3125125
-/
theorem Determined.compl {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E) :
    Determined S Eᶜ := by
  intro ω ω' h
  simp only [Finset.mem_compl]
  exact not_congr (hE ω ω' h)

omit [(a : A) → DecidableEq (β a)] in
/-- The standard way to exhibit a determined event: an event cut out of the whole space by a
predicate that only reads the coordinates in `S`.
@isnad1 id=determin.1h4v.s6.e040226d14ac from=translated src=- shape=78754ccc vocab=6808cd9e
-/
theorem determined_filter_univ {S : Finset A} (p : Cfg β → Prop) [DecidablePred p]
    (hp : ∀ ω ω' : Cfg β, (∀ a ∈ S, ω a = ω' a) → (p ω ↔ p ω')) :
    Determined S (Finset.univ.filter p) := fun ω ω' h ↦ by simpa using hp ω ω' h

/-- The event that one coordinate lands in a prescribed set is determined by that
coordinate.
@isnad1 id=determin.0h4v.s6.50031b6a9236 from=translated src=- shape=f5f66975 vocab=cb9e15c3
-/
theorem determined_coord (a : A) (s : Finset (β a)) :
    Determined {a} (Finset.univ.filter fun ω : Cfg β => ω a ∈ s) :=
  determined_filter_univ _ fun _ _ hagree ↦ by
    rw [hagree a (Finset.mem_singleton_self a)]

/-- A pinning event is determined by the coordinates it pins.
@isnad1 id=determin.0h4v.s7.569b65733fdf from=translated src=- shape=3fce7761 vocab=5c5e77d9
-/
theorem determined_pin (T : Finset A) (s : (a : A) → Finset (β a)) :
    Determined T (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a) :=
  determined_filter_univ _ fun _ _ hagree ↦
    forall₂_congr fun a ha ↦ by rw [hagree a ha]

end Determined

section Independence

section Glue

omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]

/-- `glue S u v` is the configuration following `u` on `S` and `v` off `S`. -/
def glue (S : Finset A) (u v : Cfg β) : Cfg β := fun a ↦ if a ∈ S then u a else v a

/--
@isnad1 id=eq.1h6v.s5.15632b74d970 from=translated src=- shape=29474f2b vocab=8c3d1b11
-/
@[simp] theorem glue_apply_of_mem {S : Finset A} {u v : Cfg β} {a : A} (ha : a ∈ S) :
    glue S u v a = u a := by simp [glue, ha]

/--
@isnad1 id=eq.1h6v.s5.7d156e96faa3 from=translated src=- shape=6d4bede0 vocab=8c3d1b11
-/
@[simp] theorem glue_apply_of_notMem {S : Finset A} {u v : Cfg β} {a : A} (ha : a ∉ S) :
    glue S u v a = v a := by simp [glue, ha]

/-- An event determined by `S` only sees the `S`-half of a glued configuration.
@isnad1 id=iff.1h6v.s6.9eb59664c013 from=translated src=- shape=ab5985c8 vocab=dc4309ea
-/
theorem Determined.mem_glue_iff_left {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E)
    {u v : Cfg β} : glue S u v ∈ E ↔ u ∈ E :=
  hE _ _ fun _ ha ↦ glue_apply_of_mem ha

/-- An event determined by a set disjoint from `S` only sees the off-`S` half of a glued
configuration.
@isnad1 id=iff.2h7v.s6.7352ee40dc20 from=translated src=- shape=4f237b92 vocab=779d4018
-/
theorem Determined.mem_glue_iff_right {S T : Finset A} {F : Finset (Cfg β)}
    (hF : Determined T F) (hST : Disjoint S T) {u v : Cfg β} : glue S u v ∈ F ↔ v ∈ F :=
  hF _ _ fun _ ha ↦ glue_apply_of_notMem (Finset.disjoint_right.mp hST ha)

/-- The involution `(u, v) ↦ (glue S u v, glue S v u)` used to prove independence. -/
def swapGlue (S : Finset A) (p : Cfg β × Cfg β) : Cfg β × Cfg β :=
  (glue S p.1 p.2, glue S p.2 p.1)

/-- `swapGlue S` is an involution.
@isnad1 id=eq.0h4v.s5.62fccbbc25f5 from=translated src=- shape=09a82fd2 vocab=7cf0887a
-/
theorem swapGlue_swapGlue (S : Finset A) (p : Cfg β × Cfg β) :
    swapGlue S (swapGlue S p) = p := by
  refine Prod.ext (funext fun a ↦ ?_) (funext fun a ↦ ?_) <;>
    by_cases ha : a ∈ S <;> simp [swapGlue, ha]

end Glue

variable [∀ a, Nonempty (β a)]

/-- **Independence.**  Two events determined by disjoint sets of coordinates are independent
for the uniform counting probability.  This is the probabilistic input to the local lemma of
Section 10 of `bs_lambda.txt`.
@isnad1 id=eq.3h6v.s6.c5036a072ab0 from=translated src=- shape=b28dd994 vocab=b2b5d256
-/
theorem pr_inter_of_disjoint_support {S T : Finset A} {E F : Finset (Cfg β)}
    (hE : Determined S E) (hF : Determined T F) (hST : Disjoint S T) :
    pr (E ∩ F) = pr E * pr F := by
  -- `swapGlue S` is a bijection between `(E ∩ F) ×ˢ univ` and `E ×ˢ F`
  have hcard : ((E ∩ F) ×ˢ (Finset.univ : Finset (Cfg β))).card = (E ×ˢ F).card := by
    refine Finset.card_nbij' (swapGlue S) (swapGlue S) ?_ ?_ (fun p _ ↦ swapGlue_swapGlue S p)
      (fun q _ ↦ swapGlue_swapGlue S q)
    all_goals
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_inter, Finset.mem_univ,
        and_true] at hp ⊢
      exact ⟨hE.mem_glue_iff_left.mpr hp.1, (hF.mem_glue_iff_right hST).mpr hp.2⟩
  rw [Finset.card_product, Finset.card_product, Finset.card_univ] at hcard
  have hcast : ((E ∩ F).card : ℝ) * (Fintype.card (Cfg β) : ℝ) = (E.card : ℝ) * (F.card : ℝ) :=
    mod_cast hcard
  rw [pr_eq_div, pr_eq_div, pr_eq_div, div_mul_div_comm, div_eq_div_iff card_cfg_pos_real.ne'
    (mul_ne_zero card_cfg_pos_real.ne' card_cfg_pos_real.ne'), ← hcast]
  ring

end Independence

section Pinning

/-- **Counting core.**  Pinning one coordinate to a prescribed value divides the number of
configurations by the size of that coordinate's alphabet.
@isnad1 id=eq.0h4v.s6.85167f521339 from=translated src=- shape=3e94770d vocab=8acde319
-/
theorem card_filter_coord_mul_card (a : A) (b : β a) :
    (Finset.univ.filter fun ω : Cfg β => ω a = b).card * Fintype.card (β a)
      = Fintype.card (Cfg β) := by
  have h := Fintype.card_filter_piFinset_eq_of_mem
    (fun i ↦ (Finset.univ : Finset (β i))) a (Finset.mem_univ b)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [h, Fintype.card_pi]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ a)

variable [∀ a, Nonempty (β a)]

/-- A single coordinate takes a prescribed value with probability `1 / |β a|`.
@isnad1 id=eq.0h4v.s6.f4cd26261494 from=translated src=- shape=80b51350 vocab=2a1c26f2
-/
theorem pr_coord_eq (a : A) (b : β a) :
    pr (Finset.univ.filter fun ω : Cfg β => ω a = b) = 1 / (Fintype.card (β a) : ℝ) := by
  rw [pr_eq_div, div_eq_div_iff card_cfg_pos_real.ne'
    (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := β a)).ne'), one_mul]
  exact_mod_cast card_filter_coord_mul_card a b

/-- A single coordinate lands in a prescribed set with probability `|s| / |β a|`.
@isnad1 id=eq.0h4v.s7.ee5a0f470aa6 from=translated src=- shape=a9cc363a vocab=8ee6e0e9
-/
theorem pr_coord_mem (a : A) (s : Finset (β a)) :
    pr (Finset.univ.filter fun ω : Cfg β => ω a ∈ s)
      = (s.card : ℝ) / (Fintype.card (β a) : ℝ) := by
  have hU : (Finset.univ.filter fun ω : Cfg β ↦ ω a ∈ s)
      = s.biUnion (fun b ↦ Finset.univ.filter fun ω : Cfg β ↦ ω a = b) := by
    ext ω
    simp
  have hdisj : ∀ b ∈ s, ∀ c ∈ s, b ≠ c →
      Disjoint (Finset.univ.filter fun ω : Cfg β ↦ ω a = b)
        (Finset.univ.filter fun ω : Cfg β ↦ ω a = c) := fun b _ c _ hbc ↦
    Finset.disjoint_filter.2 fun ω _ h1 h2 ↦ hbc (h1 ▸ h2)
  rw [hU, pr_biUnion hdisj, Finset.sum_congr rfl fun b _ ↦ pr_coord_eq a b, Finset.sum_const,
    nsmul_eq_mul, mul_one_div]

/-- **Pinning several coordinates.**  Distinct coordinates are independent, so the
probability that each of them lands in a prescribed set is the product of the individual
probabilities.
@isnad1 id=eq.0h4v.s8.6f719555494c from=translated src=- shape=82785d1d vocab=a9fac30f
-/
theorem pr_pin_eq (T : Finset A) (s : (a : A) → Finset (β a)) :
    pr (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a)
      = ∏ a ∈ T, ((s a).card : ℝ) / (Fintype.card (β a) : ℝ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have heq : (Finset.univ.filter fun ω : Cfg β ↦ ∀ b ∈ insert a T, ω b ∈ s b) =
        (Finset.univ.filter fun ω : Cfg β ↦ ω a ∈ s a) ∩
        (Finset.univ.filter fun ω : Cfg β ↦ ∀ b ∈ T, ω b ∈ s b) := by
      ext ω
      simp
    have hdisj : Disjoint {a} T := by simp [ha]
    rw [heq, pr_inter_of_disjoint_support (determined_coord a (s a)) (determined_pin T s) hdisj,
      pr_coord_mem, ih, Finset.prod_insert ha]

/-- Pinning several coordinates into target sets of size at most `m`.
@isnad1 id=le.1h5v.s8.11cfd1607d12 from=translated src=- shape=0c9e4f98 vocab=8284cb55
-/
theorem pr_pin_le (T : Finset A) (s : (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ a ∈ T, (s a).card ≤ m) :
    pr (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a)
      ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
  rw [pr_pin_eq]
  gcongr with a ha
  exact_mod_cast hm a ha

end Pinning

end BSLambda.LLL
