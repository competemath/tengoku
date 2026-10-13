/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Basic exchangeability definitions

This file starts the Layer 0 exchangeability API: indexed block laws of a family,
prefix laws, path laws, finite exchangeability, full exchangeability, and
contractability. The definitions are intentionally hypothesis-light; measurability
hypotheses enter only in lemmas that compose `Measure.map`s.

`blockLaw` and its characteristic lemmas are stated for an arbitrary index type; the remaining
definitions here are about the order structure of `ℕ` (prefixes, shifts, strictly increasing
selections) and stay sequence-level.

The prefix/tail measurable equivalence `prefixSplitEquiv` is an exception on both counts: it is
neither a roadmap signature nor adapted from the pinned sources, but general infrastructure that
several exchangeability arguments need in order to reindex a sequence as a length-`r` prefix paired
with the tail from index `r`. It lives here because it is stated purely in terms of the order
structure of `ℕ`, with no measure and no process.

The remaining declarations follow the roadmap signatures in
`TauCetiRoadmap/Exchangeability/README.md` and
`TauCetiRoadmap/Exchangeability/Suggested.lean`, Layer 0. They are adapted from the
`cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The finite-dimensional law of a family along a coordinate selection `k`.

The index type is arbitrary: nothing about a finite selection needs the indices to be natural
numbers, and `ExchangeableFamily` selects from an arbitrary type. Sequence-level users get the
`ι = ℕ` case by unification. -/
def blockLaw (μ : Measure Ω) (X : ι → Ω → α) {m : ℕ} (k : Fin m → ι) :
    Measure (Fin m → α) :=
  μ.map fun ω i => X (k i) ω

/-- The law of the first `n` coordinates of a process. -/
@[expose]
def prefixLaw (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Measure (Fin n → α) :=
  blockLaw μ X fun i : Fin n => i.val

/-- The law of the whole process as a measure on path space. -/
@[expose]
def pathLaw (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (ℕ → α) :=
  μ.map fun ω i => X i ω

/-- Projection from path space to the first `n` coordinates. -/
@[expose]
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i.val

/-- The left shift on one-sided path space. -/
@[expose]
def shift (α : Type*) (x : ℕ → α) : ℕ → α :=
  fun n => x (n + 1)

/-- Reindex a one-sided path by a permutation of time. -/
@[expose]
def permReindex (π : Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α :=
  fun n => x (π n)

/-- Finite exchangeability at `n`: the first `n` coordinates have permutation-invariant law. -/
@[expose]
def ExchangeableAt (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n

/-- Finite exchangeability at every length. -/
@[expose]
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n, ExchangeableAt μ X n

/-- Full exchangeability: the path law is invariant under every permutation of `ℕ`. -/
@[expose]
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ π : Equiv.Perm ℕ, μ.map (fun ω i => X (π i) ω) = pathLaw μ X

/-- Contractability, or spreadability: finite-dimensional laws are invariant under strictly
increasing finite subsequences. -/
@[expose]
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k → blockLaw μ X k = prefixLaw μ X m

@[simp]
theorem blockLaw_def (μ : Measure Ω) (X : ι → Ω → α) {m : ℕ} (k : Fin m → ι) :
    blockLaw μ X k = μ.map (fun ω i => X (k i) ω) :=
  (rfl)

-- Annotated `@[grind =>]` rather than `@[simp]`: `blockLaw_def` already simp-normalizes
-- `blockLaw μ X k` to `μ.map …` (so a `@[simp]` here would be shadowed), and the preimage form
-- needs the a.e.-measurability side condition `hXk`, which `simp` cannot discharge.

@[simp]
theorem prefixLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) :
    prefixLaw μ X n = blockLaw μ X (fun i : Fin n => i.val) :=
  rfl

@[simp]
theorem pathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) :
    pathLaw μ X = μ.map (fun ω i => X i ω) :=
  rfl

/-- The path law of the coordinate process on path space is the law itself. -/
theorem pathLaw_coord (ρ : Measure (ℕ → α)) : pathLaw ρ (fun i (x : ℕ → α) => x i) = ρ := by
  rw [pathLaw_def]; exact Measure.map_id'

omit [MeasurableSpace α] in
@[simp]
theorem prefixProj_apply (n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n x i = x i.val :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem shift_apply (x : ℕ → α) (n : ℕ) : shift α x n = x (n + 1) :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem permReindex_apply (π : Equiv.Perm ℕ) (x : ℕ → α) (n : ℕ) :
    permReindex π x n = x (π n) :=
  rfl

omit [MeasurableSpace α] in
/-- Composing `permReindex π` after `permReindex σ` reindexes by `σ * π`. -/
@[simp]
theorem permReindex_permReindex (π σ : Equiv.Perm ℕ) (x : ℕ → α) :
    permReindex (α := α) π (permReindex (α := α) σ x) =
      permReindex (α := α) (σ * π) x := by
  rfl

/-- The prefix projection is measurable. -/
theorem measurable_prefixProj (n : ℕ) : Measurable (prefixProj α n) := by
  unfold prefixProj
  measurability

/-- The one-sided path-space shift is measurable. -/
theorem measurable_shift : Measurable (shift α) := by
  unfold shift
  measurability

/-- Split a sequence into its length-`r` prefix `Fin r → α` and the tail `ℕ → α` from index `r`, as
a measurable equivalence.  The forward map sends `f` to `(fun i => f i.val, fun j => f (r + j))`;
its inverse glues a prefix/tail pair back into a sequence, taking coordinates below `r` from the
prefix and the rest (reindexed by `· - r`) from the tail. -/
def prefixSplitEquiv (r : ℕ) : (ℕ → α) ≃ᵐ (Fin r → α) × (ℕ → α) :=
  (MeasurableEquiv.arrowCongr' (finSumNatEquiv r).symm (.refl α)).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ => α)

/-- **Applying `prefixSplitEquiv`**: it reads off the length-`r` prefix and the tail from index `r`.

This is the one place that depends on the definitional form of `MeasurableEquiv.arrowCongr'` and
`sumPiEquivProdPi`, neither of which exposes an apply lemma. Everything else about the equivalence
is derived from here, so the fragile step is isolated rather than repeated. -/
@[simp]
theorem prefixSplitEquiv_apply (r : ℕ) (f : ℕ → α) :
    prefixSplitEquiv r f = (fun i : Fin r => f (i : ℕ), fun j : ℕ => f (r + j)) := (rfl)

/-- The inverse of `prefixSplitEquiv` glues a prefix/tail pair into a sequence: coordinates below
`r` come from the prefix `p.1`, the rest (reindexed by `· - r`) from the tail `p.2`. -/
@[simp]
theorem prefixSplitEquiv_symm_apply (r : ℕ) (p : (Fin r → α) × (ℕ → α)) (n : ℕ) :
    (prefixSplitEquiv r).symm p n = if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r) := by
  have key : (prefixSplitEquiv r).symm p
      = fun n => if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r) := by
    apply (prefixSplitEquiv r).injective
    rw [MeasurableEquiv.apply_symm_apply, prefixSplitEquiv_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp only [dite_eq_left i.isLt, Fin.eta]
    · have h : ¬ (r + j < r) := Nat.not_lt.mpr (Nat.le_add_right r j)
      simp only [dite_eq_right h, Nat.add_sub_cancel_left]
  rw [key]

/-- The prefix law is the pushforward of the path law by `prefixProj`. -/
theorem map_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : AEMeasurable (fun ω => fun i => X i ω) μ) (n : ℕ) :
    (pathLaw μ X).map (prefixProj α n) = prefixLaw μ X n := by
  rw [pathLaw_def, prefixLaw_def, blockLaw_def]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable hX,
    Function.comp_def]
  rfl

theorem Exchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : Exchangeable μ X) (n : ℕ) : ExchangeableAt μ X n :=
  h n

theorem ExchangeableAt.permute {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) (σ : Equiv.Perm (Fin n)) :
    blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n :=
  h σ

theorem FullyExchangeable.permute {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (π : Equiv.Perm ℕ) :
    μ.map (fun ω i => X (π i) ω) = pathLaw μ X :=
  h π

end Probability

end TauCeti
