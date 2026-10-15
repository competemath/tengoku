/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Basic
public import Tengoku

/-!
# Example 1.B (Scott 1981, PRG-19, §1) — binary sequences

Scott's recurring **binary** example, generalizing the finite binary tree of
Example 1.4 to
*infinite* sequences. Take `Δ = Σ*` with `Σ = {0,1}` (the finite binary strings,
`Λ` = the empty
string), and for `σ ∈ Σ*` let `σΣ*` be the set of all *extensions* of `σ`. The
neighbourhoods are

`B = {σΣ* ∣ σ ∈ Σ*}`,

a neighbourhood being "all extensions of a fixed prefix `σ`". We encode `Σ* = List
Bool`, the
empty sequence `Λ = []`, concatenation `στ = σ ++ τ`, and the *initial-segment*
relation
`σ prefix τ` by mathlib's list-prefix order `σ <+: τ`. The cone `σΣ*` is `cone σ = {w ∣
σ <+: w}`.

Deliverables (all of the Example-1.B paragraph, lines 281–315 of the source):

* **Example 1.B / Exercise (`B` is a system).** `B : NeighborhoodSystem Str`,
built from the
  prefix *trichotomy* via `ofNestedOrDisjoint` — any two cones are nested or
  disjoint.
* **`σ⊥` (the finite elements).** `sigmaBot σ = ↑(cone σ)`, the principal filter
of `σΣ*`; its
  minimal neighbourhood is `σΔ = cone σ`.
* **Factoid `σ₀⊥ ⊆ σ₁⊥ iff σ₀` initial segment of `σ₁`.** `sigmaBot_le_iff`.
* **Exercise (`σx ∈ |B|`).** `sigmaElt σ x`, and `sigmaElt σ ⊥ = σ⊥`
(`sigmaElt_bot`) justifying
  the `σ⊥` notation.
* **Factoid `x = ⋃ₙ σₙ⊥`.** `mem_iff_exists_sigmaBot`: every `x ∈ |B|` is the
union of the finite
  elements `σ⊥` with `σΣ* ∈ x` — the concrete "limit of finite approximations" in
  `|B|`. (The
  countable *chain* form, with `σₙ prefix σₙ₊₁` enumerated, needs choice and is left to
  the prose.)

Everything is **constructive** (`#print axioms ⊆ {propext, Quot.sound}`):
list-prefix is decidable,
so the trichotomy is choice-free.
-/

@[expose] public section

namespace Domain.Neighborhood.ExampleB

open Domain.Neighborhood NeighborhoodSystem

/-- The token type `Σ* = List Bool` (finite binary strings); `Λ = []`. -/
abbrev Str := List Bool

/-- The neighbourhood `σΣ*`: all *extensions* of `σ` (sequences with `σ` as an
initial segment). -/
def cone (σ : Str) : Set Str := {w | σ <+: w}

/--
@isnad1 id=iff.0h2v.s4.fdb710039b64 from=translated src=- shape=542ed584 vocab=1c50368c
-/
@[simp] theorem mem_cone {σ w : Str} : w ∈ cone σ ↔ σ <+: w := Iff.rfl

/-- `ΛΣ* = Σ*`: the cone of the empty string is everything (Scott's `Δ`).
@isnad1 id=eq.0h0v.s3.f8d0071ecb2e from=translated src=- shape=f18a2434 vocab=10b488b1
-/
theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

/-- **Cones reverse the prefix order.** `σΣ* ⊆ τΣ*` iff `τ` is an initial segment
of `σ`: a longer
prefix carves out a *smaller* cone. (`→` tests at `σ ∈ σΣ*`; `←` is transitivity
of `<+:`.)
@isnad1 id=iff.0h2v.s4.36035de3a0fc from=translated src=- shape=19c51dc9 vocab=96580b8f
-/
theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

/-- **Cones are one-one in the prefix.** `cone σ = cone τ ⟹ σ = τ`: from the two
inclusions we get
`τ <+: σ` and `σ <+: τ`, and a prefix-antisymmetry (equal lengths) finishes. Used
by the approximable
maps `B → T` / `B → B` (Examples 2.3, 2.4) to read off the unique generating
prefix of a cone.
@isnad1 id=eq.1h2v.s4.d81c6d1acb1d from=translated src=- shape=8d95209b vocab=55da7df5
-/
theorem cone_injective {σ τ : Str} (h : cone σ = cone τ) : σ = τ := by
  have h1 : τ <+: σ := cone_subset_cone.mp (le_of_eq h)
  have h2 : σ <+: τ := cone_subset_cone.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

/-- **Prefix trichotomy for cones.** Any two cones are nested-or-disjoint: either
one contains the
other, or they are disjoint (incomparable prefixes have no common extension).
Choice-free: the
prefix relation on `List Bool` is decidable.
@isnad1 id=or.0h2v.s5.1702c5bd9607 from=translated src=- shape=615a3bce vocab=11761244
-/
theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in Scott's binary neighbourhood system `B`: `X ∈ B` iff `X = σΣ*`
for some `σ`. -/
def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

/-- **Exercise ("`B` is a neighbourhood system").** The family `B = {σΣ* ∣ σ ∈
Σ*}` is pairwise
nested-or-disjoint, by `cone_trichotomy`.
@isnad1 id=nestedor.0h0v.s1.a389fedc83ee from=translated src=- shape=25b03439 vocab=b44ac6c5
-/
theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone_trichotomy σ τ

/-- **Example 1.B (Scott 1981, PRG-19).** The binary neighbourhood system `B` on
`Δ = Σ*`. -/
def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ ⟨[], cone_nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

/--
@isnad1 id=iff.0h1v.s3.794cfedaff49 from=translated src=- shape=d213e086 vocab=6221367a
-/
@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

/--
@isnad1 id=eq.0h0v.s3.747c6c18685c from=translated src=- shape=d672ce25 vocab=1a9a50e2
-/
@[simp] theorem B_master : B.master = Set.univ := rfl

/-- Every cone is a neighbourhood of `B`.
@isnad1 id=mem.0h1v.s2.67e2ef8266ca from=translated src=- shape=9bb0b988 vocab=0ea5085f
-/
theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

/-! ### Prepending a prefix: `σX = {στ ∣ τ ∈ X}`. -/

/-- Scott's `σX = {στ ∣ τ ∈ X}` (prepend the prefix `σ` to every member of `X`). -/
def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

/--
@isnad1 id=iff.0h3v.s5.868eddec1e19 from=translated src=- shape=f97296ed vocab=9e498b1d
-/
@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

/-- **`σ(τΣ*) = (στ)Σ*`.** Prepending `σ` to a cone yields the cone of the
concatenation — this is
why `σx` lands back in `B` and why `σ⊥` is again a finite element.
@isnad1 id=eq.0h2v.s4.d322a22e4cb8 from=translated src=- shape=0067d683 vocab=9ab1a8c3
-/
theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
  constructor
  · simp_all
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

/-- `σΣ* = σ·Σ*`: prepending `σ` to the whole space recovers the cone of `σ`.
@isnad1 id=eq.0h1v.s3.1b3573d9e395 from=translated src=- shape=bb0e013e vocab=1c4fe956
-/
theorem prepend_univ (σ : Str) : prepend σ Set.univ = cone σ := by
  ext w
  simp only [mem_prepend, Set.mem_univ, true_and, mem_cone]
  constructor
  · simp_all
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

/-- Prepending preserves membership in `B` (`σ` applied to a cone is a cone).
@isnad1 id=mem.1h2v.s4.a7cceef0d2d0 from=translated src=- shape=32106f09 vocab=3977499e
-/
theorem memB_prepend (σ : Str) {X : Set Str} (hX : B.mem X) : B.mem (prepend σ X) := by
  obtain ⟨ρ, rfl⟩ := hX
  exact ⟨σ ++ ρ, prepend_cone σ ρ⟩

/-! ### The finite elements `σ⊥` and the initial-segment factoid. -/

/-- **`σ⊥`, a finite element of `|B|`.** The principal filter `↑(σΣ*)` of the cone
of `σ`; its
minimal neighbourhood is `σΔ = σΣ*` (Scott). These are exactly the finite elements
of `|B|`. -/
def sigmaBot (σ : Str) : B.Element := B.principal (memB_cone σ)

/-- **Factoid (Scott 1981, PRG-19).** "`σ₀⊥ ⊆ σ₁⊥` if and only if `σ₀` is an
*initial segment* of
the sequence `σ₁`." The approximation order on finite elements is exactly the
prefix order:
`σ₀⊥ ⊑ σ₁⊥ ↔ σ₀ <+: σ₁`. (Via `principal_le_iff` — reversal — composed with
`cone_subset_cone` —
reversal again — which cancel to give the prefix order directly.)
@isnad1 id=iff.0h2v.s4.546a2339515c from=translated src=- shape=a8e24674 vocab=cb58ad01
-/
theorem sigmaBot_le_iff (σ₀ σ₁ : Str) :
    sigmaBot σ₀ ≤ sigmaBot σ₁ ↔ σ₀ <+: σ₁ := by
  rw [sigmaBot, sigmaBot, B.principal_le_iff, cone_subset_cone]

/-! ### The operation `σx` (Scott's left-multiplication on elements). -/

/-- **Exercise (`σx ∈ |B|`).** For `x ∈ |B|` and `σ ∈ Σ*`, Scott's
`σx = {Y ∣ σX ⊆ Y for some X ∈ x}` is again an element of `|B|`.

The filter laws: `master` uses `X = Δ ∈ x` (`σΔ ⊆ Δ` trivially); `inter` takes `X₁
∩ X₂ ∈ x` and
the consistency witness `σ(X₁∩X₂)`, which is a *cone* (hence in `B`, by
`memB_prepend`) contained in
both `Y₁` and `Y₂`; `up` reuses the same `X`. -/
def sigmaElt (σ : Str) (x : B.Element) : B.Element where
  mem Y := B.mem Y ∧ ∃ X, x.mem X ∧ prepend σ X ⊆ Y
  sub h := h.1
  master_mem := ⟨B.master_mem, B.master, x.master_mem, Set.subset_univ _⟩
  inter_mem := by
    intro Y₁ Y₂ h1 h2
    obtain ⟨hY₁, X₁, hX₁, hsub₁⟩ := h1
    obtain ⟨hY₂, X₂, hX₂, hsub₂⟩ := h2
    have hXinter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁ hX₂
    have hsub : prepend σ (X₁ ∩ X₂) ⊆ Y₁ ∩ Y₂ := by
      rintro w ⟨τ, ⟨hτ₁, hτ₂⟩, rfl⟩
      exact ⟨hsub₁ ⟨τ, hτ₁, rfl⟩, hsub₂ ⟨τ, hτ₂, rfl⟩⟩
    have hZmem : B.mem (prepend σ (X₁ ∩ X₂)) := memB_prepend σ (x.sub hXinter)
    exact ⟨B.inter_mem hY₁ hY₂ hZmem hsub, X₁ ∩ X₂, hXinter, hsub⟩
  up_mem := by
    intro X Y hX hY hXY
    obtain ⟨_, X', hX', hsub'⟩ := hX
    exact ⟨hY, X', hX', hsub'.trans hXY⟩

/-- **`σ⊥` really is `σ` applied to `⊥`.** `sigmaElt σ ⊥ = sigmaBot σ`, justifying
the `σ⊥`
notation: applying `σ` to the least element produces the finite element `↑(σΣ*)`.
@isnad1 id=eq.0h1v.s3.6dad139f5a60 from=translated src=- shape=88fa8707 vocab=738034db
-/
theorem sigmaElt_bot (σ : Str) : sigmaElt σ B.bot = sigmaBot σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [B.mem_bot] at hX
    subst hX
    rw [B_master, prepend_univ] at hsub
    exact ⟨hY, hsub⟩
  · rintro ⟨hY, hcone⟩
    refine ⟨hY, B.master, B.mem_bot.mpr rfl, ?_⟩
    rw [B_master, prepend_univ]
    exact hcone

/-! ### Every element is a union of its finite approximations `σ⊥`. -/

/-- **Factoid (Scott 1981, PRG-19).** "`x = ⋃ₙ σₙ⊥`": every `x ∈ |B|` is the union
of the finite
elements `σ⊥` whose generating cone `σΣ*` lies in `x`. In membership form, a
neighbourhood `Z`
belongs to `x` iff `Z` lies in some `σ⊥ = ↑(σΣ*)` with `σΣ* ∈ x`.

This is the concrete "an element is uniquely determined by its finite
approximations" in `|B|`
(`Basic.eq_iUnion_principal` specialized to `B`, where every neighbourhood is a
cone). The further
arrangement of the `σ` into a single increasing chain `σ₀ prefix σ₁ prefix …` requires
choice/enumeration and
is left to Scott's prose.
@isnad1 id=iff.0h2v.s4.c0f3112c67f3 from=translated src=- shape=2f1f9fb4 vocab=f40134e0
-/
theorem mem_iff_exists_sigmaBot (x : B.Element) {Z : Set Str} :
    x.mem Z ↔ ∃ σ, x.mem (cone σ) ∧ (sigmaBot σ).mem Z := by
  constructor
  · intro hZ
    obtain ⟨σ, rfl⟩ := x.sub hZ
    exact ⟨σ, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨σ, hcone, hZmem, hsub⟩
    exact x.up_mem hcone hZmem hsub

end Domain.Neighborhood.ExampleB
