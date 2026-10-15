/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.ApproximableExercises
public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.ExampleB
public import Tengoku

/-!
# Exercise 2.21 (Scott 1981, PRG-19) — the system `𝒞`, total finite sequences,
juxtaposition

The system `𝔹` of 2.3 has as its total elements only the *infinite* sequences: a
finite prefix `σ`
only ever yields the **partial** element `σ⊥ = ↑(σΣ*)`, which can always be
sharpened by a longer
prefix. We modify `𝔹` to a system `𝒞` having **both** finite and infinite
sequences as total
elements (Scott's hint `𝔹 ⊆ 𝒞`).

The idea: keep the cones `σΣ* = cone σ` of `𝔹` (these give the partial `σ⊥` and,
in the limit, the
infinite total sequences), and add for every finite `σ` a *terminator token* — the
**singleton**
`{σ}`. The neighbourhood `{σ}` asserts "the sequence is exactly `σ` (terminated)".
Because `{σ}` is
a minimal nonempty neighbourhood, `↑{σ}` is a *total* (maximal) element — this is
the total finite
sequence `σ`. We thus distinguish:

* `Λ = ↑{[]}`  — the **total empty sequence** (terminated), and
* `⊥ = ↑Δ = ↑(cone [])` — the **undefined sequence**, with `⊥ ⊏ Λ`.

`𝒞 = {σΣ*} ∪ {{σ}}` is again pairwise nested-or-disjoint (a singleton sits inside
a cone exactly
when its string extends the cone's prefix; two distinct singletons are disjoint),
so it is a
neighbourhood system via `ofNestedOrDisjoint`, and visibly `𝔹 ⊆ 𝒞`.

**Juxtaposition `xy`.** We build `juxtapose : ApproximableMap₂ 𝒞 𝒞 𝒞` realizing
the
left-to-right-biased concatenation:

* if `x` extends the prefix `σ` but is *not known to terminate* (a cone
neighbourhood `σΣ* ∈ x`),
  the result only commits to the prefix `σ` — `xy ⊒ σ⊥`, independent of `y`. Hence
  **for an infinite
  (total) `x`, `xy = x` for all `y`** (`juxtapose_cone`);
* if `x` is the total finite sequence `σ` (the terminator `{σ} ∈ x`), the result
is `σ` followed by
  `y`: `xy` prepends `σ` to `y` (`juxtapose_singleton_mem`).

This is the "strong left-to-right bias" Scott describes: `y` is consulted only
after `x` is known to
have terminated.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise221

open Domain.Neighborhood NeighborhoodSystem ExampleB

/-! ### The neighbourhood system `𝒞`: cones together with terminator singletons. -/

/-- Membership in `𝒞`: `X` is either a cone `σΣ*` (as in `𝔹`) or a terminator
singleton `{σ}`. -/
def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})

/-- A singleton is never a cone (a cone has at least two elements `σ` and `σ0`).
@isnad1 id=not.0h2v.s4.090a3797ae94 from=translated src=- shape=c9ae1b1c vocab=3d017307
-/
theorem cone_not_subset_singleton (σ τ : Str) : ¬ cone σ ⊆ ({τ} : Set Str) := by
  intro h
  have h1 : σ ∈ ({τ} : Set Str) := h (mem_cone.mpr List.prefix_rfl)
  have h2 : (σ ++ [false]) ∈ ({τ} : Set Str) := h (mem_cone.mpr (List.prefix_append σ [false]))
  rw [Set.mem_singleton_iff] at h1 h2
  rw [← h1] at h2
  have hlen := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

/-- Cones and singletons are distinct neighbourhoods.
@isnad1 id=ne.0h2v.s4.553d0be1ae71 from=translated src=- shape=8e64aab0 vocab=4d8cef5c
-/
theorem cone_ne_singleton (σ τ : Str) : cone σ ≠ ({τ} : Set Str) := by
  intro h
  refine cone_not_subset_singleton σ τ ?_
  simp_all

/-- Nested-or-disjoint for a cone vs. a terminator singleton: `{τ} ⊆ σΣ*` iff `σ prefix
τ`, else
disjoint. Choice-free (`σ <+: τ` is decidable).
@isnad1 id=or.0h2v.s5.2a46e872b411 from=translated src=- shape=f0c0862f vocab=b65e31d1
-/
theorem cone_singleton_nd (σ τ : Str) :
    cone σ ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ cone σ ∨ cone σ ∩ ({τ} : Set Str) = ∅ :=
  if h : σ <+: τ then
    Or.inr (Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h)))
  else
    Or.inr (Or.inr (by
      simp_all))

/-- Nested-or-disjoint for a terminator singleton vs. a cone (the mirror of
`cone_singleton_nd`).
@isnad1 id=or.0h2v.s5.90976d44c3a2 from=translated src=- shape=510334e4 vocab=b65e31d1
-/
theorem singleton_cone_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ cone τ ∨ cone τ ⊆ ({σ} : Set Str) ∨ ({σ} : Set Str) ∩ cone τ = ∅ :=
  if h : τ <+: σ then
    Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h))
  else
    Or.inr (Or.inr (by
      simp_all))

/-- Nested-or-disjoint for two terminator singletons: equal or disjoint.
@isnad1 id=or.0h2v.s6.2eb74fa01b9f from=translated src=- shape=c6eeff41 vocab=a0a7a493
-/
theorem singleton_singleton_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ ({σ} : Set Str) ∨
      ({σ} : Set Str) ∩ ({τ} : Set Str) = ∅ := by
  rcases (inferInstance : Decidable (σ = τ)) with h | h
  · simp_all
  · subst h; exact Or.inl subset_rfl

/-- **`𝒞` is pairwise nested-or-disjoint.** Cone/cone is the `𝔹` trichotomy; the
mixed and
singleton/singleton cases are the three lemmas above.
@isnad1 id=nestedor.0h0v.s1.b58b3b147d56 from=translated src=- shape=25b03439 vocab=f4fbad2d
-/
theorem nestedOrDisjoint_C : NestedOrDisjoint memC := by
  rintro X Y hX hY
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩ <;> rcases hY with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · exact cone_trichotomy σ τ
  · exact cone_singleton_nd σ τ
  · exact singleton_cone_nd σ τ
  · exact singleton_singleton_nd σ τ

/-- **The system `𝒞`** on `Δ = Σ*`: cones and terminator singletons. -/
def C : NeighborhoodSystem Str :=
  ofNestedOrDisjoint memC Set.univ (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint_C
    (by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact Set.subset_univ _)

/--
@isnad1 id=iff.0h1v.s3.58777217394b from=translated src=- shape=d213e086 vocab=b012db33
-/
@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl

/--
@isnad1 id=eq.0h0v.s3.91b46e379511 from=translated src=- shape=d672ce25 vocab=fba56ad3
-/
@[simp] theorem C_master : C.master = Set.univ := rfl

/-- Every cone is a neighbourhood of `𝒞` — this is the inclusion `𝔹 ⊆ 𝒞`.
@isnad1 id=mem.0h1v.s2.57d7880e6860 from=translated src=- shape=9bb0b988 vocab=f32c4ec5
-/
theorem memC_cone (σ : Str) : C.mem (cone σ) := Or.inl ⟨σ, rfl⟩

/-- Every terminator singleton `{σ}` is a neighbourhood of `𝒞`.
@isnad1 id=mem.0h1v.s3.f7fc5b0d6cee from=translated src=- shape=4c8e040a vocab=27fcd77f
-/
theorem memC_singleton (σ : Str) : C.mem ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩

/-- **`𝔹 ⊆ 𝒞`.** Every neighbourhood of `𝔹` is a neighbourhood of `𝒞`.
@isnad1 id=mem.1h1v.s3.e251f2bbc89f from=translated src=- shape=c4dd80e1 vocab=17d199ec
-/
theorem memB_imp_memC {X : Set Str} (hX : B.mem X) : C.mem X := by
  obtain ⟨σ, rfl⟩ := hX; exact memC_cone σ

/-- Every neighbourhood of `𝒞` is nonempty (there is no empty token).
@isnad1 id=nonempty.1h1v.s3.9e241adbf6e2 from=translated src=- shape=afedc36f vocab=99966793
-/
theorem memC_nonempty {W : Set Str} (hW : C.mem W) : W.Nonempty := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨σ, mem_cone.mpr List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- A nonempty `𝒞`-neighbourhood contained in a singleton *is* that singleton.
@isnad1 id=eq.2h2v.s5.44935aacb796 from=translated src=- shape=da40ce71 vocab=5f461e80
-/
theorem subset_singleton_eq {W : Set Str} {σ : Str} (hW : C.mem W) (hsub : W ⊆ ({σ} : Set Str)) :
    W = ({σ} : Set Str) := by
  rcases hW with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact absurd hsub (cone_not_subset_singleton ρ σ)
  · simp_all

/-! ### Total elements: finite sequences `↑{σ}`, and `⊥ ⊏ Λ`. -/

/-- The **total finite sequence** `σ` as an element of `|𝒞|`: the principal filter
`↑{σ}`. -/
def singletonElt (σ : Str) : C.Element := C.principal (memC_singleton σ)

/-- `Λ`, the **total empty sequence** (terminated): `↑{[]}`. -/
def Lambda : C.Element := singletonElt []

/-- **Total finite sequences.** `↑{σ}` is a total (maximal) element of `|𝒞|`: any
element above it
must equal it, because `{σ}` is a minimal nonempty neighbourhood. This is what was
*false* in `𝔹`,
where finite sequences gave only the partial `σ⊥`.
@isnad1 id=istotal.0h1v.s2.deaf4cfa4255 from=translated src=- shape=9bb0b988 vocab=c9c38873
-/
theorem isTotal_singletonElt (σ : Str) : C.IsTotal (singletonElt σ) := by
  intro y hy Z hZ
  have hσy : y.mem ({σ} : Set Str) := hy {σ} ⟨memC_singleton σ, subset_rfl⟩
  have hinter : y.mem (({σ} : Set Str) ∩ Z) := y.inter_mem hσy hZ
  have hmemC : C.mem (({σ} : Set Str) ∩ Z) := y.sub hinter
  have heq : ({σ} : Set Str) ∩ Z = ({σ} : Set Str) :=
    subset_singleton_eq hmemC Set.inter_subset_left
  exact ⟨y.sub hZ, by rw [← heq]; exact Set.inter_subset_right⟩

/-- **`⊥ ⊏ Λ`.** The undefined sequence `⊥ = ↑Δ` is strictly below the total empty
sequence
`Λ = ↑{[]}`: they are distinct because `⊥` contains only `Δ`, whereas `Λ` contains
`{[]} ≠ Δ`.
@isnad1 id=lt.0h0v.s4.0c86f6a552fa from=translated src=- shape=020eb140 vocab=7616f98b
-/
theorem bot_lt_Lambda : C.bot < Lambda := by
  refine lt_of_le_of_ne (C.bot_le _) ?_
  intro h
  have hmem : C.bot.mem ({([] : Str)} : Set Str) := by
    rw [h]; exact ⟨memC_singleton [], subset_rfl⟩
  rw [C.mem_bot, C_master] at hmem
  have h2 : ([true] : Str) ∈ ({([] : Str)} : Set Str) := by rw [hmem]; trivial
  rw [Set.mem_singleton_iff] at h2
  exact absurd h2 (by decide)

/-! ### Prepending a string to a `𝒞`-neighbourhood. -/

/-- `σ{ρ} = {σρ}`: prepending `σ` to a terminator singleton.
@isnad1 id=eq.0h2v.s5.8dfb9a708726 from=translated src=- shape=047bd7f0 vocab=f43df283
-/
theorem prepend_singleton (σ ρ : Str) : prepend σ ({ρ} : Set Str) = ({σ ++ ρ} : Set Str) := by
  ext w
  simp_all

/-- Prepending preserves `𝒞`-membership (cone ↦ cone, singleton ↦ singleton).
@isnad1 id=mem.1h2v.s4.879bf88f3f51 from=translated src=- shape=32106f09 vocab=eeb38b74
-/
theorem memC_prepend (σ : Str) {Y : Set Str} (hY : C.mem Y) : C.mem (prepend σ Y) := by
  rcases hY with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · rw [prepend_cone]; exact memC_cone (σ ++ ρ)
  · rw [prepend_singleton]; exact memC_singleton (σ ++ ρ)

/-- `σY ⊆ σΣ* = cone σ`: prepending `σ` always lands inside the cone of `σ`.
@isnad1 id=le.0h2v.s3.9f303c0ad020 from=translated src=- shape=2bc827d7 vocab=c41976bc
-/
theorem prepend_subset_cone (σ : Str) (Y : Set Str) : prepend σ Y ⊆ cone σ := by
  rintro w ⟨τ, _, rfl⟩
  exact mem_cone.mpr (List.prefix_append σ τ)

/-- Prepending is monotone in the suffix set.
@isnad1 id=le.1h3v.s4.9a7177def061 from=translated src=- shape=b83855b6 vocab=aee13793
-/
theorem prepend_mono (σ : Str) {Y Y' : Set Str} (h : Y' ⊆ Y) : prepend σ Y' ⊆ prepend σ Y := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

/-! ### Juxtaposition `xy` as an approximable map of two variables. -/

/-- **Juxtaposition `xy`** as an approximable map `𝒞 × 𝒞 → 𝒞`.

The relation `X, Y j Z` reads off the *left-to-right bias*: if the first input
neighbourhood `X` is
a cone `σΣ*` (`x` extends `σ` but is undetermined), the output only commits to the
prefix `σ`
(`σΣ* ⊆ Z`), ignoring `Y`; if `X` is a terminator `{σ}` (`x` is the total finite
sequence `σ`), the
output prepends `σ` to the second input `Y` (`σY ⊆ Z`). -/
def juxtapose : ApproximableMap₂ C C C where
  rel X Y Z := C.mem Y ∧ C.mem Z ∧
    ((∃ σ, X = cone σ ∧ cone σ ⊆ Z) ∨ (∃ σ, X = ({σ} : Set Str) ∧ prepend σ Y ⊆ Z))
  rel_dom₀ := by
    rintro X Y Z ⟨_, _, (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)⟩
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_dom₁ := fun ⟨hY, _, _⟩ => hY
  rel_cod := fun ⟨_, hZ, _⟩ => hZ
  master_rel := ⟨C.master_mem, C.master_mem,
    Or.inl ⟨[], C_master.trans cone_nil.symm, by rw [C_master]; exact Set.subset_univ _⟩⟩
  inter_right := by
    rintro X Y Z Z' ⟨hY, hZ, hd⟩ ⟨_, hZ', hd'⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hd' with ⟨σ', hX', hsub'⟩ | ⟨σ', hX', _⟩
      · obtain rfl : σ = σ' := cone_injective hX'
        exact ⟨hY, C.inter_mem hZ hZ' (memC_cone σ) (Set.subset_inter hsub hsub'),
          Or.inl ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
      · exact absurd hX' (cone_ne_singleton σ σ')
    · rcases hd' with ⟨σ', hX', _⟩ | ⟨σ', hX', hsub'⟩
      · exact absurd hX'.symm (cone_ne_singleton σ' σ)
      · obtain rfl : σ = σ' := by
          have := hX'; rw [Set.singleton_eq_singleton_iff] at this; exact this
        exact ⟨hY, C.inter_mem hZ hZ' (memC_prepend σ hY) (Set.subset_inter hsub hsub'),
          Or.inr ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hY, _, hd⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hY', hZ', ?_⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hX' with ⟨σ', rfl⟩ | ⟨σ', rfl⟩
      · exact Or.inl ⟨σ', rfl, (hX'X.trans hsub).trans hZZ'⟩
      · refine Or.inr ⟨σ', rfl, ?_⟩
        have hσσ' : σ <+: σ' := mem_cone.mp (Set.singleton_subset_iff.mp hX'X)
        have h2 : cone σ' ⊆ cone σ := cone_subset_cone.mpr hσσ'
        exact ((prepend_subset_cone σ' Y').trans (h2.trans hsub)).trans hZZ'
    · obtain rfl : X' = ({σ} : Set Str) := subset_singleton_eq hX' hX'X
      exact Or.inr ⟨σ, rfl, ((prepend_mono σ hY'Y).trans hsub).trans hZZ'⟩

/-- **Left-to-right bias / "`x` infinite ⟹ `xy = x`".** On a partial input `σ⊥ =
↑(σΣ*)` the
juxtaposition returns `σ⊥` itself, *independently of `y`*. Since an infinite
(total) sequence is the
directed union of its finite approximants `σ⊥`, this says `xy = x` for total
infinite `x`.
@isnad1 id=eq.0h2v.s4.908ff62337fa from=translated src=- shape=13d92056 vocab=b2e09178
-/
theorem juxtapose_cone (σ : Str) (y : C.Element) :
    juxtapose.toElementMap₂ (C.principal (memC_cone σ)) y = C.principal (memC_cone σ) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, ⟨_, hconeX⟩, _, hY, hZ, hd⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, _⟩
    · exact ⟨hZ, hconeX.trans hsub⟩
    · exact absurd hconeX (cone_not_subset_singleton σ ρ)
  · rintro ⟨hZ, hconeσZ⟩
    exact ⟨cone σ, C.master, ⟨memC_cone σ, subset_rfl⟩, y.master_mem, C.master_mem, hZ,
      Or.inl ⟨σ, rfl, hconeσZ⟩⟩

/-- **`σy` for a total finite `x = ↑{σ}`.** When the first argument is the total
finite sequence
`σ`, juxtaposition prepends `σ` to `y`: `Z ∈ (↑{σ})y` iff `Z` contains `σY'` for
some `Y' ∈ y`. The
coarser cone witnesses `σΣ* ∈ ↑{σ}` add nothing, since `σΔ = σΣ*` is itself of the
form `σY'`.
@isnad1 id=iff.0h3v.s5.2270ed34f4a0 from=translated src=- shape=4edabbef vocab=c5416609
-/
theorem juxtapose_singleton_mem (σ : Str) (y : C.Element) {Z : Set Str} :
    (juxtapose.toElementMap₂ (singletonElt σ) y).mem Z ↔
      C.mem Z ∧ ∃ Y', y.mem Y' ∧ prepend σ Y' ⊆ Z := by
  constructor
  · rintro ⟨X, Y, ⟨_, hsingleX⟩, hYmem, _, hZ, hd⟩
    refine ⟨hZ, ?_⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, hsub⟩
    · have hρσ : ρ <+: σ := mem_cone.mp (Set.singleton_subset_iff.mp hsingleX)
      refine ⟨C.master, y.master_mem, ?_⟩
      rw [C_master, prepend_univ]
      exact (cone_subset_cone.mpr hρσ).trans hsub
    · obtain rfl : σ = ρ := by
        simp_all
      exact ⟨Y, hYmem, hsub⟩
  · rintro ⟨hZ, Y', hY'mem, hsub⟩
    exact ⟨{σ}, Y', ⟨memC_singleton σ, subset_rfl⟩, hY'mem, y.sub hY'mem, hZ,
      Or.inr ⟨σ, rfl, hsub⟩⟩

end Domain.Neighborhood.Exercise221
