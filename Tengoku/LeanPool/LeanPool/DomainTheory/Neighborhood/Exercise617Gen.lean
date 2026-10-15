/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Exercise617
public import Tengoku

/-!
# Exercise 6.17 part 2 (Scott 1981, PRG-19) — the generalization `Cₐ ≅ 𝟙 + Σₐ Cₐ`

Example 6.2 / Exercise 6.17 ask for the generalization of `C` corresponding to
Scott's `A ≅ Aⁿ + Aⁿ`:
replace the two-letter alphabet `{0,1}` of `C` (`C ≅ 𝟙 + C + C`) by an arbitrary
alphabet `A`. The
domain `Cₐ` of *finite or infinite `A`-sequences* then satisfies the domain
equation
`Cₐ ≅ 𝟙 + Σ_{a:A} Cₐ` (the `A`-indexed separated sum of copies of `Cₐ`).
Instantiating `A := Fin n`
gives **`Cₙ ≅ 𝟙 + n·Cₙ`**; `A := Bool` recovers Example 6.2's `C`.

This module mirrors, generically over an alphabet `A` with decidable equality, the
binary development
of `Example44` (the domain), `Example62`/`Example62C` (the sum and the
isomorphism) and `Exercise617`
(initiality).

## Stage 1 (this section): the generic domain `Cₐ`

`Strn A = List A`; cones `coneN σ = σA*`; the neighbourhood system `Cn = {σA*} ∪
{{σ}}`; the total
elements `strElemN σ` and partial elements `strBotN σ`; and the successors
`consMapN a : Cₐ → Cₐ`
prepending the letter `a`. Everything is the alphabet-generic copy of `Example44`,
and the data
(`Cn`, `consMapN`) stays choice-free.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise617Gen

open Domain.Neighborhood NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise510

variable {A : Type} [DecidableEq A]

/-- The token type `A*` of finite `A`-strings. -/
abbrev Strn (A : Type) := List A

/-- The cone `σA*`: all extensions of `σ`. -/
def coneN (σ : Strn A) : Set (Strn A) := {w | σ <+: w}

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h3v.s4.5a66b30f3304 from=translated src=- shape=02bfba58 vocab=85b2635f
-/
@[simp] theorem mem_coneN {σ w : Strn A} : w ∈ coneN σ ↔ σ <+: w := Iff.rfl

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h1v.s3.29f76f2ff6c6 from=translated src=- shape=926f3dd5 vocab=3badcf52
-/
theorem coneN_nil : coneN ([] : Strn A) = Set.univ := by ext w; simp [coneN]

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h3v.s4.b09832b3c6ee from=translated src=- shape=c12f32c7 vocab=258a6da3
-/
theorem coneN_subset_coneN {σ τ : Strn A} : coneN σ ⊆ coneN τ ↔ τ <+: σ := by
  constructor
  · intro h; exact h (show σ ∈ coneN σ from List.prefix_rfl)
  · intro hτσ w hw; exact hτσ.trans hw

omit [DecidableEq A] in
/--
@isnad1 id=eq.1h3v.s4.ef6310b0da8d from=translated src=- shape=d33e9c6e vocab=4bc130b8
-/
theorem coneN_injective {σ τ : Strn A} (h : coneN σ = coneN τ) : σ = τ := by
  have h1 : τ <+: σ := coneN_subset_coneN.mp (le_of_eq h)
  have h2 : σ <+: τ := coneN_subset_coneN.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

omit [DecidableEq A] in
/--
@isnad1 id=or.0h3v.s5.94d53caf4153 from=translated src=- shape=a93b7126 vocab=57c678b9
-/
theorem coneN_trichotomy (σ τ : Strn A) :
    coneN σ ⊆ coneN τ ∨ coneN τ ⊆ coneN σ ∨ coneN σ ∩ coneN τ = ∅ := by
  classical
  exact if hστ : σ <+: τ then Or.inr (Or.inl (coneN_subset_coneN.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (coneN_subset_coneN.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_coneN, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in `Cₐ`: a cone `σA*` or a singleton `{σ}`. -/
def memCn (X : Set (Strn A)) : Prop := (∃ σ, X = coneN σ) ∨ (∃ σ, X = {σ})

omit [DecidableEq A] in
/--
@isnad1 id=memcn.0h2v.s3.415d7b384749 from=translated src=- shape=41820d97 vocab=711485c4
-/
theorem memCn_coneN (σ : Strn A) : memCn (coneN σ) := Or.inl ⟨σ, rfl⟩

omit [DecidableEq A] in
/--
@isnad1 id=memcn.0h2v.s4.4dcb7ffc3787 from=translated src=- shape=6ec794f0 vocab=f7125ebb
-/
theorem memCn_singleton (σ : Strn A) : memCn ({σ} : Set (Strn A)) := Or.inr ⟨σ, rfl⟩

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h3v.s5.a13ad83d348c from=translated src=- shape=94394170 vocab=e4547611
-/
theorem singleton_subset_coneN {σ τ : Strn A} : ({τ} : Set (Strn A)) ⊆ coneN σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_coneN]

omit [DecidableEq A] in
/--
@isnad1 id=or.0h3v.s6.ea1587721dec from=translated src=- shape=7d3dd4b4 vocab=d35e7896
-/
theorem singleton_coneN_nd (σ τ : Strn A) :
    ({τ} : Set (Strn A)) ⊆ coneN σ ∨ coneN σ ⊆ {τ} ∨ ({τ} : Set (Strn A)) ∩ coneN σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_coneN.mpr h)
  · simp_all

omit [DecidableEq A] in
/--
@isnad1 id=nestedor.0h1v.s2.b23f87a09dda from=translated src=- shape=28ebabf1 vocab=812c4278
-/
theorem nestedOrDisjointN : NestedOrDisjoint (memCn (A := A)) := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact coneN_trichotomy σ τ
  · rcases singleton_coneN_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_coneN_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · simp_all

/-- **The generic domain `Cₐ`** of finite-or-infinite `A`-sequences. -/
def Cn (A : Type) : NeighborhoodSystem (Strn A) :=
  NeighborhoodSystem.ofNestedOrDisjoint memCn Set.univ (Or.inl ⟨[],
    coneN_nil.symm⟩) nestedOrDisjointN
    (fun _ => Set.subset_univ _)

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h2v.s4.6c872f825f22 from=translated src=- shape=afadf761 vocab=5f1962f3
-/
@[simp] theorem Cn_mem {X : Set (Strn A)} : (Cn A).mem X ↔ memCn X := Iff.rfl

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h1v.s3.c43602944a59 from=translated src=- shape=687b3bbd vocab=3137d7a9
-/
@[simp] theorem Cn_master : (Cn A).master = (Set.univ : Set (Strn A)) := rfl

omit [DecidableEq A] in
/-- `Cₐ` is `∅`-free: every neighbourhood is non-empty (cones and singletons are
inhabited).
@isnad1 id=nonempty.1h2v.s4.be626b5fe4ce from=translated src=- shape=b4b2d588 vocab=4072f847
-/
theorem Cn_nonempty : ∀ X, (Cn A).mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- The partial element `σ⊥ = ↑σA*`. -/
def strBotN (σ : Strn A) : (Cn A).Element := (Cn A).principal (memCn_coneN σ)

/-- The total element `σ = ↑{σ}`. -/
def strElemN (σ : Strn A) : (Cn A).Element := (Cn A).principal (memCn_singleton σ)

/-! ### Prepending a letter: the successors `x ↦ a·x`. -/

/-- `σX = {στ ∣ τ ∈ X}`. -/
def prependN (σ : Strn A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h4v.s5.805894eeb6d5 from=translated src=- shape=9eed1517 vocab=72919d19
-/
@[simp] theorem mem_prependN {σ : Strn A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ prependN σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h3v.s5.4cb4217a1f15 from=translated src=- shape=14451b0c vocab=ed4f9549
-/
theorem prependN_coneN (σ ρ : Strn A) : prependN σ (coneN ρ) = coneN (σ ++ ρ) := by
  ext w
  simp only [mem_prependN, mem_coneN]
  constructor
  · rintro ⟨τ, hτ, rfl⟩; exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h3v.s5.2963866d3240 from=translated src=- shape=7c0cff93 vocab=e5d815ad
-/
theorem prependN_singleton (σ τ : Strn A) : prependN σ {τ} = {σ ++ τ} := by
  ext w
  simp_all

omit [DecidableEq A] in
/--
@isnad1 id=le.1h4v.s5.32fd695976f9 from=translated src=- shape=207ac3c4 vocab=f1bc40a3
-/
theorem prependN_mono (σ : Strn A) {X X' : Set (Strn A)} (h : X' ⊆ X) :
    prependN σ X' ⊆ prependN σ X := by
  rintro w ⟨τ, hτ, rfl⟩; exact ⟨τ, h hτ, rfl⟩

omit [DecidableEq A] in
/--
@isnad1 id=memcn.1h3v.s4.49c9dc5017d9 from=translated src=- shape=f18a6a89 vocab=594a7dd6
-/
theorem memCn_prependN (σ : Strn A) {X : Set (Strn A)} (hX : memCn X) : memCn (prependN σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prependN_coneN σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prependN_singleton σ ρ⟩

/-- **The successor `x ↦ a·x`** prepending the letter `a`: `X (a·x) Y ↔ aX ⊆ Y`. -/
def consMapN (a : A) : ApproximableMap (Cn A) (Cn A) where
  rel X Y := memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Or.inl ⟨[], coneN_nil.symm⟩, Or.inl ⟨[], coneN_nil.symm⟩,
    fun _ _ => trivial⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    have hsubInter : prependN [a] X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hZ : memCn (prependN [a] X) := memCn_prependN [a] hX
    exact ⟨hX, (Cn A).inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prependN_mono [a] hX'X).trans (hXY.trans hYY')⟩

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h4v.s5.ed25c8328616 from=translated src=- shape=ef92a4b2 vocab=6562dc38
-/
@[simp] theorem consMapN_rel {a : A} {X Y : Set (Strn A)} :
    (consMapN a).rel X Y ↔ memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y := Iff.rfl

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h3v.s5.91187044e02a from=translated src=- shape=48c0e48e vocab=63e1ecc7
-/
theorem consMapN_strBot (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strBotN σ) = strBotN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXcone⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc coneN (a :: σ) = prependN [a] (coneN σ) := by rw [prependN_coneN]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXcone
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, memCn_coneN σ, hY, ?_⟩
    rw [show prependN [a] (coneN σ) = coneN (a :: σ) by rw [prependN_coneN]; rfl]
    exact hsub

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h3v.s5.a0a7fa6bb3a3 from=translated src=- shape=48c0e48e vocab=eea3e9ff
-/
theorem consMapN_strElem (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strElemN σ) = strElemN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXsing⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc ({a :: σ} : Set (Strn A)) = prependN [a] {σ} := by rw [prependN_singleton]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXsing
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, memCn_singleton σ, hY, ?_⟩
    rw [show prependN [a] ({σ} : Set (Strn A)) = {a :: σ} by rw [prependN_singleton]; rfl]
    exact hsub

/-! ## Stage 2: the `A`-indexed separated sum `Tsig(X) = 𝟙 + Σ_{a:A} X`

The right-hand side of the generalized domain equation. Tokens are `Option (Unit ⊕
(A × β))`: a
fresh basepoint `Λ = none`, the lone `𝟙`-token `tu = some (inl ())`, and the
`A`-indexed family of
tagged copies `tc a t = some (inr (a, t))`. This is the alphabet-generic analogue
of `Example62C`'s
three-way `sum3 unitSys C C` (`= 𝟙 + C + C`), the index `Bool` being replaced by
`A`. -/

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- Tokens of the indexed sum `𝟙 + Σ_a β`. -/
abbrev SigTok (A : Type) (β : Type v) := Option (Unit ⊕ (A × β))

/-- The lone `𝟙`-token. -/
def tu : SigTok A β := some (Sum.inl ())

/-- The token `t` in the `a`-indexed copy. -/
def tc (a : A) (t : β) : SigTok A β := some (Sum.inr (a, t))

/-- The `𝟙`-copy neighbourhood (the image of `univ : Set Unit`). -/
def jU : Set (SigTok A β) := {tu}

/-- The `a`-indexed tagged copy `aX`. -/
def jc (a : A) (X : Set β) : Set (SigTok A β) := {w | ∃ t, w = tc a t ∧ t ∈ X}

omit [DecidableEq A] in
/--
@isnad1 id=and.1h6v.s5.2bc1935467d2 from=translated src=- shape=f556bd9b vocab=5e0b49f4
-/
theorem tc_injective {a a' : A} {t t' : β} (h : (tc a t : SigTok A β) = tc a' t') :
    a = a' ∧ t = t' := by
  simp only [tc, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h; exact h

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h5v.s5.50e3dd4845be from=translated src=- shape=c3aafcd2 vocab=2b33851d
-/
@[simp] theorem tc_mem_jc {a : A} {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∈ jc a X ↔ t ∈ X := by
  constructor
  · rintro ⟨t', heq, ht'⟩; obtain ⟨-, rfl⟩ := tc_injective heq; exact ht'
  · intro ht; exact ⟨t, rfl, ht⟩

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h3v.s5.af3fef216c50 from=translated src=- shape=3b4496cc vocab=c59797ff
-/
@[simp] theorem mem_jU {w : SigTok A β} : w ∈ (jU : Set (SigTok A β)) ↔ w = tu := Iff.rfl

omit [DecidableEq A] in
/--
@isnad1 id=not.0h2v.s4.ec2bff4f43e4 from=translated src=- shape=b7d6de96 vocab=6ae8a4fe
-/
theorem none_not_mem_jU : (none : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu]

omit [DecidableEq A] in
/--
@isnad1 id=not.0h4v.s5.23daf3263215 from=translated src=- shape=3607ae95 vocab=7a39ae78
-/
@[simp] theorem none_not_mem_jc {a : A} {X : Set β} : (none : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tc])

omit [DecidableEq A] in
/--
@isnad1 id=not.0h4v.s4.b93236bb946c from=translated src=- shape=22e9cb4c vocab=c098c075
-/
@[simp] theorem tu_not_mem_jc {a : A} {X : Set β} : (tu : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tu, tc])

omit [DecidableEq A] in
/--
@isnad1 id=not.0h4v.s4.d719ce305f97 from=translated src=- shape=ce4fca6e vocab=17f2a117
-/
theorem tc_not_mem_jU {a : A} {t : β} :
    (tc a t : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu, tc]

omit [DecidableEq A] in
/--
@isnad1 id=not.1h6v.s5.baa2e387ba23 from=translated src=- shape=5c457bae vocab=2b33851d
-/
theorem tc_mem_jc_ne {a a' : A} (h : a ≠ a') {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∉ jc a' X := by
  rintro ⟨t', heq, -⟩; exact h (tc_injective heq).1

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h5v.s5.28e84748ec8f from=translated src=- shape=7e23e7c2 vocab=687be0af
-/
theorem jc_inter_jc_same (a : A) (X X' : Set β) :
    (jc a X ∩ jc a X' : Set (SigTok A β)) = jc a (X ∩ X') := by
  ext w
  constructor
  · rintro ⟨⟨t, rfl, ht⟩, ⟨t', heq, ht'⟩⟩
    obtain ⟨-, rfl⟩ := tc_injective heq; exact ⟨t, rfl, ht, ht'⟩
  · rintro ⟨t, rfl, ht, ht'⟩; exact ⟨⟨t, rfl, ht⟩, ⟨t, rfl, ht'⟩⟩

omit [DecidableEq A] in
/--
@isnad1 id=eq.1h6v.s5.cc2f844e1c63 from=translated src=- shape=1a4eb7b9 vocab=379c3bfa
-/
theorem jc_inter_jc_ne {a a' : A} (h : a ≠ a') (X X' : Set β) :
    (jc a X ∩ jc a' X' : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨t, rfl, -⟩ ⟨t', heq, -⟩
  exact h (tc_injective heq).1

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h4v.s5.69cfda1c172c from=translated src=- shape=95dc0201 vocab=279e21a9
-/
theorem jU_inter_jc (a : A) (X : Set β) : (jU ∩ jc a X : Set (SigTok A β)) = ∅ := by
  ext w
  simp_all

omit [DecidableEq A] in
/--
@isnad1 id=nonempty.0h2v.s3.33c2bc96cc31 from=translated src=- shape=f8727182 vocab=e96a364d
-/
theorem jU_nonempty : (jU : Set (SigTok A β)).Nonempty := ⟨tu, rfl⟩

omit [DecidableEq A] in
/--
@isnad1 id=nonempty.1h4v.s4.d17c67a75309 from=translated src=- shape=81c5631d vocab=583f8188
-/
theorem jc_nonempty {a : A} {X : Set β} (hX : X.Nonempty) :
  (jc a X : Set (SigTok A β)).Nonempty := by
  obtain ⟨t, ht⟩ := hX; exact ⟨tc a t, t, rfl, ht⟩

omit [DecidableEq A] in
/--
@isnad1 id=iff.0h5v.s5.a165772aff41 from=translated src=- shape=a6bf970f vocab=095cb78c
-/
theorem jc_subset_jc {a : A} {X X' : Set β} :
    (jc a X : Set (SigTok A β)) ⊆ jc a X' ↔ X ⊆ X' := by
  constructor
  · intro h t ht; exact tc_mem_jc.mp (h (tc_mem_jc.mpr ht))
  · rintro h w ⟨t, rfl, ht⟩; exact tc_mem_jc.mpr (h ht)

omit [DecidableEq A] in
/--
@isnad1 id=eq.1h5v.s5.5ab81ca3c9b7 from=translated src=- shape=b596dd22 vocab=cbada739
-/
theorem jc_injective {a : A} {X X' : Set β} (h : (jc a X : Set (SigTok A β)) = jc a X') : X = X' :=
  Set.Subset.antisymm (jc_subset_jc.mp h.subset) (jc_subset_jc.mp h.symm.subset)

omit [DecidableEq A] in
/-- Tagged copies determine both index and set: `aX = a'X'` (with `X` non-empty)
forces `a=a'`,
`X=X'`.
@isnad1 id=and.2h6v.s5.a87dea411391 from=translated src=- shape=f7fb1764 vocab=583f8188
-/
theorem jc_eq_jc {a a' : A} {X X' : Set β} (hXne : X.Nonempty)
    (heq : (jc a X : Set (SigTok A β)) = jc a' X') : a = a' ∧ X = X' := by
  obtain ⟨t, ht⟩ := hXne
  obtain ⟨t', he, -⟩ := heq ▸ (tc_mem_jc.mpr ht)
  obtain ⟨rfl, -⟩ := tc_injective he
  exact ⟨rfl, jc_injective heq⟩

variable (V : NeighborhoodSystem β)

/-- The master neighbourhood `{Λ} ∪ {tu} ∪ ⋃_a aΔ`. -/
def masterSig : Set (SigTok A β) :=
  {w | w = none ∨ w = tu ∨ ∃ a t, t ∈ V.master ∧ w = tc a t}

variable {V}

omit [DecidableEq A] in
/--
@isnad1 id=mem.0h3v.s5.f4807b047d23 from=translated src=- shape=d26fbd7a vocab=a964287a
-/
@[simp] theorem none_mem_masterSig : (none : SigTok A β) ∈ masterSig V := Or.inl rfl

omit [DecidableEq A] in
/--
@isnad1 id=mem.0h3v.s4.f3c872090b35 from=translated src=- shape=bc019318 vocab=7fc41af0
-/
@[simp] theorem tu_mem_masterSig : (tu : SigTok A β) ∈ masterSig V := Or.inr (Or.inl rfl)

omit [DecidableEq A] in
/--
@isnad1 id=le.0h3v.s4.0d64cdc8e4bf from=translated src=- shape=863d8b14 vocab=45ab229f
-/
theorem jU_subset_masterSig : (jU : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w rfl; exact tu_mem_masterSig

omit [DecidableEq A] in
/--
@isnad1 id=le.1h5v.s5.c709c1f69546 from=translated src=- shape=d3abe9bf vocab=6301c902
-/
theorem jc_subset_masterSig {a : A} {X : Set β} (hX : V.mem X) :
    (jc a X : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w ⟨t, rfl, ht⟩; exact Or.inr (Or.inr ⟨a, t, V.sub_master hX ht, rfl⟩)

omit [DecidableEq A] in
/--
@isnad1 id=eq.0h3v.s4.8d8f1a5c178b from=translated src=- shape=5306fe70 vocab=f52be031
-/
theorem masterSig_inter_jU : (masterSig V ∩ jU : Set (SigTok A β)) = jU :=
  Set.inter_eq_right.mpr jU_subset_masterSig

omit [DecidableEq A] in
/--
@isnad1 id=eq.1h5v.s5.1a01e3c8689a from=translated src=- shape=f7189a0a vocab=79565352
-/
theorem masterSig_inter_jc {a : A} {X : Set β} (hX : V.mem X) :
    (masterSig V ∩ jc a X : Set (SigTok A β)) = jc a X :=
  Set.inter_eq_right.mpr (jc_subset_masterSig hX)

omit [DecidableEq A] in
theorem eq_masterSig_of_subset {W : Set (SigTok A β)}
    (hsub : masterSig V ⊆ W) (hsub' : W ⊆ masterSig V) : W = masterSig V :=
  Set.Subset.antisymm hsub' hsub

/-- **The `A`-indexed separated sum `𝟙 + Σ_a V`** over `{Λ} ∪ {tu} ∪ ⋃_a aΔ`,
under the standing
assumption that no neighbourhood of `V` is empty. The alphabet-generic analogue of
`sum3 unitSys V V`
(Example 6.2). -/
def sumSig (A : Type) [DecidableEq A] (V : NeighborhoodSystem β)
    (h : ∀ X, V.mem X → X.Nonempty) :
    NeighborhoodSystem (SigTok A β) where
  mem W := W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X
  master := masterSig V
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
    · exact subset_rfl
    · exact jU_subset_masterSig
    · exact jc_subset_masterSig hX
  inter_mem := by
    have hne : ∀ W, (W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X) →
        (W : Set (SigTok A β)).Nonempty := by
      rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
      · exact ⟨none, none_mem_masterSig⟩
      · exact jU_nonempty
      · exact jc_nonempty (h X hX)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [masterSig_inter_jc hX']; exact Or.inr (Or.inr ⟨a', X', hX', rfl⟩)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [Set.inter_self]; exact Or.inr (Or.inl rfl)
      · rw [jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jc hX]; exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
      · rw [Set.inter_comm, jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · by_cases haa : a = a'
        · subst haa
          rw [jc_inter_jc_same] at hZsub ⊢
          rcases hZ with rfl | rfl | ⟨a₂, Z₂, hZ₂, rfl⟩
          · exact absurd (hZsub none_mem_masterSig) (by simp)
          · exact absurd (hZsub (show tu ∈ jU from rfl)) tu_not_mem_jc
          · by_cases ha₂ : a = a₂
            · subst ha₂
              exact Or.inr (Or.inr ⟨a, X ∩ X', V.inter_mem hX hX' hZ₂ (jc_subset_jc.mp hZsub), rfl⟩)
            · obtain ⟨t, ht⟩ := h Z₂ hZ₂
              exact absurd (hZsub (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm ha₂))
        · rw [jc_inter_jc_ne haa] at hZsub ⊢
          obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)

/--
@isnad1 id=eq.1h3v.s5.4473263ea4ae from=translated src=- shape=0f4f8af2 vocab=642417e5
-/
@[simp] theorem sumSig_master {h : ∀ X, V.mem X → X.Nonempty} :
    (sumSig A V h).master = masterSig V := rfl

/--
@isnad1 id=nonempty.2h4v.s5.9f1390587340 from=translated src=- shape=71e2f5c5 vocab=b00b1990
-/
theorem sumSig_nonempty {h : ∀ X, V.mem X → X.Nonempty} :
    ∀ W, (sumSig A V h).mem W → W.Nonempty := by
  rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
  · exact ⟨none, none_mem_masterSig⟩
  · exact jU_nonempty
  · exact jc_nonempty (h X hX)

/-! ### Shape lemmas: no nesting through the wrong tag. -/

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- A `sumSig`-neighbourhood contained in an `a`-copy `aX` is itself an `a`-copy.
@isnad1 id=ex.3h6v.s6.af726d36d952 from=translated src=- shape=034efdb3 vocab=f8b454b6
-/
theorem mem_subset_jc_inv {W : Set (SigTok A β)} {a : A} {X : Set β}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jc a X) : ∃ X₂, V.mem X₂ ∧ W = jc a X₂ := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jc
  · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
    obtain ⟨rfl, -⟩ := tc_injective heq
    exact ⟨X₂, hX₂, rfl⟩

/-- A `sumSig`-neighbourhood contained in the `𝟙`-copy `jU` is `jU`.
@isnad1 id=eq.3h4v.s5.1d29805161c8 from=translated src=- shape=2273cb81 vocab=77175b99
-/
theorem mem_subset_jU_inv {W : Set (SigTok A β)}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jU) : W = jU := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jU
  · rfl
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU

/-! ### The canonical injections `𝟙 ↪ 𝟙+Σ_a V` and `V ↪ 𝟙+Σ_a V` (the `a`-th
copy). -/

/-- The basepoint/`𝟙`-injection: the image of the unique point of `𝟙`. Its proper
neighbourhood is
the `𝟙`-copy `jU`. -/
def sinjU : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ W = jU
  sub := by
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | rfl) (rfl | rfl)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (by rw [masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_comm, masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_self])
  up_mem := by
    rintro W W' (rfl | rfl) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc

/-- The `a`-th copy injection `V ↪ 𝟙+Σ_a V`: send `x∈|V|` to the sum element whose
proper
neighbourhoods are the `a`-copies `aX` with `X∈x`. -/
def sinjC (a : A) (x : V.Element) : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ ∃ X, V.mem X ∧ W = jc a X ∧ x.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [masterSig_inter_jc hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x.sub (x.inter_mem hx hx'), jc_inter_jc_same a X X', x.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective heq
        exact Or.inr ⟨X', hX', rfl, x.up_mem hx hX' (jc_subset_jc.mp hsub)⟩

/--
@isnad1 id=mem.1h3v.s5.d7fec7eca36c from=translated src=- shape=5ac42154 vocab=885e3129
-/
@[simp] theorem sinjU_mem_jU : (sinjU (h := h)).mem (jU : Set (SigTok A β)) := Or.inr rfl

/--
@isnad1 id=iff.2h6v.s6.811a5d777b17 from=translated src=- shape=a994077b vocab=b0a625d0
-/
@[simp] theorem sinjC_mem_jc {a : A} {x : V.Element} {X : Set β} (hX : V.mem X) :
    (sinjC (h := h) a x).mem (jc a X) ↔ x.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · rw [jc_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

/--
@isnad1 id=le.2h6v.s6.166a5e509ecd from=translated src=- shape=8b2b0649 vocab=ee9aac9e
-/
theorem sinjC_mono {a : A} {x x' : V.Element} (hxle : x ≤ x') :
    sinjC (h := h) a x ≤ sinjC a x' := by
  rintro W (rfl | ⟨X, hX, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, hX, rfl, hxle X hm⟩

end SumSig

/-! ### The sum map `Σ f = I_𝟙 + Σ_a f` and its functoriality. -/

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **The indexed sum map `Σf = I_𝟙 + Σ_a f`** acting as the identity on the
`𝟙`-summand and as `f`
on each `a`-copy. The generic analogue of `sumMap3 (idMap unitSys) f f`. -/
def sumMapSig (f : ApproximableMap V₀ V₁) :
    ApproximableMap (sumSig A V₀ h₀) (sumSig A V₁ h₁) where
  rel W W' := (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
    (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
      ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y')
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨(sumSig A V₀ h₀).master_mem, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (SigTok A β₁),
        (W'' = masterSig V₁ ∨ (W = jU ∧ W'' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W'' = jc a Y' ∧ f.rel X Y') → (sumSig A V₁ h₁).mem W'' := by
      rintro W'' (rfl | ⟨-, rfl⟩ | ⟨a, X, Y', -, rfl, hf⟩)
      · exact (sumSig A V₁ h₁).master_mem
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩)
    have key : (W'₁ ∩ W'₂ = masterSig V₁ ∨ (W = jU ∧ W'₁ ∩ W'₂ = jU) ∨
        ∃ a X Y', W = jc a X ∧ W'₁ ∩ W'₂ = jc a Y' ∧ f.rel X Y') := by
      rcases hd₁ with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Y'₁, hWX, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ masterSig V₁ from
          (sumSig A V₁ h₁).sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hWX, rfl, hf⟩
        · rw [Set.inter_eq_left.mpr jU_subset_masterSig]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · rw [Set.inter_self]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf)
          exact absurd ((hWX.symm.trans hWU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · rcases hd₂ with rfl | ⟨hWU2, rfl⟩ | ⟨a', X', Y'₂, hWX', rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (jc_subset_masterSig (f.rel_cod hf₁))]
          exact Or.inr (Or.inr ⟨a, X, Y'₁, hWX, rfl, hf₁⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf₁)
          exact absurd ((hWX.symm.trans hWU2) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
        · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X (f.rel_dom hf₁)) (hWX.symm.trans hWX')
          rw [jc_inter_jc_same]
          exact Or.inr (Or.inr ⟨a, X, Y'₁ ∩ Y'₂, hWX, rfl, f.inter_right hf₁ hf₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_masterSig_of_subset hW'W'₂ ((sumSig A V₁ h₁).sub_master hW'₂mem))
    · have hW₂jU : W₂ = jU := mem_subset_jU_inv hW₂mem hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hW₂jU, rfl⟩)
      · exact absurd (hW'W'₂ (show tu ∈ jU from rfl)) tu_not_mem_jc
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_jc_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := jc_subset_jc.mp hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        exact absurd (hW'W'₂ (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        obtain ⟨t', he, -⟩ := hW'W'₂ (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X₂, Y'₂, rfl, rfl,
          f.mono hf hX₂X (jc_subset_jc.mp hW'W'₂) hX₂ hY'₂⟩)

/-- The sum map is strict: it sends `⊥ = master` only to `master`.
@isnad1 id=isstrict.2h6v.s6.c4a85b794a34 from=translated src=- shape=68f457c6 vocab=ab01b977
-/
theorem isStrict_sumMapSig (f : ApproximableMap V₀ V₁) :
    IsStrict (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  rintro W' ⟨-, -, hd⟩
  rcases hd with rfl | ⟨hWU, -⟩ | ⟨a, X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWU ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jU
  · exact absurd (hWX ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jc

/--
@isnad1 id=iff.2h8v.s7.8ef816a35dd8 from=translated src=- shape=e4011e7f vocab=10bfa2cf
-/
@[simp] theorem sumMapSig_rel {f : ApproximableMap V₀ V₁} {W W'} :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).rel W W' ↔
      (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
        (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y') := Iff.rfl

/-- `Σf` fixes the basepoint injection.
@isnad1 id=eq.2h6v.s6.12b7a1027c9f from=translated src=- shape=7805a054 vocab=48a3c946
-/
theorem sumMapSig_sinjU (f : ApproximableMap V₀ V₁) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjU (h := h₀))
      = sinjU (h := h₁) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hU with hUm | rfl
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · exact absurd (hUj ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · rintro (rfl | rfl)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · exact ⟨jU, Or.inr rfl, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
        Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- `Σf` on the `a`-copy injection: `(Σf)(inj_a x) = inj_a (f x)`.
@isnad1 id=eq.2h8v.s6.e8b4a6dd8d2b from=translated src=- shape=5863e467 vocab=a1604593
-/
theorem sumMapSig_sinjC (f : ApproximableMap V₀ V₁) (a : A) (x : V₀.Element) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjC (h := h₀) a x)
      = sinjC (h := h₁) a (f.toElementMap x) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨hUjU, rfl⟩ | ⟨a', X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUjU) ▸ none_mem_masterSig) none_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X₀ hX₀
        exact absurd ((hUeq.symm.trans hUjU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X₀ hX₀) (hUeq.symm.trans hUj)
        exact Or.inr ⟨Y', f.rel_cod hf, rfl, ⟨X₀, hx, hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨jc a X, Or.inr ⟨X, x.sub hx, rfl, hx⟩, Or.inr (Or.inr ⟨a, X, x.sub hx, rfl⟩),
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩

/-- **Functoriality (identities): `Σ(I) = I`.**
@isnad1 id=eq.1h3v.s6.e1905a6ec2ed from=translated src=- shape=6d0fe12f vocab=4a5cf80a
-/
theorem sumMapSig_id :
    sumMapSig (A := A) (V₀ := V₀) (V₁ := V₀) (h₀ := h₀) (h₁ := h₀) (idMap V₀)
      = idMap (sumSig A V₀ h₀) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, -, -, hXY⟩
    · exact (sumSig A V₀ h₀).sub_master hW
    · exact subset_rfl
    · exact jc_subset_jc.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V₀ h₀).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₀ X hX; exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X, X', rfl, rfl, hX, hX', jc_subset_jc.mp hsub⟩)

/-- **Functoriality (composition): `Σ(g∘f) = Σg ∘ Σf`.**
@isnad1 id=eq.3h9v.s7.d9bace4911d9 from=translated src=- shape=ff0f8871 vocab=bb094638
-/
theorem sumMapSig_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    sumMapSig (A := A) (h₀ := h₀) (h₁ := h₂) (g.comp f)
      = (sumMapSig (A := A) (h₀ := h₁) (h₁ := h₂) g).comp
          (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨masterSig V₁, ⟨hW, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩,
        (sumSig A V₁ h₁).master_mem, hW'', Or.inl rfl⟩
    · exact ⟨jU, ⟨hW, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨hWU, rfl⟩)⟩,
        Or.inr (Or.inl rfl), hW'', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨jc a Y', ⟨hW, Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩),
        Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), hW'',
        Or.inr (Or.inr ⟨a, Y', Z'', rfl, rfl, hg⟩)⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, -, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨hW'U, rfl⟩ | ⟨a, Y', Z'', hW'Y', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨hWU, -⟩ | ⟨a, X, Y'₀, -, hW'eq, hf⟩
      · exact absurd ((hW'U.symm) ▸ none_mem_masterSig) none_not_mem_jU
      · exact Or.inr (Or.inl ⟨hWU, rfl⟩)
      · obtain ⟨t, ht⟩ := h₁ Y'₀ (f.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'U) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hdf with rfl | ⟨-, hW'U⟩ | ⟨a', X, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨t, ht⟩ := h₁ Y' (g.rel_dom hg)
        exact absurd ((hW'U.symm.trans hW'Y') ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₁ Y'₀ (f.rel_cod hf)) (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr ⟨a', X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)

end SumMapSig

/-! ## The endofunctor `Tsig(X) = 𝟙 + Σ_a X` on the `∅`-free category. -/

/-- `Tsig` on objects: `Tsig(D) = 𝟙 + Σ_a D`, again `∅`-free (`sumSig_nonempty`). -/
def tsigObj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) : StrictDomainObj.{0} where
  carrier := SigTok A D.carrier
  sys := sumSig A D.sys D.nonempty
  nonempty := sumSig_nonempty
attribute [local implicit_reducible] tsigObj

/--
@isnad1 id=eq.0h2v.s4.bfdcf99d37f1 from=translated src=- shape=44d35f1c vocab=64f3c96d
-/
@[simp] theorem tsigObj_sys (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (tsigObj A D).sys = sumSig A D.sys D.nonempty := rfl

/-- `Tsig` on maps: `Tsig(f) = I_𝟙 + Σ_a f`, strict by `isStrict_sumMapSig`. -/
def tsigMapHom (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}} (f : Category.Hom D E) :
    Category.Hom (tsigObj A D) (tsigObj A E) :=
  ⟨sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1, isStrict_sumMapSig _⟩

/--
@isnad1 id=eq.0h4v.s7.9607fd2278aa from=translated src=- shape=49c480d3 vocab=c31707d0
-/
@[simp] theorem tsigMapHom_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : Category.Hom D E) :
    (tsigMapHom A f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl

/-- **The functor `Tsig(X) = 𝟙 + Σ_{a:A} X`** on the category of `∅`-free domains
and strict
maps. -/
def Tsig (A : Type) [DecidableEq A] : Endofunctor StrictDomainObj.{0} where
  obj := tsigObj A
  map := tsigMapHom A
  map_id _D := Subtype.ext sumMapSig_id
  map_comp {_D _E _F} g f := Subtype.ext (sumMapSig_comp g.1 f.1)
attribute [local implicit_reducible] Tsig

/--
@isnad1 id=eq.0h2v.s4.486d73b97162 from=translated src=- shape=2119f8af vocab=e73310b1
-/
@[simp] theorem Tsig_obj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (Tsig A).obj D = tsigObj A D := rfl

/--
@isnad1 id=eq.0h4v.s7.db378a093497 from=translated src=- shape=105b54d1 vocab=aca21833
-/
@[simp] theorem Tsig_map_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : Category.Hom D E) :
    ((Tsig A).map f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl

/-! ## Stage 3: the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.

The alphabet-generic analogue of `Example62C` (`C ≅ 𝟙 + C + C`). Prepending the
letter `a` to a
neighbourhood gives `embA a X`; a `Cₐ`-neighbourhood is the master, the terminator
`{Λ}`, or some
`a`-copy `aX`, exactly the shapes of the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `aX = {a :: w' ∣ w' ∈ X}`: the `a`-prefixed copy of a neighbourhood. -/
def embA (a : A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ w', w = a :: w' ∧ w' ∈ X}

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=iff.0h4v.s5.3c6dc0e75f0e from=translated src=- shape=eb158d4f vocab=1f81de4f
-/
@[simp] theorem mem_embA {a : A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ embA a X ↔ ∃ w', w = a :: w' ∧ w' ∈ X := Iff.rfl

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.0h3v.s4.096aa6fd76a1 from=translated src=- shape=273985a6 vocab=cec064f2
-/
theorem embA_eq_prependN (a : A) (X : Set (Strn A)) : embA a X = prependN [a] X := by
  ext w
  simp only [mem_embA, mem_prependN]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨t, hX, rfl⟩; exact ⟨t, rfl, hX⟩

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.0h3v.s4.8f30a6a4efe3 from=translated src=- shape=4139143c vocab=20cb2cc4
-/
theorem embA_coneN (a : A) (σ : Strn A) : embA a (coneN σ) = coneN (a :: σ) := by
  rw [embA_eq_prependN, prependN_coneN]; rfl

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.0h3v.s5.bc7b92fd9217 from=translated src=- shape=3fc0ce9c vocab=31dc7d4c
-/
theorem embA_singleton (a : A) (σ : Strn A) : embA a ({σ} : Set (Strn A)) = {a :: σ} := by
  rw [embA_eq_prependN, prependN_singleton]; rfl

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=memcn.1h3v.s4.fa39878fdeca from=translated src=- shape=244c5e93 vocab=58dea02d
-/
theorem memCn_embA (a : A) {X : Set (Strn A)} (hX : memCn X) : memCn (embA a X) := by
  rw [embA_eq_prependN]; exact memCn_prependN [a] hX

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=not.0h3v.s4.34d8c477b2e6 from=translated src=- shape=09dca381 vocab=35b57119
-/
theorem nil_not_mem_embA {a : A} {X : Set (Strn A)} : ([] : Strn A) ∉ embA a X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=ne.0h3v.s4.3bdfc01424aa from=translated src=- shape=45013f7a vocab=1251243f
-/
theorem embA_ne_univ (a : A) (X : Set (Strn A)) : embA a X ≠ Set.univ := by
  intro h; exact nil_not_mem_embA (X := X) (a := a) (by rw [h]; trivial)

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.0h4v.s5.6dcea1cec26c from=translated src=- shape=da1baad3 vocab=dbc4fd54
-/
theorem embA_inter (a : A) (X X' : Set (Strn A)) : embA a X ∩ embA a X' = embA a (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA]
  constructor
  · simp_all
  · rintro ⟨w', rfl, hX, hX'⟩; exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.1h5v.s5.c24bc78e9f69 from=translated src=- shape=340eeea1 vocab=266147f4
-/
theorem embA_inter_ne {a a' : A} (h : a ≠ a') (X Y : Set (Strn A)) :
    embA a X ∩ embA a' Y = ∅ := by
  ext w
  simp_all

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=iff.0h4v.s5.7af9f0c94d56 from=translated src=- shape=deb956c4 vocab=44d83845
-/
theorem embA_subset {a : A} {X X' : Set (Strn A)} : embA a X ⊆ embA a X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact hX'
  · rintro h w ⟨w', rfl, hX⟩; exact ⟨w', rfl, h hX⟩

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.1h4v.s4.3e51eecdaca0 from=translated src=- shape=421b9135 vocab=ffeab81a
-/
theorem embA_injective {a : A} {X X' : Set (Strn A)} (h : embA a X = embA a X') : X = X' :=
  Set.Subset.antisymm (embA_subset.mp h.subset) (embA_subset.mp h.symm.subset)

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=nonempty.1h3v.s4.ec2a6347571b from=translated src=- shape=6e3ac567 vocab=d778b4d3
-/
theorem embA_nonempty {a : A} {X : Set (Strn A)} (hX : X.Nonempty) : (embA a X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨a :: w', w', rfl, hw'⟩

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=memcn.1h3v.s4.dfdb5e2d6808 from=translated src=- shape=ba9fd936 vocab=58dea02d
-/
theorem memCn_embA_inv {a : A} {W : Set (Strn A)} (h : memCn (embA a W)) : memCn W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embA a W := hσ ▸ (show σ ∈ coneN σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_coneN] at hσ; rw [embA_injective hσ]; exact memCn_coneN w'
  · have hmem : σ ∈ embA a W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set (Strn A)))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_singleton] at hσ; rw [embA_injective hσ]; exact memCn_singleton w'

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=ne.2h5v.s5.bcfe12313dfa from=translated src=- shape=e6a58e21 vocab=d778b4d3
-/
theorem embA_ne {a a' : A} (h : a ≠ a') {X Y : Set (Strn A)} (hX : X.Nonempty) :
    embA a X ≠ embA a' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (a :: w') ∈ embA a' Y := heq ▸ (⟨w', rfl, hw'⟩ : (a :: w') ∈ embA a X)
  simp_all

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.0h3v.s5.d5ec8814bc55 from=translated src=- shape=3870187c vocab=2a0dc098
-/
theorem singleton_nil_inter_embA (a : A) (X : Set (Strn A)) :
    (({[]} : Set (Strn A)) ∩ embA a X) = ∅ := by
  simp_all

omit [DecidableEq A] in
/--
@isnad1 id=ne.0h1v.s4.1a3b94727f2a from=translated src=- shape=82992da7 vocab=d5a714b7
-/
theorem singleton_nil_ne_univ : ({[]} : Set (Strn A)) ≠ Set.univ := by
  simp_all

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=ne.0h3v.s4.0d7540759857 from=translated src=- shape=56b9f123 vocab=93b830d0
-/
theorem singleton_nil_ne_embA (a : A) (X : Set (Strn A)) :
    ({[]} : Set (Strn A)) ≠ embA a X := by
  intro h
  exact nil_not_mem_embA
    (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Strn A) ∈ ({[]} : Set (Strn A))))

omit [DecidableEq A] [Inhabited A] in
/-- **The shape of a `Cₐ`-neighbourhood.** Every neighbourhood is the master `Σ*`,
the terminator
`{Λ}`, or an `a`-copy `aX` with `X ∈ Cₐ`.
@isnad1 id=or.1h2v.s5.7084e87ec002 from=translated src=- shape=4e39cdd0 vocab=6244de40
-/
theorem memCn_cases {W : Set (Strn A)} (hW : memCn W) :
    W = Set.univ ∨ W = ({[]} : Set (Strn A)) ∨ ∃ a X, memCn X ∧ W = embA a X := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl coneN_nil
    | cons a σ' => exact Or.inr (Or.inr ⟨a, coneN σ', memCn_coneN σ', (embA_coneN a σ').symm⟩)
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons a σ' => exact Or.inr (Or.inr ⟨a, {σ'}, memCn_singleton σ', (embA_singleton a σ').symm⟩)

/-! ### The sum target `𝟙 + Σ_a Cₐ` and its inversion lemmas. -/

/-- The right-hand side of the domain equation: the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/
abbrev CCn (A : Type) [DecidableEq A] : NeighborhoodSystem (SigTok A (Strn A)) :=
  sumSig A (Cn A) Cn_nonempty

omit [Inhabited A] in
/--
@isnad1 id=mem.1h3v.s5.07fce9dd7d1e from=translated src=- shape=23211103 vocab=7cd9d693
-/
theorem sumSig_mem_jc_inv {a : A} {X : Set (Strn A)} (h : (CCn A).mem (jc a X)) :
    (Cn A).mem X := by
  rcases h with h0 | hU | ⟨a', X', hX', heq⟩
  · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
  · have : (tu : SigTok A (Strn A)) ∈ jc a X := by rw [hU]; rfl
    exact absurd this tu_not_mem_jc
  · by_cases haa : a = a'
    · subst haa; rw [jc_injective heq]; exact hX'
    · obtain ⟨t, ht⟩ := Cn_nonempty X' hX'
      exact absurd (heq.symm ▸ (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm haa))

/-! ### The forward half `toCC : |Cₐ| → |𝟙 + Σ_a Cₐ|`. -/

/-- **Forward half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** Records, for each branch, whether `x`
finishes at `Λ`
(the `𝟙`-summand) or reaches the `a`-copy `aX` (the `a`-th summand). -/
def toCC (x : (Cn A).Element) : (CCn A).Element where
  mem W := W = masterSig (Cn A)
    ∨ (W = jU ∧ x.mem ({[]} : Set (Strn A)))
    ∨ (∃ a X, (Cn A).mem X ∧ W = jc a X ∧ x.mem (embA a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨a', X', hX', rfl, hzF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [masterSig_inter_jU], hzU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [masterSig_inter_jc hX'], hzF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, masterSig_inter_jU], hzU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hzU⟩)
    · exfalso
      have hx := x.inter_mem hzU hzF'; rw [singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hzF⟩)
    · exfalso
      have hx := x.inter_mem hzF hzU'; rw [Set.inter_comm, singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hx := x.inter_mem hzF hzF'; rw [embA_inter] at hx
        exact Or.inr (Or.inr ⟨a, X ∩ X', memCn_embA_inv (x.sub hx), jc_inter_jc_same a X X', hx⟩)
      · exfalso
        have hx := x.inter_mem hzF hzF'; rw [embA_inter_ne haa] at hx
        obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((CCn A).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X', hX', rfl,
          x.up_mem hzF (memCn_embA a hX') (embA_subset.mpr (jc_subset_jc.mp hsub))⟩)

omit [Inhabited A] in
/--
@isnad1 id=iff.0h2v.s5.4fdc53ae9ed8 from=translated src=- shape=2ed50eda vocab=bf90afba
-/
@[simp] theorem toCC_mem_jU {x : (Cn A).Element} :
    (toCC x).mem (jU : Set (SigTok A (Strn A))) ↔ x.mem ({[]} : Set (Strn A)) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨a', X', hX', heq, hz⟩)
    · exact absurd (h0.symm ▸ none_mem_masterSig) none_not_mem_jU
    · exact hz
    · exact absurd (heq ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

omit [Inhabited A] in
/--
@isnad1 id=iff.1h4v.s5.1b42480595db from=translated src=- shape=326e7943 vocab=f45e429e
-/
theorem toCC_mem_jc {x : (Cn A).Element} {a : A} {X : Set (Strn A)}
    (hX : (Cn A).mem X) :
    (toCC x).mem (jc a X) ↔ x.mem (embA a X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨a', X', hX', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · obtain ⟨t, ht⟩ := Cn_nonempty X hX
      exact absurd (heq ▸ (tc_mem_jc.mpr ht)) tc_not_mem_jU
    · obtain ⟨rfl, rfl⟩ := jc_eq_jc (Cn_nonempty X hX) heqj
      exact hz
  · intro hz; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hz⟩)

omit [DecidableEq A] [Inhabited A] in
/-- Prefixed copies determine index and set: `aX = a'X'` (with `X` non-empty)
forces `a=a'`,
`X=X'`.
@isnad1 id=and.2h5v.s5.c1a065c24833 from=translated src=- shape=1a352b0f vocab=d778b4d3
-/
theorem embA_eq_embA {a a' : A} {X X' : Set (Strn A)} (hXne : X.Nonempty)
    (h : embA a X = embA a' X') : a = a' ∧ X = X' := by
  obtain ⟨w', hw'⟩ := hXne
  have hmem : (a :: w') ∈ embA a X := ⟨w', rfl, hw'⟩
  rw [h] at hmem
  obtain ⟨u, he, -⟩ := hmem
  rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
  exact ⟨rfl, embA_injective h⟩

/-! ### The inverse half `fromCC : |𝟙 + Σ_a Cₐ| → |Cₐ|`. -/

/-- **Inverse half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
def fromCC (s : (CCn A).Element) : (Cn A).Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set (Strn A)) ∧ s.mem jU)
    ∨ (∃ a X, (Cn A).mem X ∧ W = embA a X ∧ s.mem (jc a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl ⟨[], coneN_nil.symm⟩
    · exact memCn_singleton []
    · exact memCn_embA a hX
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨a', X', hX', rfl, hsF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [Set.univ_inter], hsF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_univ], hsF⟩)
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_same] at hs
        exact Or.inr (Or.inr ⟨a, X ∩ X', sumSig_mem_jc_inv (s.sub hs), embA_inter a X X', hs⟩)
      · exfalso
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_ne haa] at hs
        obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        simp_all
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
        refine Or.inr (Or.inr ⟨a, X', hX', rfl, ?_⟩)
        exact s.up_mem hsF (Or.inr (Or.inr ⟨a, X', hX', rfl⟩))
          (jc_subset_jc.mpr (embA_subset.mp hsub))

/--
@isnad1 id=iff.0h2v.s5.66038af8eb83 from=translated src=- shape=5558d256 vocab=5e1ab31a
-/
@[simp] theorem fromCC_mem_nil {s : (CCn A).Element} :
    (fromCC s).mem ({[]} : Set (Strn A)) ↔ s.mem (jU : Set (SigTok A (Strn A))) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨a', X', hX', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embA a' X')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

omit [Inhabited A] in
/--
@isnad1 id=iff.1h4v.s5.f2255a9ec4d1 from=translated src=- shape=97d8f16f vocab=6d2bd025
-/
theorem fromCC_mem_embA {s : (CCn A).Element} {a : A} {X : Set (Strn A)}
    (hX : (Cn A).mem X) :
    (fromCC s).mem (embA a X) ↔ s.mem (jc a X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨a', X', hX', heqj, hs⟩)
    · exact absurd h0 (embA_ne_univ a X)
    · exact absurd heq.symm (singleton_nil_ne_embA a X)
    · obtain ⟨rfl, rfl⟩ := embA_eq_embA (Cn_nonempty X hX) heqj
      exact hs
  · intro hs; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hs⟩)

/-! ### The two halves are mutually inverse. -/

omit [Inhabited A] in
/--
@isnad1 id=eq.0h2v.s4.7b86fb30d94a from=translated src=- shape=9c1e6faf vocab=ecde7e95
-/
theorem fromCC_toCC (x : (Cn A).Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_jU.mp hs
    · exact (toCC_mem_jc hX).mp hs
  · intro hW
    rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_jU.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (toCC_mem_jc hX).mpr hW⟩)

/--
@isnad1 id=eq.0h2v.s5.fdaaec704444 from=translated src=- shape=e7394b1a vocab=16489774
-/
theorem toCC_fromCC (s : (CCn A).Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embA hX).mp hs
  · intro hW
    rcases s.sub hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (fromCC_mem_embA hX).mpr hW⟩)

/-- **The isomorphism `|Cₐ| ≃o |𝟙 + Σ_a Cₐ|`.** -/
def ccEquiv : (Cn A).Element ≃o (CCn A).Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro hle W hW
      rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_jU.mp (hle _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_jc hX).mp (hle _ (Or.inr (Or.inr ⟨a, X, hX, rfl, hW⟩)))
    · intro hle W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hle _ hz⟩)
      · exact Or.inr (Or.inr ⟨a, X, hX, rfl, hle _ hz⟩)

/--
@isnad1 id=eq.0h2v.s7.73d0eb67b30b from=translated src=- shape=22f5185e vocab=af23b4f0
-/
@[simp] theorem ccEquiv_apply (x : (Cn A).Element) : ccEquiv x = toCC x := rfl

/-! ### Bridging the isomorphism to the successors `consMapN`. -/

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=iff.1h4v.s5.ebc61c19bc41 from=translated src=- shape=c8a84d35 vocab=2bafbf30
-/
theorem consMapN_mem_embA {a : A} {z : (Cn A).Element} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    ((consMapN a).toElementMap z).mem (embA a X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', -, -, hsub⟩
    rw [← embA_eq_prependN] at hsub
    exact z.up_mem hzX' hX (embA_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memCn_embA a hX, ?_⟩
    rw [← embA_eq_prependN]

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=not.1h5v.s5.d6e951ad56e5 from=translated src=- shape=05f6b41b vocab=15781112
-/
theorem consMapN_not_mem_embA_ne {a c : A} (hac : a ≠ c) {z : (Cn A).Element} {X : Set (Strn A)} :
    ¬ ((consMapN a).toElementMap z).mem (embA c X) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  obtain ⟨w, hw, -⟩ := hsub ⟨t, rfl, ht⟩
  rw [List.cons.injEq] at hw; exact hac hw.1

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=not.0h3v.s5.f8a078d82e7b from=translated src=- shape=e5cecb61 vocab=e24c3948
-/
theorem consMapN_not_mem_nil {a : A} {z : (Cn A).Element} :
    ¬ ((consMapN a).toElementMap z).mem ({[]} : Set (Strn A)) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  simp_all

omit [Inhabited A] in
/-- **`toCC ∘ (a·) = inj_a`.** Prepending the letter `a` to `z` is, across `Cₐ ≅
𝟙+Σ_a Cₐ`, the
injection of `z` into the `a`-th summand.
@isnad1 id=eq.0h3v.s5.2484780319cb from=translated src=- shape=c33a5568 vocab=c5ea62cf
-/
theorem toCC_consMapN (a : A) (z : (Cn A).Element) :
    toCC ((consMapN a).toElementMap z) = sinjC (h := Cn_nonempty) a z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨c, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact absurd hz consMapN_not_mem_nil
    · by_cases hac : a = c
      · subst hac; exact Or.inr ⟨X, hX, rfl, (consMapN_mem_embA hX).mp hz⟩
      · exact absurd hz (consMapN_not_mem_embA_ne hac)
  · rintro (rfl | ⟨X, hX, rfl, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (consMapN_mem_embA hX).mpr hm⟩)

omit [Inhabited A] in
/-- **`toCC Λ̂ = inj_𝟙`.** The finished empty sequence is the terminator (the
`𝟙`-summand).
@isnad1 id=eq.0h1v.s4.3b91104172c2 from=translated src=- shape=c44ccb37 vocab=9cf1eafb
-/
theorem toCC_strElemN_nil :
    toCC (strElemN ([] : Strn A)) = sinjU (h := Cn_nonempty) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, memCn_singleton [], subset_rfl⟩)

end Iso

/-! ## `Cₐ` as a `Tsig`-algebra. -/

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `Cₐ` as an object of the `∅`-free category. -/
def Cnobj (A : Type) : StrictDomainObj.{0} := ⟨Strn A, Cn A, Cn_nonempty⟩

/--
@isnad1 id=eq.0h1v.s3.e53c53c70621 from=translated src=- shape=ee354b3f vocab=0ac025d2
-/
@[simp] theorem Cnobj_sys (A : Type) : (Cnobj A).sys = Cn A := rfl

/-- **The `Tsig`-algebra structure on `Cₐ`.** The structure map `i : 𝟙+Σ_a Cₐ →
Cₐ` is the
inverse of
the domain-equation isomorphism `ccEquiv`, strict by `isStrict_ofIso`. -/
def cnStr : Category.Hom ((Tsig A).obj (Cnobj A)) (Cnobj A) :=
  ⟨ofIso ccEquiv.symm, isStrict_ofIso _⟩

/-- **`Cₐ` is a `Tsig`-algebra** for `Tsig(X) = 𝟙 + Σ_a X`. -/
def Cnalg (A : Type) [DecidableEq A] [Inhabited A] : TAlgebra (Tsig A) := ⟨Cnobj A, cnStr⟩

end Algebra

/-! ## The `liftCn` combinator: an approximable map out of `Cₐ` (generic
`Exercise419.liftC`). -/

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

omit [DecidableEq A] in
/-- A cone is never contained in a singleton: it has the two distinct elements `τ`
and
`τ·default`.
@isnad1 id=not.0h3v.s5.0dc0ae80aa81 from=translated src=- shape=ffd4bb74 vocab=feee9a08
-/
theorem not_coneN_subset_singleton (τ σ : Strn A) : ¬ coneN τ ⊆ ({σ} : Set (Strn A)) := by
  intro h
  have h1 : τ ∈ ({σ} : Set (Strn A)) := h (show τ ∈ coneN τ from List.prefix_rfl)
  have h2 : (τ ++ [default]) ∈ ({σ} : Set (Strn A)) := h (List.prefix_append τ [default])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [default] := h1.trans h2.symm
  simp at this

omit [DecidableEq A] in
/--
@isnad1 id=ne.0h3v.s4.546509455021 from=translated src=- shape=9a71b09e vocab=b2b91d1c
-/
theorem coneN_ne_singleton (τ σ : Strn A) : coneN τ ≠ ({σ} : Set (Strn A)) := fun h =>
  not_coneN_subset_singleton τ σ (h ▸ subset_rfl)

/-- A map `Cₐ → V` determined by its value `coneVal σ` on each partial element
`σ⊥` and `singVal σ`
on each total element `σ`. (The alphabet-generic copy of `Exercise419.liftC`.) -/
def liftCn (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap (Cn A) V where
  rel X Y := (∃ σ, X = coneN σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memCn_coneN σ
    · exact memCn_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [Cn_master]; exact coneN_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have hσσ : σ = σ' := coneN_injective hX'
      subst hσσ
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (coneN_ne_singleton σ σ')
    · exact absurd hX'.symm (coneN_ne_singleton σ' σ)
    · have hσσ : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst hσσ
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · have hpre : σ <+: τ := coneN_subset_coneN.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · have hpre : σ <+: τ := singleton_subset_coneN.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_coneN_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          simp_all
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

omit [DecidableEq A] in
/--
@isnad1 id=eq.2h6v.s7.47b7f36ce9be from=translated src=- shape=7ec9b487 vocab=2cc453b2
-/
theorem liftCn_strBot (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strBotN σ) = coneVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := coneN_subset_coneN.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_coneN_subset_singleton σ σ')
  · intro hY
    exact ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

omit [DecidableEq A] in
/--
@isnad1 id=eq.2h6v.s7.8b3ea097a93a from=translated src=- shape=1849a735 vocab=60b0cb87
-/
theorem liftCn_strElem (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strElemN σ) = singVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_coneN.mp; rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · simp_all
  · intro hY
    exact ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

omit [DecidableEq A] [Inhabited A] in
/-- Two maps out of `Cₐ` agree once they agree on every `σ⊥` and `σ` (generic
`Exercise516.map_ext_C`).
@isnad1 id=eq.2h5v.s6.5cc84659e55f from=translated src=- shape=2ca2b144 vocab=fb9a00e2
-/
theorem map_ext_Cn {V : NeighborhoodSystem β} {f g : ApproximableMap (Cn A) V}
    (hbot : ∀ σ, f.toElementMap (strBotN σ) = g.toElementMap (strBotN σ))
    (helem : ∀ σ, f.toElementMap (strElemN σ) = g.toElementMap (strElemN σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (Cn_mem.mp hX)
  · exact hbot σ
  · exact helem σ

end Lift

/-! ## Initiality of `(Cₐ, i)`: the unique homomorphism into any `Tsig`-algebra. -/

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The distinguished point `e = k(inj_𝟙)`: the image under `k` of the terminator. -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjU (h := B.carrier.nonempty))

/-- The `a`-th successor operation `f_a = k ∘ inj_a`. -/
def descF (a : A) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjC (h := B.carrier.nonempty) a y)

/-- The recursion `φ(Λ)=z`, `φ(a·σ)=f_a(φ(σ))` on a finite string, with base value
`z`. -/
def descVal (z : B.carrier.sys.Element) : Strn A → B.carrier.sys.Element
  | [] => z
  | a :: σ => descF B a (descVal z σ)

omit [Inhabited A] in
/--
@isnad1 id=le.1h5v.s7.1bd14f8fe0d7 from=translated src=- shape=6ef56334 vocab=9ddf03ae
-/
theorem descF_mono (a : A) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B a y ≤ descF B a y' :=
  B.str.1.toElementMap_mono (sinjC_mono h)

omit [Inhabited A] in
/--
@isnad1 id=le.1h5v.s7.dd51e5cfaacc from=translated src=- shape=396bae53 vocab=a8381de5
-/
theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

omit [Inhabited A] in
/--
@isnad1 id=eq.0h5v.s6.c44ebb1b89bb from=translated src=- shape=4e034aeb vocab=756a5e18
-/
theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Strn A) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons a σ ih => exact congrArg (descF B a) ih

omit [Inhabited A] in
/--
@isnad1 id=le.1h4v.s7.1f912fee7847 from=translated src=- shape=0666a5b0 vocab=0a66faa3
-/
theorem descMap_hcone {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

omit [Inhabited A] in
/--
@isnad1 id=le.1h4v.s6.45876c7c18ff from=translated src=- shape=8f6950a9 vocab=ce8c529e
-/
theorem descMap_hsing {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

/-- **The homomorphism `Cₐ → E`**, built by `liftCn` from the head-recursion. -/
def descMap : ApproximableMap (Cn A) B.carrier.sys :=
  liftCn B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

/--
@isnad1 id=eq.0h3v.s6.da114b72171c from=translated src=- shape=a0ebff7e vocab=33c1d137
-/
@[simp] theorem descMap_strBot (σ : Strn A) :
    (descMap B).toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ :=
  liftCn_strBot _ _ _ _ _ σ

/--
@isnad1 id=eq.0h3v.s6.61dd9e50a266 from=translated src=- shape=a87de752 vocab=fa4ecdc1
-/
@[simp] theorem descMap_strElem (σ : Strn A) :
    (descMap B).toElementMap (strElemN σ) = descVal B (descE B) σ :=
  liftCn_strElem _ _ _ _ _ σ

omit [DecidableEq A] [Inhabited A] in
/--
@isnad1 id=eq.0h1v.s4.f7f9f71943cc from=translated src=- shape=d63acad9 vocab=3f017257
-/
theorem Cn_bot_eq_strBotN_nil : (Cn A).bot = strBotN ([] : Strn A) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  change ((Cn A).mem Y ∧ (Cn A).master ⊆ Y) ↔ ((Cn A).mem Y ∧ coneN [] ⊆ Y)
  rw [Cn_master, coneN_nil]

/--
@isnad1 id=isstrict.0h2v.s5.a415fc8eeeee from=translated src=- shape=d544977b vocab=3a95c6b6
-/
theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, Cn_bot_eq_strBotN_nil, descMap_strBot]
  rfl

/-- The bundled strict homomorphism `Cₐ → E`. -/
def descStrict : Category.Hom (Cnobj A) B.carrier := ⟨descMap B, descMap_strict B⟩

/-! ### The homomorphism square and uniqueness. -/

omit [Inhabited A] in
/--
@isnad1 id=eq.0h5v.s8.db0c661914ca from=translated src=- shape=e0970343 vocab=2528e911
-/
theorem genKey (g : ApproximableMap (Cn A) B.carrier.sys) (a : A) (w : (Cn A).Element) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC ((consMapN a).toElementMap w)))
      = descF B a (g.toElementMap w) := by
  rw [toCC_consMapN, sumMapSig_sinjC]; rfl

omit [Inhabited A] in
/--
@isnad1 id=eq.0h3v.s8.556943a703fa from=translated src=- shape=d5335f51 vocab=9cebae26
-/
theorem genKey0 (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strElemN ([] : Strn A))))
      = descE B := by
  rw [toCC_strElemN_nil, sumMapSig_sinjU]; rfl

/--
@isnad1 id=eq.0h3v.s8.dd1ebd8f5333 from=translated src=- shape=e4e3114c vocab=38ff05ad
-/
theorem genKeyBot (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strBotN ([] : Strn A))))
      = B.carrier.sys.bot := by
  have hb : toCC (strBotN ([] : Strn A)) = (CCn A).bot := by
    rw [← Cn_bot_eq_strBotN_nil, ← ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMapSig (A := A) (h₀ := Cn_nonempty)
    (h₁ := B.carrier.nonempty) g)]
  exact isStrict_iff_apply_bot.mp B.str.2

/--
@isnad1 id=eq.0h1v.s7.b89d5fe99ca0 from=translated src=- shape=9cf298a9 vocab=8f6255e3
-/
theorem ccEquiv_symm_comp :
    (ofIso (ccEquiv (A := A)).symm).comp (ofIso ccEquiv) = idMap (Cn A) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

/--
@isnad1 id=eq.0h1v.s7.e1dae496b76d from=translated src=- shape=827bbb9b vocab=8f6255e3
-/
theorem ccEquiv_comp_symm :
    (ofIso (ccEquiv (A := A))).comp (ofIso ccEquiv.symm) = idMap (CCn A) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

/-- **Any map satisfying the homomorphism recursion equals `descMap`.**
@isnad1 id=eq.1h3v.s8.57d6945757dc from=translated src=- shape=f99fd4ea vocab=147acaae
-/
theorem rec_determines (g : ApproximableMap (Cn A) B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKeyBot B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strBot]
      have h := genKey B g a (strBotN σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElemN σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKey0 B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strElem]
      have h := genKey B g a (strElemN σ)
      rw [ih] at h
      exact h
  apply map_ext_Cn
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

/-- `Cₐ`'s algebra map satisfies the recursion.
@isnad1 id=eq.0h2v.s8.ca2e4ca9b64a from=translated src=- shape=ceb8fc4c vocab=147acaae
-/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_Cn
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strBot]
      have h := genKey B (descMap B) a (strBotN σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strElem]
      have h := genKey B (descMap B) a (strElemN σ)
      rw [descMap_strElem] at h
      exact h.symm

/-- **The homomorphism square** `desc ∘ i = k ∘ T(desc)`.
@isnad1 id=eq.0h2v.s8.330949324da5 from=translated src=- shape=81502392 vocab=09cd2bca
-/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

/-- **The descent homomorphism `(Cₐ, i) → (E, k)`** as a `Tsig`-algebra
homomorphism. -/
def descAlgHom : AlgHom (Cnalg A) B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

/-- **Uniqueness.** Any `Tsig`-algebra homomorphism out of `(Cₐ, i)` equals
`descAlgHom`.
@isnad1 id=eq.0h3v.s5.9ce5dbca6363 from=translated src=- shape=ec51ace6 vocab=2440dd0e
-/
theorem descAlgHom_uniq (h' : AlgHom (Cnalg A) B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (
          h₁ := B.carrier.nonempty) hom.1) := by
      have hcomm := congrArg Subtype.val comm
      exact hcomm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial

/-- **Exercise 6.17 part 2 — `(Cₐ, i)` is an initial `Tsig`-algebra for `Tsig(X) =
𝟙 + Σ_a X`.**
The descent map `φ : Cₐ → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(a·x)
= f_a(φ x)`
(`f_a = k ∘ inj_a`), built choice-free via `liftCn`; it is the unique
`Tsig`-algebra homomorphism, so
`Cₐ` is the initial algebra of `X ↦ 𝟙 + Σ_a X`. -/
def CnisInitial (A : Type) [DecidableEq A] [Inhabited A] : IsInitial (Cnalg A) where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

/-- **Exercise 6.17 part 2 — the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.**
@isnad1 id=isomorph.0h1v.s4.c29d635e1809 from=translated src=- shape=21c23ba3 vocab=95ed5a68
-/
theorem Cn_domain_equation (A : Type) [DecidableEq A] [Inhabited A] :
    Cn A ≅ᴰ CCn A := ⟨ccEquiv⟩

/-! ## Instantiation: `Cₙ ≅ 𝟙 + n·Cₙ` over the `n`-letter alphabet `Fin (n+1)`.

Taking `A := Fin (n+1)` recovers Scott's `Cₙ`: the domain of finite-or-infinite
sequences over an
`(n+1)`-letter alphabet, satisfying `Cₙ ≅ 𝟙 + (n+1)·Cₙ`. (For `n = 1`, `Fin 2 ≃
Bool` recovers
Example 6.2's `C ≅ 𝟙 + C + C`.) -/

/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`.
@isnad1 id=isomorph.0h1v.s6.4a4f91c0f70e from=translated src=- shape=f0fcd79f vocab=942ba71d
-/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))

/-- **`Cₙ` is the initial algebra** of `X ↦ 𝟙 + Σ_{Fin (n+1)} X`. -/
def CfinIsInitial (n : ℕ) : IsInitial (Cnalg (Fin (n + 1))) := CnisInitial (Fin (n + 1))

end Domain.Neighborhood.Exercise617Gen
