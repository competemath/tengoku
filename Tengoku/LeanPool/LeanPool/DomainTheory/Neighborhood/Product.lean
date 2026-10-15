/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.ApproximableExercises
public import Tengoku

/-!
# Lecture III (§3) — the product system: Definitions 3.1, 3.3, Propositions 3.2,
3.4,
Lemma 3.6, Theorems 3.5, 3.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981), Lecture III,
*Constructions on domains*. Given two neighbourhood systems over **disjoint**
token sets `Δ₀`, `Δ₁`,
the **product system** `𝒟₀ × 𝒟₁` has neighbourhoods `X ∪ Y` (`X ∈ 𝒟₀`, `Y ∈ 𝒟₁`)
over `Δ₀ ∪ Δ₁`.

We model the disjoint union of token sets by the **sum type** `α ⊕ β`, and the
product
neighbourhood `X ∪ Y` by `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y`. Because
`Sum.inl` and
`Sum.inr` have disjoint ranges, the cleanest facts of Scott's proof become
transparent:

* `prodNbhd_inter` — `(X ∪ Y) ∩ (X' ∪ Y') = (X ∩ X') ∪ (Y ∩ Y')` (Scott's (2));
* `prodNbhd_subset_iff` — `X ∪ Y ⊆ X' ∪ Y' ↔ X ⊆ X' ∧ Y ⊆ Y'` (Scott's (1));
* `prodNbhd_injective` — the representation `X ∪ Y` is unique.

This file formalizes:

* **Definition 3.1 / Proposition 3.2** — the product system `prod V₀ V₁`, the
element pairing
  `pair x y = ⟨x, y⟩`, the order law `pair_le_pair_iff` (3.2(i)), and the
  order-isomorphism
  `prodEquiv : |𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`.
* **Definition 3.3 / Proposition 3.4** — projections `proj₀`, `proj₁`, the paired
mapping `paired f g`,
  and `proj₀_comp_paired`, `proj₁_comp_paired`, `paired_proj` (`⟨p₀∘h, p₁∘h⟩ =
  h`),
  `toElementMap_paired` (`⟨f, g⟩(w) = ⟨f(w), g(w)⟩`).
* **Lemma 3.6** — constant maps `constMap b` (`X b Y ↔ Y ∈ b`) with
`toElementMap_constMap`.
* **Theorem 3.5** — joint vs. separate approximability, via the bridge
`ApproximableMap (prod V₀ V₁) V₂
  ≃ ApproximableMap₂ V₀ V₁ V₂` (`ofMap₂` / `toMap₂` and round-trips).
* **Proposition 3.7** — multivariate approximable functions are closed under
substitution
  (`comp`/`paired`/`proj` bookkeeping).

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- The product neighbourhood `X ∪ Y` over the disjoint union `Δ₀ ∪ Δ₁`, modelled
on `α ⊕ β` as
`Sum.inl '' X ∪ Sum.inr '' Y`. -/
def prodNbhd (X : Set α) (Y : Set β) : Set (α ⊕ β) := Sum.inl '' X ∪ Sum.inr '' Y

/--
@isnad1 id=iff.0h5v.s5.55dabd692535 from=translated src=- shape=439dec5c vocab=cefbe86a
-/
@[simp] theorem mem_prodNbhd_inl {X : Set α} {Y : Set β} {a : α} :
    (Sum.inl a : α ⊕ β) ∈ prodNbhd X Y ↔ a ∈ X := by
  simp [prodNbhd]

/--
@isnad1 id=iff.0h5v.s5.4eb0854bc983 from=translated src=- shape=62fb2f6a vocab=e09b71ef
-/
@[simp] theorem mem_prodNbhd_inr {X : Set α} {Y : Set β} {b : β} :
    (Sum.inr b : α ⊕ β) ∈ prodNbhd X Y ↔ b ∈ Y := by
  simp [prodNbhd]

/--
@isnad1 id=eq.0h4v.s4.b7bb13b19176 from=translated src=- shape=2502133d vocab=07128578
-/
@[simp] theorem inl_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inl ⁻¹' prodNbhd X Y = X := by ext a; simp

/--
@isnad1 id=eq.0h4v.s4.2c32aecf46fb from=translated src=- shape=af378d34 vocab=29f47882
-/
@[simp] theorem inr_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inr ⁻¹' prodNbhd X Y = Y := by ext b; simp

/-- Scott's (2): the product nbhds intersect componentwise.
@isnad1 id=eq.0h6v.s5.8a9d3271cac6 from=translated src=- shape=4497b71a vocab=37244cf9
-/
theorem prodNbhd_inter (X X' : Set α) (Y Y' : Set β) :
    prodNbhd X Y ∩ prodNbhd X' Y' = prodNbhd (X ∩ X') (Y ∩ Y') := by
  ext (a | b) <;> simp [Set.mem_inter_iff]

/-- Scott's (1): inclusion of product nbhds is componentwise (uses disjointness of
`Δ₀`, `Δ₁`).
@isnad1 id=iff.0h6v.s5.d7c1cd4a1303 from=translated src=- shape=87b0c089 vocab=a303434c
-/
theorem prodNbhd_subset_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y ⊆ prodNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have : (Sum.inl a : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using ha)
      simpa using this
    · have : (Sum.inr b : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using hb)
      simpa using this
  · rintro ⟨hX, hY⟩ (a | b) hs
    · simp only [mem_prodNbhd_inl] at hs ⊢; exact hX hs
    · simp only [mem_prodNbhd_inr] at hs ⊢; exact hY hs

/-- The representation `X ∪ Y` is unique (choice-free, via the preimage
projections).
@isnad1 id=and.1h6v.s5.88080d021d5d from=translated src=- shape=2abd59da vocab=d19a00ee
-/
theorem prodNbhd_injective {X X' : Set α} {Y Y' : Set β}
    (h : prodNbhd X Y = prodNbhd X' Y') : X = X' ∧ Y = Y' := by
  refine ⟨?_, ?_⟩
  · rw [← inl_preimage_prodNbhd X Y, ← inl_preimage_prodNbhd X' Y', h]
  · rw [← inr_preimage_prodNbhd X Y, ← inr_preimage_prodNbhd X' Y', h]

/-- **Definition 3.1 (Scott 1981, PRG-19).** The *product system* `𝒟₀ × 𝒟₁`:
neighbourhoods are
`X ∪ Y` with `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. Closure under consistent intersection is Scott's
(2)
(`prodNbhd_inter`) together with the factors' closure; the consistency witness `Z
⊆ (X∪Y) ∩ (X'∪Y')`
splits into witnesses `Z₀ ⊆ X ∩ X'`, `Z₁ ⊆ Y ∩ Y'` by `prodNbhd_subset_iff`. -/
def prod (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y
  master := prodNbhd V₀.master V₁.master
  master_mem := ⟨V₀.master, V₁.master, V₀.master_mem, V₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', V₀.inter_mem hX hX' hZ₀ hsub₀, V₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/--
@isnad1 id=iff.0h5v.s5.89165fd03e20 from=translated src=- shape=20d5ba66 vocab=bfca4b77
-/
@[simp] theorem prod_mem_iff {W : Set (α ⊕ β)} :
    (prod V₀ V₁).mem W ↔ ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y := Iff.rfl

/--
@isnad1 id=mem.2h6v.s5.5a6bada44886 from=translated src=- shape=9d7bcb42 vocab=bfca4b77
-/
theorem prod_mem_prodNbhd {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (prod V₀ V₁).mem (prodNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

/--
@isnad1 id=eq.0h4v.s5.658eea76a143 from=translated src=- shape=343ad82e vocab=9e38d63a
-/
@[simp] theorem prod_master : (prod V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl

/-! ### Projections of an element (Scott's `z₀`, `z₁`). -/

/-- Scott's `z₀ = {X ∈ 𝒟₀ ∣ X ∪ Δ₁ ∈ z}`: the first component of a product
element. -/
def NeighborhoodSystem.Element.fst (z : (prod V₀ V₁).Element) : V₀.Element where
  mem X := V₀.mem X ∧ z.mem (prodNbhd X V₁.master)
  sub h := h.1
  master_mem := ⟨V₀.master_mem, z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz := z.inter_mem hzX hzX'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, hA, _, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    refine ⟨hX', z.up_mem hzX (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩

/-- Scott's `z₁ = {Y ∈ 𝒟₁ ∣ Δ₀ ∪ Y ∈ z}`: the second component of a product
element. -/
def NeighborhoodSystem.Element.snd (z : (prod V₀ V₁).Element) : V₁.Element where
  mem Y := V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y)
  sub h := h.1
  master_mem := ⟨V₁.master_mem, z.master_mem⟩
  inter_mem := by
    rintro Y Y' ⟨_, hzY⟩ ⟨_, hzY'⟩
    have hz := z.inter_mem hzY hzY'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, _, hB, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hB, hz⟩
  up_mem := by
    rintro Y Y' ⟨_, hzY⟩ hY' hYY'
    refine ⟨hY', z.up_mem hzY (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨subset_rfl, hYY'⟩

/--
@isnad1 id=iff.0h6v.s5.6bdd9345275b from=translated src=- shape=1a6b1260 vocab=724cb240
-/
@[simp] theorem mem_fst {z : (prod V₀ V₁).Element} {X : Set α} :
    z.fst.mem X ↔ V₀.mem X ∧ z.mem (prodNbhd X V₁.master) := Iff.rfl

/--
@isnad1 id=iff.0h6v.s5.0d8c14f3bd9b from=translated src=- shape=886bd05f vocab=421a50b9
-/
@[simp] theorem mem_snd {z : (prod V₀ V₁).Element} {Y : Set β} :
    z.snd.mem Y ↔ V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y) := Iff.rfl

/-- The key splitting (Scott's (3)): for a product element `z` and neighbourhoods
`X ∈ 𝒟₀`,
`Y ∈ 𝒟₁`, membership of `X ∪ Y` in `z` is equivalent to membership of its two
"slices".
@isnad1 id=iff.2h7v.s6.0cc734f9c302 from=translated src=- shape=fede9f6c vocab=b87bfb32
-/
theorem prod_mem_split {z : (prod V₀ V₁).Element} {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    z.mem (prodNbhd X Y) ↔ z.mem (prodNbhd X V₁.master) ∧ z.mem (prodNbhd V₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prod_mem_prodNbhd hX V₁.master_mem) ?_,
            z.up_mem h (prod_mem_prodNbhd V₀.master_mem hY) ?_⟩
    · exact prodNbhd_subset_iff.mpr ⟨subset_rfl, V₁.sub_master hY⟩
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
      Set.inter_eq_right.mpr (V₁.sub_master hY)] at this

/-! ### Definition 3.1 — the element pairing `⟨x, y⟩`. -/

/-- **Definition 3.1 (Scott 1981, PRG-19).** The element pairing `⟨x, y⟩ = {X ∪ Y
∣ X ∈ x, Y ∈
y}`. -/
def pair (x : V₀.Element) (y : V₁.Element) : (prod V₀ V₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prod_mem_prodNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

/--
@isnad1 id=iff.0h7v.s6.060a7e4c8929 from=translated src=- shape=40626a8e vocab=daa6afad
-/
@[simp] theorem mem_pair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (pair x y).mem W ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y := Iff.rfl

/--
@isnad1 id=iff.0h8v.s5.35345df07b45 from=translated src=- shape=885ae2c7 vocab=daa6afad
-/
theorem mem_pair_prodNbhd {x : V₀.Element} {y : V₁.Element} {X : Set α} {Y : Set β} :
    (pair x y).mem (prodNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

/-- **Proposition 3.2(i) (Scott 1981, PRG-19).** `⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑
y'`.
@isnad1 id=iff.0h8v.s6.f296545af44e from=translated src=- shape=52f9a990 vocab=4104d8ec
-/
theorem pair_le_pair_iff {x x' : V₀.Element} {y y' : V₁.Element} :
    pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd X V₁.master) ⟨X, V₁.master, hX, y.master_mem, rfl⟩
      obtain ⟨rfl, _⟩ := prodNbhd_injective heq
      exact hX'
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd V₀.master Y) ⟨V₀.master, Y, x.master_mem, hY, rfl⟩
      obtain ⟨_, rfl⟩ := prodNbhd_injective heq
      exact hY'
  · rintro ⟨hx, hy⟩ W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, hx X hX, hy Y hY, rfl⟩

/-- `z = ⟨z₀, z₁⟩`: every product element is the pairing of its two components.
@isnad1 id=eq.0h5v.s5.20060e06e9a3 from=translated src=- shape=b18796ce vocab=3ddbd460
-/
theorem pair_fst_snd (z : (prod V₀ V₁).Element) : pair z.fst z.snd = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prod_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prod_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

/--
@isnad1 id=eq.0h6v.s5.3aa89a8e18c0 from=translated src=- shape=b45f973c vocab=8d4c2613
-/
@[simp] theorem fst_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).fst = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).1
  · intro hX
    exact ⟨x.sub hX, mem_pair_prodNbhd.mpr ⟨hX, y.master_mem⟩⟩

/--
@isnad1 id=eq.0h6v.s5.4f3a556d1250 from=translated src=- shape=37db35c8 vocab=03c2db8c
-/
@[simp] theorem snd_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).snd = y := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).2
  · intro hY
    exact ⟨y.sub hY, mem_pair_prodNbhd.mpr ⟨x.master_mem, hY⟩⟩

/-- **Proposition 3.2 (Scott 1981, PRG-19).** The order-isomorphism `|𝒟₀ × 𝒟₁| ≃o
|𝒟₀| × |𝒟₁|`. -/
def prodEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o V₀.Element × V₁.Element where
  toFun z := (z.fst, z.snd)
  invFun p := pair p.1 p.2
  left_inv z := pair_fst_snd z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prod_mem_split hX hY).mp hW
      have hX' : z'.fst.mem X := h1 X ⟨hX, ha⟩
      have hY' : z'.snd.mem Y := h2 Y ⟨hY, hb⟩
      exact (prod_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

/--
@isnad1 id=eq.0h5v.s7.21cf7fbda9af from=translated src=- shape=01b6bc69 vocab=f1c72664
-/
@[simp] theorem prodEquiv_apply (z : (prod V₀ V₁).Element) :
    prodEquiv V₀ V₁ z = (z.fst, z.snd) := rfl

/--
@isnad1 id=eq.0h5v.s8.db237e0e3445 from=translated src=- shape=38b78225 vocab=0a712686
-/
@[simp] theorem prodEquiv_symm_apply (p : V₀.Element × V₁.Element) :
    (prodEquiv V₀ V₁).symm p = pair p.1 p.2 := rfl

/-! ### Definition 3.3 / Proposition 3.4 — projections and pairing of maps. -/

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- Every product neighbourhood is `(inl⁻¹ W) ∪ (inr⁻¹ W)`.
@isnad1 id=eq.1h5v.s5.15a45a2a0c2b from=translated src=- shape=8baac726 vocab=eb62f98f
-/
theorem prodNbhd_preimage {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) :
    W = prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, _, rfl⟩ := hW
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]

/-- An approximable map relates any input neighbourhood to the master output `Δ₁`.
@isnad1 id=rel.1h6v.s5.1aebd60c2283 from=translated src=- shape=bf49d8c1 vocab=d36a17dc
-/
theorem ApproximableMap.rel_master (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) :
    f.rel X V₁.master :=
  f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₀ : 𝒟₀ × 𝒟₁ → 𝒟₀`,
`(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def proj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₀ where
  rel W X' := (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨_, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, hA, ‹_›, rfl⟩, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₁ : 𝒟₀ × 𝒟₁ → 𝒟₁`,
`(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def proj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₁ where
  rel W Y' := (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨_, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, ‹_›, hB, rfl⟩, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

/-- **Definition 3.3 (Scott 1981, PRG-19).** The paired mapping `⟨f, g⟩ : 𝒟₂ → 𝒟₀
× 𝒟₁`,
`Z ⟨f, g⟩ (X ∪ Y) ↔ Z f X ∧ Z g Y`. -/
def paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    ApproximableMap V₂ (prod V₀ V₁) where
  rel Z P := (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P)
  rel_dom h := f.rel_dom h.2.1
  rel_cod h := h.1
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_, ?_⟩
    · simpa using f.master_rel
    · simpa using g.master_rel
  inter_right := by
    rintro Z P P' ⟨hP, hfP, hgP⟩ ⟨hP', hfP', hgP'⟩
    have hfX := f.inter_right hfP hfP'
    have hgY := g.inter_right hgP hgP'
    refine ⟨?_, ?_, ?_⟩
    · rw [prodNbhd_preimage hP, prodNbhd_preimage hP', prodNbhd_inter]
      exact prod_mem_prodNbhd (f.rel_cod hfX) (g.rel_cod hgY)
    · rw [Set.preimage_inter]; exact hfX
    · rw [Set.preimage_inter]; exact hgY
  mono := by
    rintro Z Z₂ P P₂ ⟨_, hfP, hgP⟩ hZ₂Z hPP₂ hZ₂ hP₂
    obtain ⟨A, B, hA, hB, rfl⟩ := hP₂
    have hinl : Sum.inl ⁻¹' P ⊆ A := by
      have := Set.preimage_mono (f := Sum.inl) hPP₂; rwa [inl_preimage_prodNbhd] at this
    have hinr : Sum.inr ⁻¹' P ⊆ B := by
      have := Set.preimage_mono (f := Sum.inr) hPP₂; rwa [inr_preimage_prodNbhd] at this
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]; exact f.mono hfP hZ₂Z hinl hZ₂ hA
    · rw [inr_preimage_prodNbhd]; exact g.mono hgP hZ₂Z hinr hZ₂ hB

/--
@isnad1 id=iff.0h6v.s6.67d2b6a631d9 from=translated src=- shape=33411d62 vocab=7fd84291
-/
@[simp] theorem proj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (proj₀ V₀ V₁).rel W X' ↔ (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

/--
@isnad1 id=iff.0h6v.s6.a4c3299a615e from=translated src=- shape=53f642e0 vocab=3f54f145
-/
@[simp] theorem proj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (proj₁ V₀ V₁).rel W Y' ↔ (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

/--
@isnad1 id=iff.0h10v.s6.429d20b1842b from=translated src=- shape=4004efd0 vocab=ee1ae8fb
-/
@[simp] theorem paired_rel {f : ApproximableMap V₂ V₀} {g : ApproximableMap V₂ V₁}
    {Z : Set γ} {P : Set (α ⊕ β)} :
    (paired f g).rel Z P ↔
      (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P) := Iff.rfl

/-- **Proposition 3.4(ii) (Scott 1981, PRG-19).** `p₀(z) = z₀`.
@isnad1 id=eq.0h5v.s5.158c052ab2f9 from=translated src=- shape=cbda7846 vocab=b903abbe
-/
@[simp] theorem toElementMap_proj₀ (z : (prod V₀ V₁).Element) :
    (proj₀ V₀ V₁).toElementMap z = z.fst := by
  apply Element.ext
  intro X'
  constructor
  · rintro ⟨W, hzW, hW, hX', hsub⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub
    refine ⟨hX', z.up_mem hzW (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hsub, V₁.sub_master hB⟩
  · rintro ⟨hX', hz⟩
    exact ⟨prodNbhd X' V₁.master, hz, prod_mem_prodNbhd hX' V₁.master_mem, hX', by simp⟩

/-- **Proposition 3.4(ii) (Scott 1981, PRG-19).** `p₁(z) = z₁`.
@isnad1 id=eq.0h5v.s5.345932bd23f9 from=translated src=- shape=b9862597 vocab=1675f474
-/
@[simp] theorem toElementMap_proj₁ (z : (prod V₀ V₁).Element) :
    (proj₁ V₀ V₁).toElementMap z = z.snd := by
  apply Element.ext
  intro Y'
  constructor
  · rintro ⟨W, hzW, hW, hY', hsub⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub
    refine ⟨hY', z.up_mem hzW (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hA, hsub⟩
  · rintro ⟨hY', hz⟩
    exact ⟨prodNbhd V₀.master Y', hz, prod_mem_prodNbhd V₀.master_mem hY', hY', by simp⟩

/-- **Proposition 3.4(iv) (Scott 1981, PRG-19).** `⟨f, g⟩(w) = ⟨f(w), g(w)⟩`.
@isnad1 id=eq.0h9v.s6.052afcb5e272 from=translated src=- shape=3e684099 vocab=b2bb008b
-/
theorem toElementMap_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁)
    (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) := by
  apply Element.ext
  intro P
  constructor
  · rintro ⟨Z, hwZ, hP, hfZ, hgZ⟩
    exact ⟨Sum.inl ⁻¹' P, Sum.inr ⁻¹' P, ⟨Z, hwZ, hfZ⟩, ⟨Z, hwZ, hgZ⟩, prodNbhd_preimage hP⟩
  · rintro ⟨X, Y, ⟨Z₁, hwZ₁, hfZ₁⟩, ⟨Z₂, hwZ₂, hgZ₂⟩, rfl⟩
    refine ⟨Z₁ ∩ Z₂, w.inter_mem hwZ₁ hwZ₂, prod_mem_prodNbhd (f.rel_cod hfZ₁) (g.rel_cod hgZ₂),
      ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]
      exact f.mono hfZ₁ Set.inter_subset_left subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (f.rel_cod hfZ₁)
    · rw [inr_preimage_prodNbhd]
      exact g.mono hgZ₂ Set.inter_subset_right subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (g.rel_cod hgZ₂)

/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₀ ∘ ⟨f, g⟩ = f`.
@isnad1 id=eq.0h8v.s5.eeb16ebe9066 from=translated src=- shape=b3008c56 vocab=85f0ef00
-/
theorem proj₀_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired f g) = f := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, fst_pair]

/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₁ ∘ ⟨f, g⟩ = g`.
@isnad1 id=eq.0h8v.s5.576720ed3f09 from=translated src=- shape=e859da52 vocab=cbd6bc4c
-/
theorem proj₁_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₁ V₀ V₁).comp (paired f g) = g := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₁, snd_pair]

/-- **Proposition 3.4(iii) (Scott 1981, PRG-19).** `h = ⟨p₀ ∘ h, p₁ ∘ h⟩`.
@isnad1 id=eq.0h7v.s6.0f167f6323f6 from=translated src=- shape=151e0729 vocab=8ab558e3
-/
theorem paired_proj (h : ApproximableMap V₂ (prod V₀ V₁)) :
    paired ((proj₀ V₀ V₁).comp h) ((proj₁ V₀ V₁).comp h) = h := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, pair_fst_snd]

/--
@isnad1 id=iff.0h6v.s5.c62d692d24ef from=translated src=- shape=3b88151c vocab=bfca4b77
-/
theorem prod_mem_prodNbhd_iff {X : Set α} {Y : Set β} :
    (prod V₀ V₁).mem (prodNbhd X Y) ↔ V₀.mem X ∧ V₁.mem Y := by
  constructor
  · rintro ⟨A, B, hA, hB, heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hB⟩
  · rintro ⟨hX, hY⟩; exact prod_mem_prodNbhd hX hY

/-! ### Lemma 3.6 — constant maps. -/

/-- **Lemma 3.6 (Scott 1981, PRG-19).** The constant map at `b : |𝒟₁|`: `X b Y ↔ Y
∈ b`. -/
def constMap (V₀ : NeighborhoodSystem α) (b : V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ b.mem Y
  rel_dom h := h.1
  rel_cod h := b.sub h.2
  master_rel := ⟨V₀.master_mem, b.master_mem⟩
  inter_right := by rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩; exact ⟨hX, b.inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hY⟩ _ hYY' hX' hY'
    exact ⟨hX', b.up_mem hY hY' hYY'⟩

/--
@isnad1 id=iff.0h7v.s5.5d11973fda3f from=translated src=- shape=6d77fddf vocab=b91a8bb4
-/
@[simp] theorem constMap_rel {b : V₁.Element} {X : Set α} {Y : Set β} :
    (constMap V₀ b).rel X Y ↔ V₀.mem X ∧ b.mem Y := Iff.rfl

/-- **Lemma 3.6 (Scott 1981, PRG-19).** The constant map sends every element to
`b`.
@isnad1 id=eq.0h6v.s5.81b5e8c6d7bb from=translated src=- shape=8ccb0f05 vocab=36730800
-/
@[simp] theorem toElementMap_constMap (b : V₁.Element) (x : V₀.Element) :
    (constMap V₀ b).toElementMap x = b := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, _, _, hbY⟩; exact hbY
  · intro hbY; exact ⟨V₀.master, x.master_mem, V₀.master_mem, hbY⟩

/-! ### Theorem 3.5 — joint vs. separate approximability. -/

/-- Extensionality for two-variable approximable mappings.
@isnad1 id=eq.1h8v.s6.c77058cd1129 from=translated src=- shape=bd9eb682 vocab=8512b2ea
-/
theorem ApproximableMap₂.ext {f g : ApproximableMap₂ V₀ V₁ V₂}
    (h : ∀ X Y Z, f.rel X Y Z ↔ g.rel X Y Z) : f = g := by
  obtain ⟨rf, _, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y Z; exact propext (h X Y Z)
  subst this; rfl

/-- **Theorem 3.5 (→) (Scott 1981, PRG-19).** A joint approximable mapping `𝒟₀ ×
𝒟₁ → 𝒟₂`
restricts to a two-variable mapping `X, Y f Z ↔ (X ∪ Y) f Z`. -/
def toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap₂ V₀ V₁ V₂ where
  rel X Y Z := f.rel (prodNbhd X Y) Z
  rel_dom₀ h := (prod_mem_prodNbhd_iff.mp (f.rel_dom h)).1
  rel_dom₁ h := (prod_mem_prodNbhd_iff.mp (f.rel_dom h)).2
  rel_cod h := f.rel_cod h
  master_rel := f.master_rel
  inter_right h h' := f.inter_right h h'
  mono := by
    rintro X X' Y Y' Z Z' hrel hX'X hY'Y hZZ' hX' hY' hZ'
    exact f.mono hrel (prodNbhd_subset_iff.mpr ⟨hX'X, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX' hY') hZ'

/-- **Theorem 3.5 (←) (Scott 1981, PRG-19).** A two-variable mapping induces a
joint mapping. -/
def ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ f.rel (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) Z
  rel_dom h := h.1
  rel_cod h := f.rel_cod h.2
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    simpa using f.master_rel
  inter_right := by rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩; exact ⟨hW, f.inter_right hrel hrel'⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl
    rw [inr_preimage_prodNbhd] at hinr
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact f.mono hrel hinl hinr hZZ' hA hB hZ'

/--
@isnad1 id=eq.0h7v.s5.740a3cad215b from=translated src=- shape=ef58472d vocab=4d78b89a
-/
theorem toMap₂_ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : toMap₂ (ofMap₂ f) = f := by
  apply ApproximableMap₂.ext
  intro X Y Z
  change (prod V₀ V₁).mem (prodNbhd X Y) ∧ f.rel _ _ Z ↔ _
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  constructor
  · rintro ⟨_, hrel⟩; exact hrel
  · intro hrel
    exact ⟨prod_mem_prodNbhd (f.rel_dom₀ hrel) (f.rel_dom₁ hrel), hrel⟩

/--
@isnad1 id=eq.0h7v.s5.54448be3a894 from=translated src=- shape=a43e0d99 vocab=e77cbf71
-/
theorem ofMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) : ofMap₂ (toMap₂ f) = f := by
  apply ApproximableMap.ext
  intro W Z
  change (prod V₀ V₁).mem W ∧ f.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z ↔ _
  constructor
  · rintro ⟨hW, hrel⟩; rwa [← prodNbhd_preimage hW] at hrel
  · intro hrel
    exact ⟨f.rel_dom hrel, by rwa [← prodNbhd_preimage (f.rel_dom hrel)]⟩

/-- **Theorem 3.5 (Scott 1981, PRG-19).** The bijection between joint approximable
mappings
`𝒟₀ × 𝒟₁ → 𝒟₂` and two-variable mappings `𝒟₀, 𝒟₁ → 𝒟₂`: a function of two
arguments comes from
an approximable mapping iff it is separately approximable. -/
def map₂Equiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃ ApproximableMap₂ V₀ V₁ V₂ where
  toFun := toMap₂
  invFun := ofMap₂
  left_inv := ofMap₂_toMap₂
  right_inv := toMap₂_ofMap₂

/-- **Theorem 3.5 (elementwise) (Scott 1981, PRG-19).** The two-variable
elementwise map of
`toMap₂ f` is `f` evaluated at the pairing: `(toMap₂ f)(x, y) = f(⟨x, y⟩)`.
@isnad1 id=eq.0h9v.s6.8536912c6d19 from=translated src=- shape=8cbc20b7 vocab=b87585b7
-/
theorem toElementMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element)
    (y : V₁.Element) :
    (toMap₂ f).toElementMap₂ x y = f.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, hX, hY, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
    exact ⟨X, Y, hX, hY, hrel⟩

/-! ### Proposition 3.7 — closure under substitution. -/

variable {V₃ : NeighborhoodSystem δ}

/-- **Proposition 3.7 (Scott 1981, PRG-19).** Multivariate approximable functions
are closed under
substitution: substituting approximable maps `a, b : 𝒟₃ → 𝒟ᵢ` into a two-variable
approximable map
`F : 𝒟₀ × 𝒟₁ → 𝒟₂` yields the approximable map `F ∘ ⟨a, b⟩`, whose value is
`F(a(w), b(w))`. The
building blocks are exactly Definition 3.3's `paired` and Theorem 2.5's `comp`.
@isnad1 id=eq.0h12v.s6.7ba1f621aa05 from=translated src=- shape=2a796714 vocab=c0d3b40b
-/
theorem substitution_toElementMap (F : ApproximableMap (prod V₀ V₁) V₂)
    (a : ApproximableMap V₃ V₀) (b : ApproximableMap V₃ V₁) (w : V₃.Element) :
    (F.comp (paired a b)).toElementMap w
      = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, toElementMap₂_toMap₂]

end Domain.Neighborhood
