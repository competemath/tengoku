/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Approximable
public import Tengoku

/-!
# Exercise 3.18 (Scott 1981, PRG-19, §3) — the sum (coproduct) system

Scott's sum of `𝒟₀` (over `Δ₀`) and `𝒟₁` (over `Δ₁`), assuming *no neighbourhood
is empty*:

`𝒟₀ + 𝒟₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`,

a neighbourhood system over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. We model the tokens as `Option (α ⊕
β)`: `Λ = none`,
`0a = some (inl a)`, `1b = some (inr b)`; then `0X = il '' X` and `1Y = ir '' Y`.

The non-emptiness assumption (`h₀`, `h₁`) is exactly what makes the system closed
under intersection:
the two tagged copies are disjoint (`inj₀ X ∩ inj₁ Y = ∅`), so a cross pair `0X,
1Y` is *inconsistent*
(no non-empty neighbourhood lies in `∅`), and same-tag intersections reduce to
those of the factors.

We then build the injections `inMapᵢ : 𝒟ᵢ → 𝒟₀ + 𝒟₁` and projections `outMapᵢ : 𝒟₀
+ 𝒟₁ → 𝒟ᵢ`,
and prove `outMapᵢ ∘ inMapᵢ = I_{𝒟ᵢ}`. (The non-emptiness assumption is what makes
the system a
neighbourhood system; the section/retraction identities hold for the resulting
maps.)

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Left tag `0a = some (inl a)`. -/
def il (a : α) : Option (α ⊕ β) := some (Sum.inl a)

/-- Right tag `1b = some (inr b)`. -/
def ir (b : β) : Option (α ⊕ β) := some (Sum.inr b)

/-- The tagged left copy `0X = {some (inl a) ∣ a ∈ X}`. -/
def inj₀ (X : Set α) : Set (Option (α ⊕ β)) := il '' X

/-- The tagged right copy `1Y = {some (inr b) ∣ b ∈ Y}`. -/
def inj₁ (Y : Set β) : Set (Option (α ⊕ β)) := ir '' Y

/--
@isnad1 id=iff.0h4v.s5.08254715c6e0 from=translated src=- shape=c2677913 vocab=e2407b2b
-/
@[simp] theorem il_mem_inj₀ {X : Set α} {a : α} : (il a : Option (α ⊕ β)) ∈ inj₀ X ↔ a ∈ X := by
  simp only [inj₀, Set.mem_image, il]
  simp_all

/--
@isnad1 id=not.0h4v.s5.eaa1286bf168 from=translated src=- shape=9b5d07b3 vocab=7b07e3aa
-/
@[simp] theorem ir_mem_inj₀ {X : Set α} {b : β} : (ir b : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il, ir])

/--
@isnad1 id=not.0h3v.s4.3e9a451e294f from=translated src=- shape=c18c6db3 vocab=a6e26a3b
-/
@[simp] theorem none_mem_inj₀ {X : Set α} : (none : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il])

/--
@isnad1 id=iff.0h4v.s5.649b42877ff3 from=translated src=- shape=e7725b42 vocab=59e06563
-/
@[simp] theorem ir_mem_inj₁ {Y : Set β} {b : β} : (ir b : Option (α ⊕ β)) ∈ inj₁ Y ↔ b ∈ Y := by
  simp only [inj₁, Set.mem_image, ir]
  simp_all

/--
@isnad1 id=not.0h4v.s5.08df1eaccfab from=translated src=- shape=7191e0a8 vocab=284c030e
-/
@[simp] theorem il_mem_inj₁ {Y : Set β} {a : α} : (il a : Option (α ⊕ β)) ∉ inj₁ Y := by
  rintro ⟨b, _, hb⟩; exact absurd hb (by simp [il, ir])

/--
@isnad1 id=not.0h3v.s4.cc2db75faa49 from=translated src=- shape=375e78e1 vocab=51962980
-/
@[simp] theorem none_mem_inj₁ {Y : Set β} : (none : Option (α ⊕ β)) ∉ inj₁ Y := by
  rintro ⟨b, _, hb⟩; exact absurd hb (by simp [ir])

/--
@isnad1 id=eq.0h4v.s5.85e424988d2a from=translated src=- shape=3d3fe648 vocab=8746fe91
-/
theorem inj₀_inter (X X' : Set α) :
    (inj₀ X ∩ inj₀ X' : Set (Option (α ⊕ β))) = inj₀ (X ∩ X') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, il, inj₀]

/--
@isnad1 id=eq.0h4v.s5.f209f18fc64c from=translated src=- shape=9273e613 vocab=fde52786
-/
theorem inj₁_inter (Y Y' : Set β) :
    (inj₁ Y ∩ inj₁ Y' : Set (Option (α ⊕ β))) = inj₁ (Y ∩ Y') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, ir, inj₁]

/--
@isnad1 id=eq.0h4v.s5.4c08e9e6aac5 from=translated src=- shape=fadf719d vocab=222af357
-/
theorem inj₀_inter_inj₁ (X : Set α) (Y : Set β) :
    (inj₀ X ∩ inj₁ Y : Set (Option (α ⊕ β))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro t ⟨ht0, ht1⟩
  rcases t with _ | (a | b)
  · exact none_mem_inj₀ ht0
  · exact il_mem_inj₁ ht1
  · exact ir_mem_inj₀ ht0

/--
@isnad1 id=nonempty.1h3v.s4.7ae09ea57458 from=translated src=- shape=77f6bca3 vocab=5d860846
-/
theorem inj₀_nonempty {X : Set α} (hX : X.Nonempty) : (inj₀ X : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image il hX

/--
@isnad1 id=nonempty.1h3v.s4.a4b9081a0dfa from=translated src=- shape=ad7f8718 vocab=3f5b6aab
-/
theorem inj₁_nonempty {Y : Set β} (hY : Y.Nonempty) : (inj₁ Y : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image ir hY

/--
@isnad1 id=iff.0h4v.s5.c0da5bab92f0 from=translated src=- shape=ce8c1d66 vocab=948492dd
-/
theorem inj₀_subset_inj₀ {X X' : Set α} :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₀ X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact il_mem_inj₀.mp (h (il_mem_inj₀.mpr ha))
  · intro h t ht
    rw [inj₀, Set.mem_image] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact il_mem_inj₀.mpr (h ha)

/--
@isnad1 id=iff.0h4v.s5.13c1795df887 from=translated src=- shape=8527575a vocab=5afd2f84
-/
theorem inj₁_subset_inj₁ {Y Y' : Set β} :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₁ Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact ir_mem_inj₁.mp (h (ir_mem_inj₁.mpr hb))
  · intro h t ht
    rw [inj₁, Set.mem_image] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    exact ir_mem_inj₁.mpr (h hb)

/--
@isnad1 id=eq.1h4v.s4.ace0382a4702 from=translated src=- shape=e17419fc vocab=7deb30a1
-/
theorem inj₀_injective {X X' : Set α} (h : (inj₀ X : Set (Option (α ⊕ β))) = inj₀ X') : X = X' :=
  Set.Subset.antisymm (inj₀_subset_inj₀.mp h.subset) (inj₀_subset_inj₀.mp h.symm.subset)

/--
@isnad1 id=eq.1h4v.s4.be5354af6709 from=translated src=- shape=eb1bb39c vocab=8edd6702
-/
theorem inj₁_injective {Y Y' : Set β} (h : (inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y') : Y = Y' :=
  Set.Subset.antisymm (inj₁_subset_inj₁.mp h.subset) (inj₁_subset_inj₁.mp h.symm.subset)

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

/-- The master neighbourhood of the sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. -/
def sumMaster : Set (Option (α ⊕ β)) := insert none (inj₀ V₀.master ∪ inj₁ V₁.master)

variable {V₀ V₁}

/--
@isnad1 id=mem.0h4v.s5.c645f4821a9e from=translated src=- shape=93295cce vocab=7e57eefa
-/
@[simp] theorem none_mem_sumMaster : (none : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ :=
  Set.mem_insert _ _

/--
@isnad1 id=le.1h5v.s5.d551cf2586d0 from=translated src=- shape=d18f0721 vocab=99b5f691
-/
theorem inj₀_subset_sumMaster {X : Set α} (hX : V₀.mem X) :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ sumMaster V₀ V₁ := by
  intro t ht
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _ ?_))
  exact (inj₀_subset_inj₀.mpr (V₀.sub_master hX)) ht

/--
@isnad1 id=le.1h5v.s5.91cac6b0af47 from=translated src=- shape=e60c4e59 vocab=cb9397f2
-/
theorem inj₁_subset_sumMaster {Y : Set β} (hY : V₁.mem Y) :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ sumMaster V₀ V₁ := by
  intro t ht
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ ?_))
  exact (inj₁_subset_inj₁.mpr (V₁.sub_master hY)) ht

/--
@isnad1 id=eq.1h5v.s5.9c36f947a720 from=translated src=- shape=3bc58b97 vocab=b72fed3d
-/
theorem sumMaster_inter_inj₀ {X : Set α} (hX : V₀.mem X) :
    (sumMaster V₀ V₁ ∩ inj₀ X : Set (Option (α ⊕ β))) = inj₀ X :=
  Set.inter_eq_right.mpr (inj₀_subset_sumMaster hX)

/--
@isnad1 id=eq.1h5v.s5.3cff2282d5c3 from=translated src=- shape=988d2900 vocab=825a47aa
-/
theorem sumMaster_inter_inj₁ {Y : Set β} (hY : V₁.mem Y) :
    (sumMaster V₀ V₁ ∩ inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y :=
  Set.inter_eq_right.mpr (inj₁_subset_sumMaster hY)

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The *sum system* `𝒟₀ + 𝒟₁` over `{Λ} ∪
0Δ₀ ∪ 1Δ₁`,
under the standing assumption that no neighbourhood of `𝒟₀` or `𝒟₁` is empty. -/
def sum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem (Option (α ⊕ β)) where
  mem W := W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ W = inj₀ X) ∨ (∃ Y, V₁.mem Y ∧ W = inj₁ Y)
  master := sumMaster V₀ V₁
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact subset_rfl
    · exact inj₀_subset_sumMaster hX
    · exact inj₁_subset_sumMaster hY
  inter_mem := by
    -- every neighbourhood is non-empty, hence so is any consistency witness `Z`
    have hne : ∀ W, (W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ W = inj₀ X) ∨
        (∃ Y, V₁.mem Y ∧ W = inj₁ Y)) → (W : Set (Option (α ⊕ β))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨none, none_mem_sumMaster⟩
      · exact inj₀_nonempty (h₀ X hX)
      · exact inj₁_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumMaster_inter_inj₀ hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [sumMaster_inter_inj₁ hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₀ hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [inj₀_inter] at hZsub ⊢
        -- witness `Z ⊆ inj₀ (X ∩ X')`; `Z` non-empty forces it to be a left copy
        -- `inj₀ Z₀`
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₀
        · refine Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ₀ (inj₀_subset_inj₀.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          exact absurd (hZsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · rw [inj₀_inter_inj₁] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₁ hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
      · rw [Set.inter_comm, inj₀_inter_inj₁] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [inj₁_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₁
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          exact absurd (hZsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
        · refine Or.inr (Or.inr ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ₁ (inj₁_subset_inj₁.mp hZsub), rfl⟩)

/-! ### The injections `inᵢ` and projections `outᵢ`. -/

/--
@isnad1 id=injectiv.0h2v.s3.1fee5366f296 from=translated src=- shape=6fd4a341 vocab=7d60eca6
-/
theorem il_injective : Function.Injective (il : α → Option (α ⊕ β)) := by
  intro a a' h; simpa [il] using h

/--
@isnad1 id=injectiv.0h2v.s3.595b4f3a3485 from=translated src=- shape=dbf4a18b vocab=137f518b
-/
theorem ir_injective : Function.Injective (ir : β → Option (α ⊕ β)) := by
  intro b b' h; simpa [ir] using h

/--
@isnad1 id=eq.0h3v.s4.7273c9de2cb4 from=translated src=- shape=870885fb vocab=3e7abf8f
-/
@[simp] theorem il_preimage_inj₀ (X : Set α) :
    ((il : α → Option (α ⊕ β)) ⁻¹' inj₀ X) = X :=
  Set.preimage_image_eq X il_injective

/--
@isnad1 id=eq.0h3v.s4.799fe616fec4 from=translated src=- shape=b9f7cd64 vocab=452ffdce
-/
@[simp] theorem ir_preimage_inj₁ (Y : Set β) :
    ((ir : β → Option (α ⊕ β)) ⁻¹' inj₁ Y) = Y :=
  Set.preimage_image_eq Y ir_injective

/-- The left content `leftPart W ⊆ Δ₀` of a sum-neighbourhood `W`: the `0`-tagged
tokens of `W`,
*plus* all of `Δ₀` whenever `W` reaches into the right copy or the basepoint (so
non-left
neighbourhoods contribute only `Δ₀`, i.e. project to `⊥`). This is a genuine
(choice-free) function
of `W`. -/
def leftPart (V₀ : NeighborhoodSystem α) (W : Set (Option (α ⊕ β))) : Set α :=
  il ⁻¹' W ∪ {a | a ∈ V₀.master ∧ ((∃ b : β, ir b ∈ W) ∨ (none : Option (α ⊕ β)) ∈ W)}

/-- The right content `rightPart W ⊆ Δ₁`, symmetric to `leftPart`. -/
def rightPart (V₁ : NeighborhoodSystem β) (W : Set (Option (α ⊕ β))) : Set β :=
  ir ⁻¹' W ∪ {b | b ∈ V₁.master ∧ ((∃ a : α, il a ∈ W) ∨ (none : Option (α ⊕ β)) ∈ W)}

/--
@isnad1 id=iff.0h5v.s6.17f6ba293c11 from=translated src=- shape=933732dd vocab=9eb6f67f
-/
@[simp] theorem mem_leftPart {V₀ : NeighborhoodSystem α} {W : Set (Option (α ⊕ β))} {a : α} :
    a ∈ leftPart V₀ W ↔ il a ∈ W ∨ (a ∈ V₀.master ∧ ((∃ b : β, ir b ∈ W) ∨ none ∈ W)) := by
  simp only [leftPart, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]

/--
@isnad1 id=iff.0h5v.s6.2ea88bc39f23 from=translated src=- shape=b73f1f2f vocab=d732161d
-/
@[simp] theorem mem_rightPart {V₁ : NeighborhoodSystem β} {W : Set (Option (α ⊕ β))} {b : β} :
    b ∈ rightPart V₁ W ↔ ir b ∈ W ∨ (b ∈ V₁.master ∧ ((∃ a : α, il a ∈ W) ∨ none ∈ W)) := by
  simp only [rightPart, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]

/--
@isnad1 id=le.1h5v.s5.bb4631651490 from=translated src=- shape=26962271 vocab=33facb39
-/
theorem leftPart_mono (V₀ : NeighborhoodSystem α) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    leftPart V₀ W ⊆ leftPart V₀ W' := by
  intro a ha
  rw [mem_leftPart] at ha ⊢
  exact ha.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨b, hb⟩ => ⟨b, h hb⟩) (
    fun hn => h hn)⟩)

/--
@isnad1 id=le.1h5v.s5.f1329b7e7900 from=translated src=- shape=a738833e vocab=3afb8f03
-/
theorem rightPart_mono (V₁ : NeighborhoodSystem β) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    rightPart V₁ W ⊆ rightPart V₁ W' := by
  intro b hb
  rw [mem_rightPart] at hb ⊢
  exact hb.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨a, ha⟩ => ⟨a, h ha⟩) (
    fun hn => h hn)⟩)

/--
@isnad1 id=eq.0h4v.s4.dc1997e3df5f from=translated src=- shape=3e06ed28 vocab=d83ac8fa
-/
@[simp] theorem leftPart_inj₀ (V₀ : NeighborhoodSystem α) (X : Set α) :
    leftPart V₀ (inj₀ X : Set (Option (α ⊕ β))) = X := by
  ext a
  simp_all

/--
@isnad1 id=eq.0h4v.s4.6a42ca5c3658 from=translated src=- shape=487efdce vocab=fd0edc58
-/
@[simp] theorem rightPart_inj₁ (V₁ : NeighborhoodSystem β) (Y : Set β) :
    rightPart V₁ (inj₁ Y : Set (Option (α ⊕ β))) = Y := by
  ext b
  simp_all

/--
@isnad1 id=eq.0h4v.s4.3df34f24e6e4 from=translated src=- shape=0720beb2 vocab=e7878b6c
-/
theorem leftPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    leftPart V₀ (sumMaster V₀ V₁) = V₀.master := by
  ext a
  simp only [mem_leftPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (il a : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [il])
      · simp_all
    · exact h
  · intro ha; exact Or.inr ha

/--
@isnad1 id=eq.1h4v.s4.e23bee71661b from=translated src=- shape=42e13121 vocab=0c616ef1
-/
theorem leftPart_inj₁ (V₀ : NeighborhoodSystem α) {Y : Set β} (hY : Y.Nonempty) :
    leftPart V₀ (inj₁ Y : Set (Option (α ⊕ β))) = V₀.master := by
  ext a
  simp only [mem_leftPart, il_mem_inj₁, none_mem_inj₁, or_false, false_or]
  constructor
  · rintro ⟨ha, _⟩; exact ha
  · intro ha; obtain ⟨b, hb⟩ := hY; exact ⟨ha, ⟨b, ir_mem_inj₁.mpr hb⟩⟩

/--
@isnad1 id=eq.0h4v.s4.236d251591bd from=translated src=- shape=30367061 vocab=ced5bf85
-/
theorem rightPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    rightPart V₁ (sumMaster V₀ V₁) = V₁.master := by
  ext b
  simp only [mem_rightPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (ir b : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [ir])
      · simp_all
    · exact h
  · intro hb; exact Or.inr hb

/--
@isnad1 id=eq.1h4v.s4.fe112e5c65ea from=translated src=- shape=83885d62 vocab=20ef4263
-/
theorem rightPart_inj₀ (V₁ : NeighborhoodSystem β) {X : Set α} (hX : X.Nonempty) :
    rightPart V₁ (inj₀ X : Set (Option (α ⊕ β))) = V₁.master := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₀, none_mem_inj₀, or_false, false_or]
  constructor
  · rintro ⟨hb, _⟩; exact hb
  · intro hb; obtain ⟨a, ha⟩ := hX; exact ⟨hb, ⟨a, il_mem_inj₀.mpr ha⟩⟩

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/--
@isnad1 id=mem.3h5v.s5.be6e70ccdc61 from=translated src=- shape=9bd4112b vocab=52617f22
-/
theorem leftPart_mem {W : Set (Option (α ⊕ β))} (hW : (sum V₀ V₁ h₀ h₁).mem W) :
    V₀.mem (leftPart V₀ W) := by
  rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rw [leftPart_sumMaster]; exact V₀.master_mem
  · rw [leftPart_inj₀]; exact hX
  · rw [leftPart_inj₁ V₀ (h₁ Y hY)]; exact V₀.master_mem

/--
@isnad1 id=mem.3h5v.s5.e181ef96489a from=translated src=- shape=971d2acf vocab=27a158d6
-/
theorem rightPart_mem {W : Set (Option (α ⊕ β))} (hW : (sum V₀ V₁ h₀ h₁).mem W) :
    V₁.mem (rightPart V₁ W) := by
  rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rw [rightPart_sumMaster]; exact V₁.master_mem
  · rw [rightPart_inj₀ V₁ (h₀ X hX)]; exact V₁.master_mem
  · rw [rightPart_inj₁]; exact hY

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left injection `in₀ : 𝒟₀ → 𝒟₀ +
𝒟₁`,
`X (in₀) W ↔ 0X ⊆ W`. -/
def inMap₀ : ApproximableMap V₀ (sum V₀ V₁ h₀ h₁) where
  rel X W := V₀.mem X ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The right injection `in₁ : 𝒟₁ → 𝒟₀ +
𝒟₁`. -/
def inMap₁ : ApproximableMap V₁ (sum V₀ V₁ h₀ h₁) where
  rel Y W := V₁.mem Y ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₁ Y ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₁.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
  inter_right := by
    rintro Y W W' ⟨hY, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hY, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro Y Y' W W' ⟨_, _, hsub⟩ hY'Y hWW' hY' hW'
    exact ⟨hY', hW', (inj₁_subset_inj₁.mpr hY'Y).trans (hsub.trans hWW')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left projection `out₀ : 𝒟₀ + 𝒟₁ →
𝒟₀`,
`W (out₀) X ↔ leftPart W ⊆ X` (right/basepoint neighbourhoods relate only to
`Δ₀`). -/
def outMap₀ : ApproximableMap (sum V₀ V₁ h₀ h₁) V₀ where
  rel W X := (sum V₀ V₁ h₀ h₁).mem W ∧ V₀.mem X ∧ leftPart V₀ W ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V₀.inter_mem hX hX' (leftPart_mem hW) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', (leftPart_mono V₀ hW'W).trans (hsub.trans hXX')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The right projection `out₁ : 𝒟₀ + 𝒟₁ →
𝒟₁`. -/
def outMap₁ : ApproximableMap (sum V₀ V₁ h₀ h₁) V₁ where
  rel W Y := (sum V₀ V₁ h₀ h₁).mem W ∧ V₁.mem Y ∧ rightPart V₁ W ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W Y Y' ⟨hW, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hW, V₁.inter_mem hY hY' (rightPart_mem hW) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W' Y Y' ⟨_, _, hsub⟩ hW'W hYY' hW' hY'
    exact ⟨hW', hY', (rightPart_mono V₁ hW'W).trans (hsub.trans hYY')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₀ ∘ in₀ = I_{𝒟₀}`.
@isnad1 id=eq.2h4v.s6.c92594e5defb from=translated src=- shape=1c45ab07 vocab=7e1c9a81
-/
theorem outMap₀_comp_inMap₀ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₀ = idMap V₀ := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, hZ, ?_⟩
    have hXW : X ⊆ leftPart V₀ W := by
      intro a ha
      rw [mem_leftPart]; exact Or.inl (hinj (il_mem_inj₀.mpr ha))
    exact hXW.trans hsub
  · rintro ⟨hX, hZ, hXZ⟩
    refine ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), hZ, ?_⟩
    rw [leftPart_inj₀]; exact hXZ

/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₁ ∘ in₁ = I_{𝒟₁}`.
@isnad1 id=eq.2h4v.s6.f1965883f9d0 from=translated src=- shape=40065554 vocab=387f1e0c
-/
theorem outMap₁_comp_inMap₁ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₁ = idMap V₁ := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, hZ, ?_⟩
    have hYW : Y ⊆ rightPart V₁ W := by
      intro b hb
      rw [mem_rightPart]; exact Or.inl (hinj (ir_mem_inj₁.mpr hb))
    exact hYW.trans hsub
  · rintro ⟨hY, hZ, hYZ⟩
    refine ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), hZ, ?_⟩
    rw [rightPart_inj₁]; exact hYZ

end Domain.Neighborhood
