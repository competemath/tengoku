/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytification.RET.ES.Codim2.ContactOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Blowing up families of graphs along `t = 0`

Write the points of `(E × ℂ) × ℂ` as `((y, t), w)`. For a family `ψ` of holomorphic functions on
`V ⊆ E × ℂ`, let `graphs V ψ` be the union of the graphs `w = ψᵢ(y, t)` over `V` and
`vertical V` the hyperplane `t = 0` over `V`. After Puiseux base change, a hypersurface near a
point of `t = 0` is `graphs V ψ` for a family whose members are disjoint over `t ≠ 0`, hence a
contact family (`Codim2.IsContactFamily`): `ψᵢ - ψⱼ = t ^ kᵢⱼ uᵢⱼ` with `uᵢⱼ` without zeros
(`Codim2.isContactFamily_of_injective`).

The blow-up of the codimension two centre `{t = 0, w = φ(y, t)}` is covered by two charts,
`Codim2.chart₁ φ : (y, t, v) ↦ (y, t, φ(y, t) + t v)` and
`Codim2.chart₂ φ : (y, s, v') ↦ (y, s v', φ(y, s v') + s)`, which agree on the overlap
(`Codim2.chart₂_eq_chart₁`) and are biholomorphic off the exceptional divisor (`t = 0`,
resp. `s = 0`). If all members of `ψ` pass through the centre, i.e. `ψᵢ = φ + t χᵢ`, then the
preimage of `graphs V ψ ∪ vertical V` under `chart₁ φ` is `graphs V χ ∪ vertical V`
(`Codim2.chart₁_mem_graphs_iff`), and under `chart₂ φ` it is `{s = 0}`, resp. `{s v' = 0}`, near
`v' = 0` (`Codim2.eventually_chart₂_mem_graphs_iff`).

For `φ = ψᵢ₀` the strict transforms `χᵢ = (ψᵢ - ψᵢ₀) / t` again form a contact family, with contact
orders `kᵢⱼ - 1` (`Codim2.IsContactFamily.blowup`). Near a point of `t = 0` only the members
through that point matter (`Codim2.IsContactFamily.eventually_mem_graphs_iff`), and those have
pairwise contact order `≥ 1` (`Codim2.IsContactFamily.one_le_of_eq`). So the maximal contact
order of the members through a point drops by one under each blow-up, and after finitely many
blow-ups at most one member passes through each point: the total transform is then locally
`{t = 0} ∪ {v = χ(y, t)}`, which the shear `Codim2.shear χ` takes to the normal crossings divisor
`{t v = 0}`.

## Main definitions

- `Codim2.graphs V ψ`, `Codim2.vertical V`: the union of graphs and the hyperplane `t = 0`.
- `Codim2.IsContactFamily V ψ k`: `ψᵢ - ψⱼ = t ^ kᵢⱼ` times a function without zeros.
- `Codim2.chart₁ φ`, `Codim2.chart₂ φ`: the two charts of the blow-up of `{t = 0, w = φ}`, with
  inverses `Codim2.chart₁Inv φ`, `Codim2.chart₂Inv φ` off the exceptional divisor.
- `Codim2.shear χ`: the biholomorphism `(y, t, v) ↦ (y, t, v - χ(y, t))`.

## Main results

- `Codim2.isContactFamily_of_injective`: families disjoint over `t ≠ 0` are contact families.
- `Codim2.chart₁_mem_graphs_iff`, `Codim2.chart₂_mem_graphs_iff`: total transforms in the charts.
- `Codim2.IsContactFamily.blowup`: strict transforms form a contact family of lower orders.
- `Codim2.IsContactFamily.eventually_mem_graphs_iff`: localisation to the members through a
  point.
-/

open Set Filter Metric Topology

namespace Codim2

variable {E : Type*} {ι : Type*}

/-! ### Graphs and the hyperplane `t = 0` -/

/-- The union over `V` of the graphs `w = ψᵢ(y, t)`. -/
def graphs (V : Set (E × ℂ)) (ψ : ι → E × ℂ → ℂ) : Set ((E × ℂ) × ℂ) :=
  {x | x.1 ∈ V ∧ ∃ i, x.2 = ψ i x.1}

/-- The hyperplane `t = 0` over `V`. -/
def vertical (V : Set (E × ℂ)) : Set ((E × ℂ) × ℂ) :=
  {x | x.1 ∈ V ∧ x.1.2 = 0}

lemma mem_graphs {V : Set (E × ℂ)} {ψ : ι → E × ℂ → ℂ} {x : (E × ℂ) × ℂ} :
    x ∈ graphs V ψ ↔ x.1 ∈ V ∧ ∃ i, x.2 = ψ i x.1 :=
  Iff.rfl

lemma mem_vertical {V : Set (E × ℂ)} {x : (E × ℂ) × ℂ} :
    x ∈ vertical V ↔ x.1 ∈ V ∧ x.1.2 = 0 :=
  Iff.rfl

/-! ### Contact families -/

section Contact

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A family `ψ` of holomorphic functions on `V` is a *contact family* with orders `k` if for
`i ≠ j` the difference `ψᵢ - ψⱼ` is `t ^ kᵢⱼ` times a holomorphic function without zeros on
`V`. -/
structure IsContactFamily (V : Set (E × ℂ)) (ψ : ι → E × ℂ → ℂ) (k : ι → ι → ℕ) : Prop where
  differentiableOn (i : ι) : DifferentiableOn ℂ (ψ i) V
  exists_unit (i j : ι) (hij : i ≠ j) : ∃ u : E × ℂ → ℂ, DifferentiableOn ℂ u V ∧
    (∀ z ∈ V, u z ≠ 0) ∧ ∀ z ∈ V, ψ i z - ψ j z = z.2 ^ k i j * u z

namespace IsContactFamily

variable {V : Set (E × ℂ)} {ψ : ι → E × ℂ → ℂ} {k : ι → ι → ℕ}

lemma mono (h : IsContactFamily V ψ k) {W : Set (E × ℂ)} (hWV : W ⊆ V) :
    IsContactFamily W ψ k where
  differentiableOn i := (h.differentiableOn i).mono hWV
  exists_unit i j hij := by
    obtain ⟨u, hu, hu0, hψu⟩ := h.exists_unit i j hij
    exact ⟨u, hu.mono hWV, fun z hz ↦ hu0 z (hWV hz), fun z hz ↦ hψu z (hWV hz)⟩

lemma comp (h : IsContactFamily V ψ k) {ι' : Type*} {e : ι' → ι} (he : Function.Injective e) :
    IsContactFamily V (fun i ↦ ψ (e i)) (fun i j ↦ k (e i) (e j)) where
  differentiableOn i := h.differentiableOn (e i)
  exists_unit i j hij := h.exists_unit (e i) (e j) (he.ne hij)

/-- Two members of a contact family agree at a point of `t = 0` if and only if their contact
order is positive. -/
lemma eq_iff_one_le (h : IsContactFamily V ψ k) {i j : ι} (hij : i ≠ j) {z : E × ℂ}
    (hz : z ∈ V) (hz0 : z.2 = 0) : ψ i z = ψ j z ↔ 1 ≤ k i j := by
  obtain ⟨u, -, hu0, hψu⟩ := h.exists_unit i j hij
  rw [← sub_eq_zero, hψu z hz, hz0, mul_eq_zero, pow_eq_zero_iff', Nat.one_le_iff_ne_zero]
  simp [hu0 z hz]

lemma one_le_of_eq (h : IsContactFamily V ψ k) {i j : ι} (hij : i ≠ j) {z : E × ℂ}
    (hz : z ∈ V) (hz0 : z.2 = 0) (he : ψ i z = ψ j z) : 1 ≤ k i j :=
  (h.eq_iff_one_le hij hz hz0).1 he

/-- Members of a contact family are disjoint over `t ≠ 0`. -/
lemma ne_of_ne_zero (h : IsContactFamily V ψ k) {i j : ι} (hij : i ≠ j) {z : E × ℂ}
    (hz : z ∈ V) (hz0 : z.2 ≠ 0) : ψ i z ≠ ψ j z := by
  obtain ⟨u, -, hu0, hψu⟩ := h.exists_unit i j hij
  rw [ne_eq, ← sub_eq_zero, hψu z hz]
  exact mul_ne_zero (pow_ne_zero _ hz0) (hu0 z hz)

/-- **Localisation.** Near a point `(z₀, w₀)` with `z₀ ∈ V`, only the members of the family
passing through it contribute to `graphs V ψ`. -/
theorem eventually_mem_graphs_iff [Finite ι] (h : IsContactFamily V ψ k) (hV : IsOpen V)
    {z₀ : E × ℂ} (hz₀ : z₀ ∈ V) (w₀ : ℂ) :
    ∀ᶠ x in 𝓝 (z₀, w₀), x ∈ graphs V ψ ↔
      x ∈ graphs V (fun i : {i // ψ i z₀ = w₀} ↦ ψ i) := by
  have hev (i : ι) (hi : ψ i z₀ ≠ w₀) : ∀ᶠ x in 𝓝 (z₀, w₀), x.2 ≠ ψ i x.1 := by
    have hc : ContinuousAt (fun x : (E × ℂ) × ℂ ↦ x.2 - ψ i x.1) (z₀, w₀) :=
      continuousAt_snd.sub (((h.differentiableOn i).continuousOn.continuousAt
        (hV.mem_nhds hz₀)).comp continuousAt_fst)
    filter_upwards [hc.eventually_ne (sub_ne_zero.2 (Ne.symm hi))] with x hx
    exact sub_ne_zero.1 hx
  have hall : ∀ᶠ x in 𝓝 (z₀, w₀), ∀ i, ψ i z₀ ≠ w₀ → x.2 ≠ ψ i x.1 :=
    eventually_all.2 fun i ↦ by
      by_cases hi : ψ i z₀ = w₀
      · exact Eventually.of_forall fun x h ↦ absurd hi h
      · exact (hev i hi).mono fun x hx _ ↦ hx
  filter_upwards [hall] with x hx
  refine ⟨fun ⟨hxV, i, hi⟩ ↦ ⟨hxV, ?_⟩, fun ⟨hxV, i, hi⟩ ↦ ⟨hxV, i, hi⟩⟩
  by_cases hi' : ψ i z₀ = w₀
  · exact ⟨⟨i, hi'⟩, hi⟩
  · exact absurd hi (hx i hi')

/-- **Strict transforms.** Let `ψ` be a contact family on an open `V` all of whose members pass
through `{t = 0, w = ψᵢ₀}`, i.e. all contact orders are positive. Then `ψᵢ = ψᵢ₀ + t χᵢ` for a
contact family `χ` with contact orders `kᵢⱼ - 1` and `χᵢ₀ = 0`. -/
theorem blowup (h : IsContactFamily V ψ k) (hV : IsOpen V) (i₀ : ι)
    (hk : ∀ i j, i ≠ j → 1 ≤ k i j) :
    ∃ χ : ι → E × ℂ → ℂ, (∀ i, ∀ z ∈ V, ψ i z = ψ i₀ z + z.2 * χ i z) ∧
      (∀ z ∈ V, χ i₀ z = 0) ∧ IsContactFamily V χ fun i j ↦ k i j - 1 := by
  classical
  have hdiv (i : ι) : ∃ χ : E × ℂ → ℂ, DifferentiableOn ℂ χ V ∧
      (∀ z ∈ V, ψ i z - ψ i₀ z = z.2 * χ z) ∧ (i = i₀ → ∀ z ∈ V, χ z = 0) := by
    by_cases hi : i = i₀
    · subst hi
      exact ⟨0, differentiableOn_const 0, fun z _ ↦ by simp, fun _ _ _ ↦ rfl⟩
    obtain ⟨u, hu, -, hψu⟩ := h.exists_unit i i₀ hi
    refine ⟨fun z ↦ z.2 ^ (k i i₀ - 1) * u z, (differentiableOn_snd.pow _).mul hu,
      fun z hz ↦ ?_, fun h ↦ absurd h hi⟩
    rw [hψu z hz, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hk i i₀ hi)]
  choose χ hχ hψχ hχ₀ using hdiv
  refine ⟨χ, fun i z hz ↦ by rw [← hψχ i z hz, add_sub_cancel], hχ₀ i₀ rfl, hχ, ?_⟩
  intro i j hij
  obtain ⟨u, hu, hu0, hψu⟩ := h.exists_unit i j hij
  refine ⟨u, hu, hu0, ?_⟩
  have hZ := interior_inter_preimage_snd_zero V
  refine EqOn.of_eqOn_diff_zero hV hZ ((hχ i).sub (hχ j)).continuousOn
    ((differentiableOn_snd.pow _).mul hu).continuousOn fun z hz ↦ ?_
  have hz0 : z.2 ≠ 0 := hz.2
  have h₁ : z.2 * (χ i z - χ j z) = z.2 * (z.2 ^ (k i j - 1) * u z) := by
    rw [mul_sub, ← hψχ i z hz.1, ← hψχ j z hz.1, sub_sub_sub_cancel_right, hψu z hz.1,
      ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hk i j hij)]
  exact mul_left_cancel₀ hz0 h₁

end IsContactFamily

/-- **Branches disjoint off `t = 0` form a contact family.** Let `G ⊆ E` be open and
preconnected and let `ψ` be a family of holomorphic functions on `G × Δ_r` which is injective at
every point with `t ≠ 0`. Then `ψ` is a contact family on `G × Δ_r`. -/
theorem isContactFamily_of_injective [FiniteDimensional ℂ E] {G : Set E} (hGo : IsOpen G)
    (hG : IsPreconnected G) {r : ℝ} {ψ : ι → E × ℂ → ℂ}
    (hψ : ∀ i, DifferentiableOn ℂ (ψ i) (G ×ˢ ball 0 r))
    (hinj : ∀ z ∈ G ×ˢ ball (0 : ℂ) r, z.2 ≠ 0 → Function.Injective fun i ↦ ψ i z) :
    ∃ k : ι → ι → ℕ, IsContactFamily (G ×ˢ ball 0 r) ψ k := by
  have h (i j : ι) (hij : i ≠ j) := exists_eq_pow_mul hGo hG ((hψ i).sub (hψ j))
    fun z hz hz0 he ↦ hij (hinj z hz hz0 (sub_eq_zero.1 he))
  choose! k u hu hu0 hψu using h
  exact ⟨k, hψ, fun i j hij ↦ ⟨u i j, hu i j hij, hu0 i j hij, hψu i j hij⟩⟩

end Contact

/-! ### The charts of the blow-up -/

/-- The first chart `(y, t, v) ↦ (y, t, φ(y, t) + t v)` of the blow-up of `{t = 0, w = φ}`. -/
def chart₁ (φ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : (E × ℂ) × ℂ :=
  (x.1, φ x.1 + x.1.2 * x.2)

/-- The inverse `(y, t, w) ↦ (y, t, (w - φ(y, t)) / t)` of `Codim2.chart₁ φ` off `t = 0`. -/
noncomputable def chart₁Inv (φ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : (E × ℂ) × ℂ :=
  (x.1, (x.2 - φ x.1) / x.1.2)

/-- The second chart `(y, s, v') ↦ (y, s v', φ(y, s v') + s)` of the blow-up of
`{t = 0, w = φ}`. -/
def chart₂ (φ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : (E × ℂ) × ℂ :=
  ((x.1.1, x.1.2 * x.2), φ (x.1.1, x.1.2 * x.2) + x.1.2)

/-- The inverse `(y, t, w) ↦ (y, w - φ(y, t), t / (w - φ(y, t)))` of `Codim2.chart₂ φ` off
`w = φ`. -/
noncomputable def chart₂Inv (φ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : (E × ℂ) × ℂ :=
  ((x.1.1, x.2 - φ x.1), x.1.2 / (x.2 - φ x.1))

/-- The shear `(y, t, v) ↦ (y, t, v - χ(y, t))`, which takes the graph of `χ` to `v = 0`. -/
def shear (χ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : (E × ℂ) × ℂ :=
  (x.1, x.2 - χ x.1)

variable (φ : E × ℂ → ℂ)

@[simp]
lemma chart₁_fst (x : (E × ℂ) × ℂ) : (chart₁ φ x).1 = x.1 :=
  rfl

@[simp]
lemma chart₁_snd (x : (E × ℂ) × ℂ) : (chart₁ φ x).2 = φ x.1 + x.1.2 * x.2 :=
  rfl

lemma chart₁_chart₁Inv {x : (E × ℂ) × ℂ} (hx : x.1.2 ≠ 0) : chart₁ φ (chart₁Inv φ x) = x := by
  refine Prod.ext rfl ?_
  simp only [chart₁, chart₁Inv]
  rw [mul_div_cancel₀ _ hx, add_sub_cancel]

lemma chart₁Inv_chart₁ {x : (E × ℂ) × ℂ} (hx : x.1.2 ≠ 0) : chart₁Inv φ (chart₁ φ x) = x := by
  refine Prod.ext rfl ?_
  simp only [chart₁, chart₁Inv]
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hx]

lemma chart₂_chart₂Inv {x : (E × ℂ) × ℂ} (hx : x.2 ≠ φ x.1) : chart₂ φ (chart₂Inv φ x) = x := by
  have hx' : x.2 - φ x.1 ≠ 0 := sub_ne_zero.2 hx
  have h₁ : ((x.1.1, (x.2 - φ x.1) * (x.1.2 / (x.2 - φ x.1))) : E × ℂ) = x.1 :=
    Prod.ext rfl (mul_div_cancel₀ _ hx')
  simp only [chart₂, chart₂Inv, h₁, add_sub_cancel]

lemma chart₂Inv_chart₂ {x : (E × ℂ) × ℂ} (hx : x.1.2 ≠ 0) : chart₂Inv φ (chart₂ φ x) = x := by
  simp only [chart₂, chart₂Inv, add_sub_cancel_left, mul_div_cancel_left₀ _ hx]

/-- The two charts agree on their overlap: `v' = v⁻¹`, `s = t v`. -/
lemma chart₂_eq_chart₁ {x : (E × ℂ) × ℂ} (hx : x.2 ≠ 0) :
    chart₂ φ ((x.1.1, x.1.2 * x.2), x.2⁻¹) = chart₁ φ x := by
  simp only [chart₂, chart₁, mul_assoc, mul_inv_cancel₀ hx, mul_one]

lemma chart₂_fst (x : (E × ℂ) × ℂ) : (chart₂ φ x).1 = (x.1.1, x.1.2 * x.2) :=
  rfl

lemma shear_injective (χ : E × ℂ → ℂ) : Function.Injective (shear χ) := by
  intro x x' h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  rw [h₁] at h₂
  exact Prod.ext h₁ (sub_left_inj.1 h₂)

variable {φ}

section Differentiable

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma differentiableOn_chart₁ {V : Set (E × ℂ)} (hφ : DifferentiableOn ℂ φ V) :
    DifferentiableOn ℂ (chart₁ φ) (Prod.fst ⁻¹' V) := by
  have h₁ : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ φ x.1) (Prod.fst ⁻¹' V) :=
    hφ.comp differentiableOn_fst fun _ hx ↦ hx
  exact differentiableOn_fst.prodMk (h₁.add
    (by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.1.2 * x.2).differentiableOn)

lemma differentiableOn_chart₁Inv {V : Set (E × ℂ)} (hφ : DifferentiableOn ℂ φ V) :
    DifferentiableOn ℂ (chart₁Inv φ) (Prod.fst ⁻¹' V ∩ {x | x.1.2 ≠ 0}) := by
  have h₁ : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ x.2 - φ x.1)
      (Prod.fst ⁻¹' V ∩ {x | x.1.2 ≠ 0}) :=
    (by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.2).differentiableOn.sub
      (hφ.comp differentiableOn_fst fun _ hx ↦ hx.1)
  have h₂ : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ (x.1.2)⁻¹)
      (Prod.fst ⁻¹' V ∩ {x | x.1.2 ≠ 0}) :=
    (by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.1.2).differentiableOn.inv
      fun _ hx ↦ hx.2
  refine differentiableOn_fst.prodMk ?_
  simp only [div_eq_mul_inv]
  exact h₁.mul h₂

lemma differentiableOn_chart₂ {V : Set (E × ℂ)} (hφ : DifferentiableOn ℂ φ V) :
    DifferentiableOn ℂ (chart₂ φ) {x | (x.1.1, x.1.2 * x.2) ∈ V} := by
  have hm : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ ((x.1.1, x.1.2 * x.2) : E × ℂ) := by
    fun_prop
  have h₁ : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ φ (x.1.1, x.1.2 * x.2))
      {x | (x.1.1, x.1.2 * x.2) ∈ V} :=
    hφ.comp hm.differentiableOn fun _ hx ↦ hx
  exact hm.differentiableOn.prodMk (h₁.add
    (by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.1.2).differentiableOn)

lemma differentiableOn_chart₂Inv {V : Set (E × ℂ)} (hφ : DifferentiableOn ℂ φ V) :
    DifferentiableOn ℂ (chart₂Inv φ) (Prod.fst ⁻¹' V ∩ {x | x.2 ≠ φ x.1}) := by
  have hs : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ x.2 - φ x.1)
      (Prod.fst ⁻¹' V ∩ {x | x.2 ≠ φ x.1}) :=
    (by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.2).differentiableOn.sub
      (hφ.comp differentiableOn_fst fun _ hx ↦ hx.1)
  have hi : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ (x.2 - φ x.1)⁻¹)
      (Prod.fst ⁻¹' V ∩ {x | x.2 ≠ φ x.1}) :=
    hs.inv fun _ hx ↦ sub_ne_zero.2 hx.2
  refine ((by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.1.1).differentiableOn.prodMk
    hs).prodMk ?_
  simp only [div_eq_mul_inv]
  exact (by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.1.2).differentiableOn.mul hi

lemma differentiableOn_shear {χ : E × ℂ → ℂ} {V : Set (E × ℂ)} (hχ : DifferentiableOn ℂ χ V) :
    DifferentiableOn ℂ (shear χ) (Prod.fst ⁻¹' V) :=
  differentiableOn_fst.prodMk
    ((by fun_prop : Differentiable ℂ fun x : (E × ℂ) × ℂ ↦ x.2).differentiableOn.sub
      (hχ.comp differentiableOn_fst fun _ hx ↦ hx))

end Differentiable

/-! ### Total transforms -/

variable {V : Set (E × ℂ)} {ψ χ : ι → E × ℂ → ℂ}

lemma chart₁_mem_vertical_iff {x : (E × ℂ) × ℂ} : chart₁ φ x ∈ vertical V ↔ x ∈ vertical V :=
  Iff.rfl

/-- **The total transform in the first chart.** If `ψᵢ = φ + t χᵢ` on `V` for all `i`, then
`chart₁ φ` pulls `graphs V ψ` back to `graphs V χ ∪ vertical V`. -/
theorem chart₁_mem_graphs_iff [Nonempty ι] (hχ : ∀ i, ∀ z ∈ V, ψ i z = φ z + z.2 * χ i z)
    {x : (E × ℂ) × ℂ} : chart₁ φ x ∈ graphs V ψ ↔ x ∈ graphs V χ ∨ x ∈ vertical V := by
  simp only [mem_graphs, mem_vertical, chart₁_fst, chart₁_snd]
  constructor
  · rintro ⟨hx, i, hi⟩
    rw [hχ i _ hx, add_right_inj] at hi
    rcases mul_eq_mul_left_iff.1 hi with h | h
    · exact Or.inl ⟨hx, i, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, i, hi⟩ | ⟨hx, h0⟩)
    · exact ⟨hx, i, by rw [hχ i _ hx, hi]⟩
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨hx, i, by rw [hχ i _ hx, h0, zero_mul, zero_mul]⟩

lemma chart₂_mem_vertical_iff {x : (E × ℂ) × ℂ} :
    chart₂ φ x ∈ vertical V ↔ (x.1.1, x.1.2 * x.2) ∈ V ∧ (x.1.2 = 0 ∨ x.2 = 0) := by
  simp only [mem_vertical, chart₂_fst, mul_eq_zero]

/-- **The total transform in the second chart.** If `ψᵢ = φ + t χᵢ` on `V` for all `i`, then
`chart₂ φ` pulls `graphs V ψ` back to `{s = 0} ∪ ⋃ᵢ {v' χᵢ(y, s v') = 1}`. -/
theorem chart₂_mem_graphs_iff [Nonempty ι] (hχ : ∀ i, ∀ z ∈ V, ψ i z = φ z + z.2 * χ i z)
    {x : (E × ℂ) × ℂ} : chart₂ φ x ∈ graphs V ψ ↔ (x.1.1, x.1.2 * x.2) ∈ V ∧
      (x.1.2 = 0 ∨ ∃ i, x.2 * χ i (x.1.1, x.1.2 * x.2) = 1) := by
  simp only [mem_graphs, chart₂_fst]
  refine and_congr_right fun hx ↦ ?_
  simp only [chart₂, hχ _ _ hx, add_right_inj]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hs : x.1.2 = 0
    · exact Or.inl hs
    · refine Or.inr ⟨i, mul_left_cancel₀ hs ?_⟩
      rw [mul_one, ← mul_assoc]
      exact hi.symm
  · rintro (hs | ⟨i, hi⟩)
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, by simp [hs]⟩
    · exact ⟨i, by rw [mul_assoc, hi, mul_one]⟩

section Topology

variable [NormedAddCommGroup E]

/-- Near the point `v' = 0` of the exceptional divisor over `z₀ = (y₀, 0)`, the preimage of
`graphs V ψ` under `chart₂ φ` is the exceptional divisor `s = 0`. -/
theorem eventually_chart₂_mem_graphs_iff [Nonempty ι] [Finite ι] (hV : IsOpen V)
    (hχ : ∀ i, ∀ z ∈ V, ψ i z = φ z + z.2 * χ i z) (hχc : ∀ i, ContinuousOn (χ i) V)
    {y₀ : E} (hy₀ : (y₀, 0) ∈ V) :
    ∀ᶠ x in 𝓝 (((y₀, 0), 0) : (E × ℂ) × ℂ), (chart₂ φ x ∈ graphs V ψ ↔ x.1.2 = 0) ∧
      (x.1.1, x.1.2 * x.2) ∈ V := by
  have hm : Continuous fun x : (E × ℂ) × ℂ ↦ ((x.1.1, x.1.2 * x.2) : E × ℂ) := by fun_prop
  have hm₀ : ((((y₀, 0), 0) : (E × ℂ) × ℂ).1.1, (((y₀, 0), 0) : (E × ℂ) × ℂ).1.2 *
      (((y₀, 0), 0) : (E × ℂ) × ℂ).2) = (y₀, 0) := by simp
  have hmem : ∀ᶠ x in 𝓝 (((y₀, 0), 0) : (E × ℂ) × ℂ), (x.1.1, x.1.2 * x.2) ∈ V :=
    hm.continuousAt.preimage_mem_nhds (by rw [hm₀]; exact hV.mem_nhds hy₀)
  have hlt (i : ι) : ∀ᶠ x in 𝓝 (((y₀, 0), 0) : (E × ℂ) × ℂ),
      ‖x.2 * χ i (x.1.1, x.1.2 * x.2)‖ < 1 := by
    have hc : ContinuousAt (fun x : (E × ℂ) × ℂ ↦ x.2 * χ i (x.1.1, x.1.2 * x.2))
        ((y₀, 0), 0) := by
      refine continuousAt_snd.mul ?_
      refine ContinuousAt.comp (f := fun x : (E × ℂ) × ℂ ↦ ((x.1.1, x.1.2 * x.2) : E × ℂ))
        ?_ hm.continuousAt
      rw [hm₀]
      exact (hχc i).continuousAt (hV.mem_nhds hy₀)
    exact hc.norm.eventually (gt_mem_nhds (by simp))
  filter_upwards [hmem, eventually_all.2 hlt] with x hx hlt
  refine ⟨?_, hx⟩
  rw [chart₂_mem_graphs_iff hχ, and_iff_right hx]
  refine or_iff_left fun ⟨i, hi⟩ ↦ ?_
  have := hlt i
  rw [hi, norm_one] at this
  exact lt_irrefl _ this

end Topology

/-- The shear by `χ` takes the graph of `χ` to the hyperplane `v = 0`. -/
lemma mem_graphs_unique_iff {χ : E × ℂ → ℂ} {x : (E × ℂ) × ℂ} :
    x ∈ graphs V (fun _ : Unit ↦ χ) ↔ x.1 ∈ V ∧ (shear χ x).2 = 0 := by
  simp [mem_graphs, shear, sub_eq_zero]

/-- A family through a point of `t = 0` with at most one member: near that point, `graphs V ψ`
is the graph of that member or empty. -/
lemma mem_graphs_iff_of_subsingleton [Subsingleton ι] {i : ι} {x : (E × ℂ) × ℂ} :
    x ∈ graphs V ψ ↔ x.1 ∈ V ∧ (shear (ψ i) x).2 = 0 := by
  simp only [mem_graphs, shear, sub_eq_zero]
  exact and_congr_right fun _ ↦ ⟨fun ⟨j, hj⟩ ↦ Subsingleton.elim j i ▸ hj, fun h ↦ ⟨i, h⟩⟩

end Codim2
