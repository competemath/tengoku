/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import Tengoku.LeanPool.LeanPool.DemazureProduct.Submodular
import Tengoku.LeanPool.LeanPool.DemazureProduct.ReducedProducts
public import Tengoku

/-! # Reduction theorems

This file formalizes the main theorems from the introduction of
[An extended Demazure product](https://arxiv.org/abs/2206.14227): Theorem B
(`thm:starGreedy`) characterizes `α ⋆ β` as a greedy maximum, and Theorem C
(`thm:reduce`) reduces inequalities `α ⋆ β ≥ γ` to equalities of reduced products.
It corresponds roughly to Section 6 of the paper. -/

@[expose] public section

namespace LeanPool.DemazureProduct

namespace Reduction

open AspPerm

/-! ### Bookkeeping helpers -/

/-! ### Theorem B: greedy characterization of `⋆` -/

/-! ### Theorem C: reduction theorem for `α ⋆ β ≥ γ` -/

/-- *Theorem C (`thm:reduce`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), second paragraph,
Bruhat component, part 1/3.*

If `α ⋆ β ≥ γ`, then `α₁ = γ ◃ β⁻¹` and `β₁ = α₁⁻¹ ▹ γ` satisfy
`α₁ ⋆ β₁ = α₁ * β₁ = γ` and `α₁ ≤ α`, `β₁ ≤ β`.
@isnad1 id=other.1h3v.s6.0265c01612b2 from=translated src=- shape=cfbe11d9 vocab=c0dce45a
-/
theorem reduce_witness (α β γ : AspPerm) (h : α ⋆ β ≥ γ) :
    let α₁ := γ ◃ β⁻¹
    let β₁ := α₁⁻¹ ▹ γ
    α₁ * β₁ = γ ∧ α₁ ⋆ β₁ = γ ∧ α₁ ≤ α ∧ β₁ ≤ β := by
  set α₁ := γ ◃ β⁻¹
  have α₁_le : α₁ ≤ α := (ge_star_iff_ge_lres α β γ).mpr h
  have h_alpha1_star_ge : α₁ ⋆ β ≥ γ :=
    (ge_star_iff_ge_lres α₁ β γ).mp (le_refl _)
  have : α₁ ≤R γ := Submodular.ler_of_lres γ β⁻¹
  set β₁ := α₁⁻¹ ▹ γ with hβ₁_def
  have β₁_le : β₁ ≤ β :=
    (ge_star_iff_ge_rres α₁ β γ).mpr h_alpha1_star_ge
  have rf := ReducedFact.of_ler_rres this hβ₁_def
  exact ⟨rf.mul_eq, rf.star_eq, α₁_le, β₁_le⟩

/-- *Theorem C (`thm:reduce`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), second paragraph, including the
shift identities, part 2/3.* Under the additional hypothesis $\chi_\alpha + \chi_\beta =
\chi_\gamma$ (which makes both shift equalities meaningful), we further have
$\alpha_1 \leq_\chi \alpha$ and $\beta_1 \leq_\chi \beta$.
@isnad1 id=other.2h3v.s6.11cba8badfcf from=translated src=- shape=70ba212a vocab=f3fd6781
-/
theorem reduce_witness_chi (α β γ : AspPerm) (hχ : α.χ + β.χ = γ.χ)
    (h : α ⋆ β ≥ γ) :
    let α₁ := γ ◃ β⁻¹
    let β₁ := α₁⁻¹ ▹ γ
    α₁ * β₁ = γ ∧ α₁ ⋆ β₁ = γ ∧ α₁ ≤χ α ∧ β₁ ≤χ β := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, h_star, h_alpha1_le, h_beta1_le⟩ := reduce_witness α β γ h
  set α₁ := γ ◃ β⁻¹ with hα₁_def
  set β₁ := α₁⁻¹ ▹ γ with hβ₁_def
  have h_chi_alpha : α₁.χ = α.χ := by
    rw [hα₁_def, AspPerm.chi_lres, AspPerm.chi_dual]
    linarith
  have h_chi_beta : β₁.χ = β.χ := by
    rw [hβ₁_def, AspPerm.chi_rres, AspPerm.chi_dual, h_chi_alpha]
    linarith
  exact ⟨h_mul, h_star, ⟨h_alpha1_le, h_chi_alpha⟩, ⟨h_beta1_le, h_chi_beta⟩⟩

/-- *Theorem C (`thm:reduce`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), first paragraph,
ASP form, part 3/3.*

For all `α, β, γ ∈ ASP` with `α.χ + β.χ = γ.χ`, the inequality `α ⋆ β ≥ γ`
is equivalent to the existence of `α₁, β₁` with `α₁ ≤χ α`, `β₁ ≤χ β`, and
`α₁ ⋆ β₁ = α₁ * β₁ = γ`.
@isnad1 id=iff.1h3v.s6.61656c082a5c from=translated src=- shape=c7cec1bb vocab=0df82262
-/
theorem reduce (α β γ : AspPerm) (hχ : α.χ + β.χ = γ.χ) :
    α ⋆ β ≥ γ ↔
      ∃ α₁ β₁ : AspPerm,
        α₁ ≤χ α ∧ β₁ ≤χ β ∧ α₁ ⋆ β₁ = γ ∧ α₁ * β₁ = γ := by
  -- Proof written by Claude Opus 4.7.
  constructor
  · intro h
    obtain ⟨h_mul, h_star, h_chi_α, h_chi_β⟩ := reduce_witness_chi α β γ hχ h
    exact ⟨_, _, h_chi_α, h_chi_β, h_star, h_mul⟩
  · rintro ⟨α₁, β₁, ⟨hα₁_le, _⟩, ⟨hβ₁_le, _⟩, h_star, _⟩
    rw [← h_star]
    exact star_mono hα₁_le hβ₁_le

/-! ### Theorem 6.1 (`resLStingy`): stingy characterization of `◃`

The dual story for `◃`, mirroring Theorem B. This is the formula labeled
`eq:resLGreedyAlpha` in
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/

/-! ### Theorem 6.5 (`reduceSeveral`): three- and many-fold reduction

The reduction theorem for products of three or more permutations follows
from `reduce` by induction. The list form below packages that induction. -/

/-- If `γ ≤ id` and `γ` has shift zero, then `γ = id`.

This is the shift-zero special case of the antisymmetry of Bruhat order. -/
private lemma eq_id_of_le_id_chi_zero {γ : AspPerm} (h : γ ≤ AspPerm.id)
    (hχ : γ.χ = 0) : γ = AspPerm.id := by
  -- Proof written by GPT 5.5.
  have h_id_le : AspPerm.id ≤ γ := by
    apply AspPerm.id_le_of_chi_nonneg
    rw [hχ]
  exact le_antisymm h h_id_le

/-- *Theorem 6.5 (`thm:reduceSeveral`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), ASP-level (list version).*

For any list of permutations `αs` and a target `γ ∈ ASP` with matching total
shift, if the Demazure product over `αs` is Bruhat-≥ `γ`, then there exists a
list of "reduced witnesses" `βs` of the same length, with `βᵢ ≤χ αᵢ`
pointwise, whose Demazure product and ordinary product both equal `γ`.
@isnad1 id=ex.2h2v.s6.3310a657c641 from=translated src=- shape=0baf372c vocab=f468c7ce
-/
theorem reduceList :
    ∀ (αs : List AspPerm) (γ : AspPerm),
      (αs.map AspPerm.χ).sum = γ.χ →
      DProd αs ≥ γ →
      ∃ βs : List AspPerm,
        List.Forall₂ (fun α β => β ≤χ α) αs βs ∧
        DProd βs = γ ∧ OrdProd βs = γ
  | [], γ, hχ, h => by
      -- Proof written by Claude Opus 4.7.
      -- Base case: γ ≤ id and γ.χ = 0, hence γ = id.
      simp only [List.map_nil, List.sum_nil, DProd_nil] at hχ h
      have hγ : γ = AspPerm.id := eq_id_of_le_id_chi_zero h hχ.symm
      simp_all
  | (α :: αs), γ, hχ, h => by
      -- Proof written by Claude Opus 4.7.
      -- Inductive step: apply `reduce` to split off `α` from the suffix.
      have hsuff : α.χ + (DProd αs).χ = γ.χ := by
        rw [AspPerm.chi_DProd]
        simpa [List.map_cons, List.sum_cons] using hχ
      have h' : α ⋆ DProd αs ≥ γ := by
        simpa only [DProd_cons] using h
      obtain ⟨α₁, π, hα₁, hπ, h_star, h_mul⟩ :=
        (reduce α (DProd αs) γ hsuff).mp h'
      -- Inductive hypothesis on the suffix targeting `π`.
      have hπ_χ : (αs.map AspPerm.χ).sum = π.χ := by
        rw [← AspPerm.chi_DProd, hπ.2]
      obtain ⟨βs, hβs_forall, hβs_star, hβs_mul⟩ :=
        reduceList αs π hπ_χ hπ.1
      refine ⟨α₁ :: βs, List.Forall₂.cons hα₁ hβs_forall, ?_, ?_⟩
      · simp only [DProd_cons, hβs_star, h_star]
      · simp only [OrdProd_cons, hβs_mul, h_mul]

end Reduction

end LeanPool.DemazureProduct
