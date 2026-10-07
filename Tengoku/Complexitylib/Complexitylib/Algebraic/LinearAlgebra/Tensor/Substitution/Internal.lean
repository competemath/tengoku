/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Tengoku

/-!
# Border substitution for tight tensors: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution`.

* **Only the kernel matters.** Over a field, `ker P ⊆ ker P'` gives `P' = G * P` (factor
  `P'` through `ℂ^α ⧸ ker P ≅ range P` and extend from `range P`), so
  `X ↦ map X Y Z T` at `P'` is the image under `G ⊗ 1 ⊗ 1` of its value at `P`.
* **One step.** Approximate `T` by `T_n = ∑_{s < r + 1} u_{n,s} ⊗ v_{n,s} ⊗ w_{n,s}`. A unit
  vector `û_n` on the line of `u_{n,0}` (any unit vector if `u_{n,0} = 0`) makes `orthProj û_n`
  kill the first summand, so `(orthProj û_n ⊗ 1 ⊗ 1) T_n` has rank at most `r`. A subsequence
  of `û_n` converges on the compact unit sphere of the sup norm, to some `u ≠ 0`, and
  `(X, S) ↦ (X ⊗ 1 ⊗ 1) S` and `orthProj` (at `u ≠ 0`) are continuous.
* **Torus limit.** With weights `σ i = τA i - τA i₀` for the `i₀` minimizing `τA` on the
  support of `u` (and `τC` shifted to compensate), `λ(t) = diag(t ^ σ i)` fixes `T` together
  with the matching diagonal maps on `B` and `C`. Conjugating gives a border-rank bound for
  the projection with kernel `ℂ λ(t) u`. Along `t = 2⁻ⁿ`, `λ(t) u → u i₀ • e_{i₀}`, since
  `σ i > 0` for every other `i` in the support (`τA` is injective), and the set of `v` whose
  projection satisfies the bound is closed at `v ≠ 0`. The projection along `e_{i₀}` has the
  same kernel as the diagonal `0/1` matrix that zeroes slice `i₀`.
* **Deletion.** For `T` restricted to `S`, the zeroed slice `i₀` is in `S`, or else the bound
  already holds for the restriction to `S` and any further deletion keeps it. Iterating gives
  the deletion order; once the bound reaches `0`, the restricted tensor is zero, which forces
  at most `r` nonzero slices.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal

open Finset Matrix Filter Topology

variable {α β γ α' β' γ' α'' : Type*}

section OrthProj

variable [Fintype α] [DecidableEq α]

theorem orthProj_mulVec (u v : α → ℂ) :
    orthProj u *ᵥ v = v - ((star u ⬝ᵥ u)⁻¹ * (star u ⬝ᵥ v)) • u := by
  rw [orthProj, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

omit [DecidableEq α] in
theorem star_dotProduct_self_ne_zero {u : α → ℂ} (hu : u ≠ 0) : star u ⬝ᵥ u ≠ 0 := by
  open ComplexOrder in exact fun h => hu (dotProduct_star_self_eq_zero.mp h)

theorem orthProj_mulVec_self (u : α → ℂ) : orthProj u *ᵥ u = 0 := by
  by_cases hu : u = 0
  · subst hu
    simp
  · rw [orthProj_mulVec, inv_mul_cancel₀ (star_dotProduct_self_ne_zero hu), one_smul, sub_self]

theorem orthProj_mulVec_eq_zero_iff {u v : α → ℂ} :
    orthProj u *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • u := by
  constructor
  · intro h
    exact ⟨_, sub_eq_zero.mp ((orthProj_mulVec u v).symm.trans h)⟩
  · rintro ⟨c, rfl⟩
    rw [mulVec_smul, orthProj_mulVec_self, smul_zero]

theorem continuousAt_orthProj {u : α → ℂ} (hu : u ≠ 0) :
    ContinuousAt (orthProj : (α → ℂ) → Matrix α α ℂ) u := by
  have hd : Continuous fun u : α → ℂ => star u ⬝ᵥ u :=
    continuous_star.dotProduct continuous_id
  have hv : Continuous fun u : α → ℂ => vecMulVec u (star u) := by
    unfold vecMulVec
    fun_prop
  unfold orthProj
  exact continuousAt_const.sub ((hd.continuousAt.inv₀ (star_dotProduct_self_ne_zero hu)).smul
    hv.continuousAt)

/-- Some unit vector `u` (for the sup norm) has `orthProj u` vanishing at `x`. -/
theorem exists_mem_sphere_orthProj_mulVec_eq_zero [Nonempty α] (x : α → ℂ) :
    ∃ u ∈ Metric.sphere (0 : α → ℂ) 1, orthProj u *ᵥ x = 0 := by
  obtain ⟨y, hy, hxy⟩ : ∃ y : α → ℂ, y ≠ 0 ∧ ∃ c : ℂ, x = c • y := by
    by_cases hx : x = 0
    · refine ⟨fun _ => 1, fun h => ?_, 0, by simp [hx]⟩
      simpa using congrFun h (Classical.arbitrary α)
    · exact ⟨x, hx, 1, (one_smul ℂ x).symm⟩
  refine ⟨((‖y‖ : ℂ)⁻¹) • y, by simpa using norm_smul_inv_norm (𝕜 := ℂ) hy, ?_⟩
  obtain ⟨c, rfl⟩ := hxy
  rw [orthProj_mulVec_eq_zero_iff]
  have hy' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
  exact ⟨c * ‖y‖, by rw [smul_smul, mul_assoc, mul_inv_cancel₀ hy', mul_one]⟩

end OrthProj

section Kernel

/-- Over a field, `ker P ⊆ ker P'` lets `P'` factor as `G * P`. -/
theorem exists_mul_eq_of_ker [Fintype α] [Fintype α'] {P : Matrix α' α ℂ}
    {P' : Matrix α'' α ℂ} (h : ∀ v, P *ᵥ v = 0 → P' *ᵥ v = 0) :
    ∃ G : Matrix α'' α' ℂ, G * P = P' := by
  classical
  set f := Matrix.toLin' P
  set f' := Matrix.toLin' P'
  have hker : LinearMap.ker f ≤ LinearMap.ker f' := fun v hv => h v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((LinearMap.ker f).liftQ f' hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun φ => φ ⟨f v, LinearMap.mem_range_self f v⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [LinearMap.comp_apply, this, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable [Fintype α] [Fintype β] [Fintype γ]

theorem borderRankLE_map_of_ker [Fintype α'] [Fintype β'] [Fintype γ']
    {P : Matrix α' α ℂ} {P' : Matrix α'' α ℂ} (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)
    {T : Tensor3 α β γ} {ρ : ℕ} (h : (map P Y Z T).BorderRankLE ρ)
    (hker : ∀ v, P *ᵥ v = 0 → P' *ᵥ v = 0) : (map P' Y Z T).BorderRankLE ρ := by
  classical
  obtain ⟨G, rfl⟩ := exists_mul_eq_of_ker hker
  have := h.map G (1 : Matrix β' β' ℂ) (1 : Matrix γ' γ' ℂ)
  rwa [map_map, Matrix.one_mul, Matrix.one_mul] at this

variable [DecidableEq β] [DecidableEq γ]

theorem continuous_map_left :
    Continuous fun p : Matrix α' α ℂ × Tensor3 α β γ =>
      map p.1 (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) p.2 := by
  unfold map
  fun_prop

theorem continuous_map_left_const (T : Tensor3 α β γ) :
    Continuous fun X : Matrix α' α ℂ => map X (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T := by
  unfold map
  fun_prop

end Kernel

section Restrict

variable [DecidableEq α]

theorem restrictSlices_restrictSlices (T : Tensor3 α β γ) (S S' : Finset α) :
    (T.restrictSlices S).restrictSlices S' = T.restrictSlices (S' ∩ S) := by
  funext i j k
  simp only [restrictSlices, Finset.mem_inter]
  split_ifs <;> simp_all

theorem restrictSlices_univ [Fintype α] (T : Tensor3 α β γ) : T.restrictSlices univ = T := by
  funext i j k
  simp [restrictSlices]

theorem restrictSlices_empty (T : Tensor3 α β γ) : T.restrictSlices ∅ = 0 := by
  funext i j k
  simp [restrictSlices]

theorem zero_restrictSlices (S : Finset α) : (0 : Tensor3 α β γ).restrictSlices S = 0 := by
  funext i j k
  simp [restrictSlices]

theorem restrictSlices_eq_map [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] (T : Tensor3 α β γ) (S : Finset α) :
    T.restrictSlices S =
      map (diagonal fun i => if i ∈ S then 1 else 0) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T := by
  rw [← diagonal_one, ← diagonal_one, map_diagonal]
  funext i j k
  simp [restrictSlices]

theorem tight_restrictSlices {T : Tensor3 α β γ} (hT : T.Tight) (S : Finset α) :
    (T.restrictSlices S).Tight := by
  obtain ⟨τA, τB, τC, hinj, h⟩ := hT
  refine ⟨τA, τB, τC, hinj, fun i j k hijk => h i j k ?_⟩
  simp only [Tensor3.restrictSlices] at hijk
  split_ifs at hijk
  · exact hijk
  · exact absurd rfl hijk

theorem borderRankLE_restrictSlices_of_subset [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {T : Tensor3 α β γ} {S S' : Finset α} {ρ : ℕ}
    (h : (T.restrictSlices S).BorderRankLE ρ) (hS : S' ⊆ S) :
    (T.restrictSlices S').BorderRankLE ρ := by
  have := h.map (diagonal fun i => if i ∈ S' then 1 else 0) (1 : Matrix β β ℂ)
    (1 : Matrix γ γ ℂ)
  rwa [← restrictSlices_eq_map, restrictSlices_restrictSlices,
    Finset.inter_eq_left.mpr hS] at this

theorem borderRankLE_restrictSlices [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] {T : Tensor3 α β γ} {ρ : ℕ} (h : T.BorderRankLE ρ) (S : Finset α) :
    (T.restrictSlices S).BorderRankLE ρ := by
  rw [restrictSlices_eq_map]
  exact h.map _ _ _

end Restrict

theorem borderRankLE_zero_tensor (r : ℕ) : (0 : Tensor3 α β γ).BorderRankLE r :=
  (borderRankLE_zero_iff.mpr rfl).mono (Nat.zero_le r)

section Substitution

variable [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

/-- A tensor of rank at most `r + 1` has rank at most `r` after projecting the first factor
along a suitable unit vector. -/
theorem exists_mem_sphere_rankLE_map_orthProj [Nonempty α] {S : Tensor3 α β γ} {r : ℕ}
    (h : S.RankLE (r + 1)) :
    ∃ u ∈ Metric.sphere (0 : α → ℂ) 1,
      (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) S).RankLE r := by
  obtain ⟨u, v, w, rfl⟩ := h
  obtain ⟨û, hû, h0⟩ := exists_mem_sphere_orthProj_mulVec_eq_zero (u 0)
  refine ⟨û, hû, fun s => orthProj û *ᵥ u (Fin.succAbove 0 s), fun s => v (Fin.succAbove 0 s),
    fun s => w (Fin.succAbove 0 s), ?_⟩
  have hz : outer (0 : α → ℂ) (v 0) (w 0) = 0 := by
    funext i j k
    simp [outer]
  rw [Tensor3.map_sum, Fin.sum_univ_succAbove _ 0]
  simp only [Tensor3.map_outer, one_mulVec, h0, hz, zero_add]

theorem exists_borderRankLE_map_orthProj [Nonempty α] {T : Tensor3 α β γ} {r : ℕ}
    (h : T.BorderRankLE (r + 1)) :
    ∃ u : α → ℂ, u ≠ 0 ∧
      (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE r := by
  obtain ⟨Tn, hTn, hlim⟩ := mem_closure_iff_seq_limit.mp h
  choose û hû hrank using fun n => exists_mem_sphere_rankLE_map_orthProj (hTn n)
  obtain ⟨u₀, hu₀, φ, hφ, hconv⟩ := (isCompact_sphere (0 : α → ℂ) 1).tendsto_subseq hû
  have hne : u₀ ≠ 0 := by
    rintro rfl
    simp at hu₀
  refine ⟨u₀, hne, mem_closure_of_tendsto (b := atTop)
    (f := fun n => map (orthProj (û (φ n))) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) (Tn (φ n)))
    ?_ (Eventually.of_forall fun n => hrank (φ n))⟩
  have hP : Tendsto (fun n => orthProj (û (φ n))) atTop (𝓝 (orthProj u₀)) :=
    (continuousAt_orthProj hne).tendsto.comp hconv
  have hT : Tendsto (fun n => Tn (φ n)) atTop (𝓝 T) := hlim.comp hφ.tendsto_atTop
  have hc : Tendsto (fun p : Matrix α α ℂ × Tensor3 α β γ =>
      map p.1 (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) p.2) (𝓝 (orthProj u₀, T))
      (𝓝 (map (orthProj u₀) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T)) :=
    continuous_map_left.tendsto' _ _ rfl
  exact (hc.comp (hP.prodMk_nhds hT)).congr fun n => rfl

/-- The diagonal matrix `diag(t ^ τ i)`: the one-parameter subgroup with weights `τ`. -/
noncomputable def torus {ι : Type*} [DecidableEq ι] (τ : ι → ℤ) (t : ℂ) : Matrix ι ι ℂ :=
  diagonal fun i => t ^ τ i

omit [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
theorem map_torus {T : Tensor3 α β γ} {τA : α → ℤ} {τB : β → ℤ} {τC : γ → ℤ}
    (hT : ∀ i j k, T i j k ≠ 0 → τA i + τB j + τC k = 0) {t : ℂ} (ht : t ≠ 0) :
    map (torus τA t) (torus τB t) (torus τC t) T = T := by
  rw [torus, torus, torus, map_diagonal]
  funext i j k
  by_cases h : T i j k = 0
  · simp [h]
  · rw [← zpow_add₀ ht, ← zpow_add₀ ht, hT i j k h, zpow_zero, one_mul]

end Substitution

section Deletion

variable [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

end Deletion

end Algebraic.Tensor3.Internal
