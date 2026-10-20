/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku.LeanPool.LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.BarrierPotential
public import Tengoku.LeanPool.LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.ColoringFramework
public import Tengoku.LeanPool.LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LaplacianBasics
import Tengoku.LeanPool.LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.DynamicColoring
import Tengoku.LeanPool.LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LoewnerPullback
import Tengoku.LeanPool.LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.OneSidedBarrier
import Tengoku.Seed.Algebra.Order.Star.Real
import Tengoku.Seed.Analysis.Matrix.PosDef

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Problem 6: Large epsilon-light vertex subsets -- Main Proof

This file contains the main theorem and its supporting lemmas.
All auxiliary infrastructure is in `Problem6Aux.lean`.

## Main theorems

- `Problem6.exists_eps_light_subset`: for every simple graph G
  and `epsilon in (0,1]`, there exists an epsilon-light subset S
  with `|S| >= epsilon/256 * |V|`
-/

@[expose] public section

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### BSS coloring infrastructure

The BSS framework follows the informal proof's dynamic approach:
1. Spectral setup: Lhalf with Lhalf² = L (via spectral theorem)
2. Normalized edge Laplacians A_e = Lhalf_pinv * L_e * Lhalf_pinv
3. Coloring with one-sided barrier tracking monochromatic matrix M_t
4. Pullback: M_k ≤ u_k·I → each color class ε-light (via eps_light_of_loewner_bound) -/

/-- For a real diagonal `f`, the unitary conjugate `U * diagonal f * U★` is Hermitian. -/
private lemma unitary_diag_conj_isHermitian (U : Matrix V V ℝ) (f : V → ℝ) :
    (U * diagonal f * (star U : Matrix V V ℝ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc,
    star_eq_conjTranspose, conjTranspose_conjTranspose]
  simp [star_trivial]

/-- Product of unitary-diagonal-conjugate matrices:
    (U * D(f) * U★) * (U * D(g) * U★) = U * D(f·g) * U★.
    Used for spectral calculus (computing products via eigenvalue multiplication). -/
lemma unitary_diag_mul
    (U : Matrix V V ℝ) (hstarU : (star U : Matrix V V ℝ) * U = 1)
    (f g : V → ℝ) :
    (U * diagonal f * (star U : Matrix V V ℝ)) *
    (U * diagonal g * (star U : Matrix V V ℝ)) =
    U * diagonal (f * g) * (star U : Matrix V V ℝ) := by
  have h1 : (U * diagonal f * (star U : Matrix V V ℝ)) *
             (U * diagonal g * (star U : Matrix V V ℝ)) =
      U * diagonal f * ((star U : Matrix V V ℝ) * U) *
      diagonal g * (star U : Matrix V V ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [h1, hstarU, Matrix.mul_one,
      show U * diagonal f * diagonal g * (star U : Matrix V V ℝ) =
           U * (diagonal f * diagonal g) * (star U : Matrix V V ℝ) by
        simp only [Matrix.mul_assoc]]
  congr 1; congr 1
  exact diagonal_mul_diagonal f g

/-- **Sub-lemma 1 (Spectral setup)**: For any graph G, there exists a Hermitian matrix
    Lhalf with Lhalf * Lhalf = graphLaplacian G (the PSD square root), constructed
    via the spectral theorem. This is Step 1 of the informal proof.
    The spectral decomposition L = U * diag(λ) * U* gives
    Lhalf = U * diag(√λ) * U*, which satisfies Lhalf² = L and IsHermitian. -/
lemma spectral_sqrt_exists
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (Lhalf : Matrix V V ℝ),
      Lhalf.IsHermitian ∧
      Lhalf * Lhalf = graphLaplacian G := by
  -- Use the spectral theorem for the PSD Hermitian graph Laplacian.
  -- L = U * diag(ev) * U* => Lhalf = U * diag(√ev) * U*
  set L := graphLaplacian G with hL_def
  have hL_psd := graphLaplacian_posSemidef G
  have hL_herm := graphLaplacian_isHermitian G
  set U := (hL_herm.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set ev := hL_herm.eigenvalues with hev_def
  have hUU : (U : Matrix V V ℝ) * (star U : Matrix V V ℝ) = 1 :=
    Unitary.coe_mul_star_self hL_herm.eigenvectorUnitary
  have hUstarU : (star U : Matrix V V ℝ) * (U : Matrix V V ℝ) = 1 :=
    Unitary.coe_star_mul_self hL_herm.eigenvectorUnitary
  have hev_nn : ∀ i, 0 ≤ ev i := hL_psd.eigenvalues_nonneg
  set sqrtEv : V → ℝ := fun i => Real.sqrt (ev i) with hsqrtEv_def
  set Lhalf := (U : Matrix V V ℝ) * diagonal sqrtEv * (star U : Matrix V V ℝ) with hLhalf_def
  have hL_eq : L = (U : Matrix V V ℝ) * diagonal ev * (star U : Matrix V V ℝ) :=
    hL_def ▸ realSpectralDecomp hL_herm
  refine ⟨Lhalf, ?_, ?_⟩
  · -- Lhalf is Hermitian
    rw [hLhalf_def]; exact unitary_diag_conj_isHermitian U sqrtEv
  · -- Lhalf * Lhalf = L
    rw [hLhalf_def, hL_eq, unitary_diag_mul U hUstarU sqrtEv sqrtEv]
    have h_sq : sqrtEv * sqrtEv = ev := by
      ext i
      rw [Pi.mul_apply, hsqrtEv_def, ← Real.sqrt_mul (hev_nn i), Real.sqrt_mul_self (hev_nn i)]
    rw [h_sq]

omit [DecidableEq V] in
/-- For a Hermitian matrix M, there exists a Hermitian pseudo-inverse M_pinv satisfying
    the Moore-Penrose conditions:
    (1) M * M_pinv * M = M
    (2) M_pinv * M * M_pinv = M_pinv
    (3) M * M_pinv is idempotent (a projection)
    Constructed via spectral decomposition: if M = U * diag(λ) * U★,
    then M_pinv = U * diag(λ⁻¹) * U★ where λ⁻¹(i) = 0 if λ(i) = 0. -/
lemma hermitian_pseudo_inverse_exists
    (M : Matrix V V ℝ) (hM : M.IsHermitian) :
    ∃ (M_pinv : Matrix V V ℝ),
      M_pinv.IsHermitian ∧
      M * M_pinv * M = M ∧
      M_pinv * M * M_pinv = M_pinv ∧
      (M * M_pinv) * (M * M_pinv) = M * M_pinv ∧
      M * M_pinv = M_pinv * M := by
  classical
  set U := (hM.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set ev := hM.eigenvalues with hev_def
  have hUstarU : (star U : Matrix V V ℝ) * U = 1 :=
    Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hM_eq : M = U * diagonal ev * (star U : Matrix V V ℝ) := realSpectralDecomp hM
  -- Pseudo-inverse eigenvalues: invert nonzero, keep zero
  set pinvEv : V → ℝ := fun i => if ev i = 0 then 0 else (ev i)⁻¹ with hpinvEv_def
  refine ⟨U * diagonal pinvEv * (star U : Matrix V V ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · -- M_pinv is Hermitian: U * diag(real) * U★ is Hermitian for real diagonal
    exact unitary_diag_conj_isHermitian U pinvEv
  · -- (1) M * M_pinv * M = M via eigenvalue identity ev * pinvEv * ev = ev
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU (ev * pinvEv) ev]
    suffices h : ev * pinvEv * ev = ev by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  · -- (2) M_pinv * M * M_pinv = M_pinv via eigenvalue identity pinvEv * ev * pinvEv = pinvEv
    rw [hM_eq, unitary_diag_mul U hUstarU pinvEv ev,
        unitary_diag_mul U hUstarU (pinvEv * ev) pinvEv]
    suffices h : pinvEv * ev * pinvEv = pinvEv by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [inv_mul_cancel₀ h, one_mul]
  · -- (3) M * M_pinv is idempotent via (ev * pinvEv)² = ev * pinvEv
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU (ev * pinvEv) (ev * pinvEv)]
    suffices h : ev * pinvEv * (ev * pinvEv) = ev * pinvEv by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ h]; simp
  · -- (4) Commutativity: M * M_pinv = M_pinv * M (diagonal multiplication commutes)
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU pinvEv ev]
    congr 1; congr 1; ext i; simp [mul_comm]

/-! #### Dynamic BSS coloring (Steps 1–5 combined)
The informal proof (Steps 3–5) uses a **dynamic** coloring process:
  1. Per-edge matrices: A_e := L^{-1/2} L_e L^{-1/2} with ∑_e A_e = I on range(L)
  2. Track M_t := ∑_{monochromatic edges at time t} A_e (DYNAMIC, depends on current coloring)
  3. At time t: color vertex v with γ, increment M_{t+1} = M_t + B_v^γ where
     B_v^γ = ∑_{u ∈ T, col(u)=γ, uv∈E} A_{uv}
  4. BSS barrier (Lemma 6.1) maintains M_t ≺ u_t·I at each step
  5. After k = n/4 steps: M_k = ∑_a L^{-1/2} L_{S_a} L^{-1/2} (by construction)
  6. Since M_k ≺ u_k·I ≺ ε·I, each color class S_a is ε-light
The proof is decomposed into:
  (A) `dynamic_barrier_coloring`: The core BSS dynamic coloring induction that
      produces a PartialColoring with per-color barrier bounds on normalized monochromatic sums.
  (B) `bss_dynamic_coloring`: Combines (A) with `pinv_pullback_eq` and
      `eps_light_of_loewner_bound` to convert barrier bounds to ε-lightness. -/

/-- Off-diagonal entry equality for the cross-edge decomposition:
    for i ≠ j, (graphLaplacian G - DS) i j = (graphLaplacian G_same) i j. -/
lemma cross_edge_off_diagonal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (pc : PartialColoring V r)
    (S : Fin r → Finset V)
    (hS : S = fun γ => pc.colored.filter (fun w => pc.color w = γ))
    (G_same : SimpleGraph V) [DecidableRel G_same.Adj]
    (hG_same : ∀ a b, G_same.Adj a b ↔ (G.Adj a b ∧ (a ∈ pc.colored ↔ b ∈ pc.colored)))
    (DS : Matrix V V ℝ)
    (hDS : DS = ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
      (inducedLaplacian G (S γ ∪ {v}) - inducedLaplacian G (S γ)))
    (i j : V) (hij : i ≠ j) :
    (graphLaplacian G - DS) i j = (graphLaplacian G_same) i j := by
  -- Helper: off-diagonal entry of graphLaplacian
  have gl_off : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (a b : V), a ≠ b →
      graphLaplacian H a b = if H.Adj a b then -1 else 0 := by
    intro H _ a b hab; simp only [graphLaplacian, Matrix.of_apply, hab, ↓reduceIte]
  -- Helper: off-diagonal entry of inducedLaplacian
  have il_off : ∀ (T : Finset V) (a b : V), a ≠ b →
      inducedLaplacian G T a b = if G.Adj a b ∧ a ∈ T ∧ b ∈ T then -1 else 0 := by
    intro T a b hab; simp only [inducedLaplacian, Matrix.of_apply, hab, ↓reduceIte]
  simp only [Matrix.sub_apply, gl_off G i j hij, gl_off G_same i j hij]
  rw [hDS]; simp only [Matrix.sum_apply, Matrix.sub_apply, il_off _ i j hij]
  by_cases hadj : G.Adj i j
  · -- G.Adj i j
    rw [ite_eq_left hadj]
    by_cases hcross : ¬(i ∈ pc.colored ↔ j ∈ pc.colored)
    · -- Cross-edge: G_same has no edge, double sum = -1
      rw [ite_eq_right (show ¬G_same.Adj i j from fun h => hcross ((hG_same i j).mp h).2)]
      -- Base sets don't contain both endpoints (cross-edge)
      have h_base : ∀ (γ : Fin r), ¬(G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ) := by
        intro γ ⟨_, hi, hj⟩
        rw [hS] at hi hj; simp only [Finset.mem_filter] at hi hj
        exact hcross ⟨fun _ => hj.1, fun _ => hi.1⟩
      simp_rw [ite_eq_right (h_base _), sub_zero]
      have h_cases : (i ∈ pc.colored ∧ j ∉ pc.colored) ∨
          (i ∉ pc.colored ∧ j ∈ pc.colored) := by
        by_cases hi : i ∈ pc.colored
        · exact Or.inl ⟨hi, fun hj => hcross ⟨fun _ => hj, fun _ => hi⟩⟩
        · exact Or.inr ⟨hi, by_contra fun hj =>
            hcross ⟨fun h => absurd h hi,
                    fun h => absurd h hj⟩⟩
      -- Goal: -1 - ∑ v, ∑ γ, (if ... then -1 else 0) = 0
      suffices h_sum :
          ∑ v ∈ Finset.univ.filter (· ∉ pc.colored),
          ∑ γ : Fin r,
          (if G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧
              j ∈ (S γ ∪ {v})
            then (-1 : ℝ) else 0) = -1 by
        linarith
      rcases h_cases with ⟨hic, hnjc⟩ | ⟨hnic, hjc⟩
      · -- i ∈ colored, j ∉ colored: only (v=j, γ=color i) contributes
        rw [Finset.sum_eq_single_of_mem j
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnjc⟩)]
        · rw [Finset.sum_eq_single_of_mem (pc.color i) (Finset.mem_univ _)]
          · rw [ite_eq_left]
            refine ⟨hadj,
              Finset.mem_union_left _ ?_,
              Finset.mem_union_right _
                (Finset.mem_singleton_self _)⟩
            rw [hS]; exact Finset.mem_filter.mpr ⟨hic, rfl⟩
          · intro γ _ hne; rw [ite_eq_right]; intro ⟨_, hi_mem, _⟩
            simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hi_mem
            exact hi_mem.elim (fun ⟨_, h⟩ => hne h.symm) (fun h => hnjc (h ▸ hic))
        · intro v _ hne
          apply Finset.sum_eq_zero; intro γ _; rw [ite_eq_right]; intro ⟨_, _, hj_mem⟩
          simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hj_mem
          exact hj_mem.elim (fun ⟨h, _⟩ => hnjc h) (fun h => hne h.symm)
      · -- i ∉ colored, j ∈ colored: only (v=i, γ=color j) contributes
        rw [Finset.sum_eq_single_of_mem i
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnic⟩)]
        · rw [Finset.sum_eq_single_of_mem (pc.color j) (Finset.mem_univ _)]
          · rw [ite_eq_left]
            refine ⟨hadj,
              Finset.mem_union_right _
                (Finset.mem_singleton_self _),
              Finset.mem_union_left _ ?_⟩
            rw [hS]; exact Finset.mem_filter.mpr ⟨hjc, rfl⟩
          · intro γ _ hne; rw [ite_eq_right]; intro ⟨_, _, hj_mem⟩
            simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hj_mem
            exact hj_mem.elim (fun ⟨_, h⟩ => hne h.symm) (fun h => hnic (h ▸ hjc))
        · intro v _ hne
          apply Finset.sum_eq_zero; intro γ _; rw [ite_eq_right]; intro ⟨_, hi_mem, _⟩
          simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hi_mem
          exact hi_mem.elim (fun ⟨h, _⟩ => hnic h) (fun h => hne h.symm)
    · -- Same-status edge: G_same has edge, double sum = 0
      have hcross' : i ∈ pc.colored ↔ j ∈ pc.colored := not_not.mp hcross
      rw [ite_eq_left ((hG_same i j).mpr ⟨hadj, hcross'⟩)]
      -- Goal: -1 - ∑ ... = -1, need ∑ ... = 0
      suffices h_sum :
          ∑ v ∈ Finset.univ.filter (· ∉ pc.colored),
          ∑ γ : Fin r,
          ((if G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧
               j ∈ (S γ ∪ {v})
             then (-1 : ℝ) else 0) -
           (if G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ then (-1 : ℝ) else 0)) = 0 by
        linarith
      apply Finset.sum_eq_zero; intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      apply Finset.sum_eq_zero; intro γ _
      have h_iff : (G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧ j ∈ (S γ ∪ {v})) ↔
          (G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ) := by
        constructor
        · intro ⟨h1, h2, h3⟩
          simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at h2 h3
          refine ⟨h1, ?_, ?_⟩
          · rcases h2 with h2 | rfl
            · rw [hS]; exact Finset.mem_filter.mpr h2
            · rcases h3 with ⟨hjc, _⟩ | rfl
              · exact absurd (hcross'.mpr hjc) hv
              · exact absurd rfl hij
          · rcases h3 with h3 | rfl
            · rw [hS]; exact Finset.mem_filter.mpr h3
            · rcases h2 with ⟨hic, _⟩ | rfl
              · exact absurd (hcross'.mp hic) hv
              · exact absurd rfl.symm hij
        · intro ⟨h1, h2, h3⟩
          exact ⟨h1, Finset.mem_union_left _ h2, Finset.mem_union_left _ h3⟩
      simp only [h_iff, sub_self]
  · -- not G.Adj i j: L = 0, all terms vanish
    rw [ite_eq_right hadj, ite_eq_right (show ¬G_same.Adj i j from
      fun h => hadj ((hG_same i j).mp h).1)]
    -- Goal: 0 - ∑ ... = 0, need ∑ ... = 0
    suffices h_sum : ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
        ((if G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧ j ∈ (S γ ∪ {v}) then (-1 : ℝ) else 0) -
         (if G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ then (-1 : ℝ) else 0)) = 0 by
      linarith
    apply Finset.sum_eq_zero; intro v _
    apply Finset.sum_eq_zero; intro γ _
    have h_neg : ∀ P, ¬(G.Adj i j ∧ P) := fun _ h => hadj h.1
    simp only [ite_eq_right (h_neg _), sub_self]

omit [DecidableEq V] in
/-- Diagonal entry derivation for the cross-edge decomposition:
    derives diagonal from row sums and off-diagonal matching. -/
lemma cross_edge_diagonal
    (L DS R : Matrix V V ℝ)
    (h_off_diag : ∀ (a b : V), a ≠ b → (L - DS) a b = R a b)
    (h_row_LHS : ∀ a, ∑ b, (L - DS) a b = 0)
    (h_row_RHS : ∀ a, ∑ b, R a b = 0)
    (i : V) :
    (L - DS) i i = R i i := by
  classical
  have h1 := h_row_LHS i
  have h2 := h_row_RHS i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1 h2
  have h3 : ∑ j ∈ Finset.univ.erase i, (L - DS) i j =
      ∑ j ∈ Finset.univ.erase i, R i j :=
    Finset.sum_congr rfl fun j hj =>
      h_off_diag i j (Finset.ne_of_mem_erase hj).symm
  linarith

/-- Base case of BSS induction: empty coloring, M_0 = 0, Φ_{ε/2}(0) = 2n/ε. -/
lemma total_barrier_bound_base
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hr_pos : 0 < r)
    (Lhalf_pinv : Matrix V V ℝ)
    (h_lap_le1 : ∀ T : Finset V, T.card ≤ 1 → inducedLaplacian G T = 0) :
    ∃ pc : PartialColoring V r,
      pc.colored.card = 0 ∧
      ((ε / 2 + (0 : ℝ) * (ε / (Fintype.card V : ℝ))) • (1 : Matrix V V ℝ) -
        ∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G
            (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv).PosDef ∧
      barrierPotential (ε / 2 + (0 : ℝ) * (ε / (Fintype.card V : ℝ)))
        (∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G
            (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv) ≤ 2 * (Fintype.card V : ℝ) / ε := by
  have h_sum_zero : ∑ γ : Fin r,
      Lhalf_pinv * inducedLaplacian G
        ((∅ : Finset V).filter (fun v =>
          (fun (_ : V) => (⟨0, hr_pos⟩ : Fin r)) v = γ)) *
        Lhalf_pinv = 0 := by
    apply Finset.sum_eq_zero; intro γ _
    simp only [Finset.filter_empty]
    rw [h_lap_le1 _ (by simp), Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨⟨∅, fun _ => ⟨0, hr_pos⟩⟩, by simp, ?_, ?_⟩
  · -- PosDef: (ε/2 · I - 0).PosDef
    simp only [zero_mul, add_zero, h_sum_zero, sub_zero]
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal (fun _ => by linarith)
  · -- Potential bound: Φ_{ε/2}(0) = 2n/ε
    simp only [zero_mul, add_zero, h_sum_zero]
    unfold barrierPotential
    rw [sub_zero]
    have h_inv : ((ε / 2) • (1 : Matrix V V ℝ))⁻¹ =
        (2 / ε) • (1 : Matrix V V ℝ) :=
      Matrix.inv_eq_right_inv (by rw [smul_mul_smul_comm, one_mul,
        show ε / 2 * (2 / ε) = 1 from by field_simp, one_smul])
    rw [h_inv, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      div_mul_eq_mul_div]

/-! ### The coloring induction result -/

/-! ### Proof of the main theorem -/

/-- For 1 ≤ n ≤ 3, a single vertex is ε-light and satisfies the size bound. -/
lemma eps_light_small_n
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : Fintype.card V < 4)
    (hne : 0 < Fintype.card V) :
    ∃ S : Finset V, IsEpsLight G ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤
      (S.card : ℝ) := by
  -- Take any single vertex v. Then L_{S} = 0 (no edges in a singleton),
  -- so εL - L_S = εL ≽ 0. Also |S| = 1 ≥ ε·n/256 since n ≤ 3 and ε ≤ 1.
  have ⟨v⟩ := Fintype.card_pos_iff.mp hne
  refine ⟨{v}, ?_, ?_⟩
  · -- {v} is ε-light: L_{S} = 0 for singleton, so εL - 0 = εL ≽ 0
    -- since L is PSD and ε > 0.
    have hLS : inducedLaplacian G {v} = 0 := by
      ext i j
      simp only [inducedLaplacian, Matrix.of_apply, Matrix.zero_apply]
      split_ifs with hij h
      · -- diagonal: need filter card = 0 since no edges within singleton
        rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _ ⟨hiv, hkv, hadj⟩
        have hi := Finset.mem_singleton.mp hiv
        have hk := Finset.mem_singleton.mp hkv
        rw [hi, hk] at hadj
        exact absurd hadj (G.loopless.irrefl _)
      · -- off-diagonal with adj and both in {v}: contradicts i ≠ j
        exfalso
        have hi := Finset.mem_singleton.mp h.2.1
        have hj := Finset.mem_singleton.mp h.2.2
        exact hij (hi.trans hj.symm)
      · rfl
    unfold IsEpsLight
    rw [hLS, sub_zero]
    exact (graphLaplacian_posSemidef G).smul hε.le
  · -- Size bound: 1 ≥ ε/256 * n when n ≤ 3 and ε ≤ 1
    simp only [Finset.card_singleton]
    have hn' : (Fintype.card V : ℝ) < 4 := Nat.cast_lt.mpr hn
    nlinarith

/-! ### Main theorem -/

end Problem6

end
