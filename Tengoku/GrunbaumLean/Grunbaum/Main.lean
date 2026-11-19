/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.Grunbaum.CorollaryG

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Main results

This file restates the results of the new proof of `Π₂ = 4/3` in item 5) of Section 3 of

* G. Basso, *Errata to the single-author papers of Giuliano Basso*, Section 3
  (*Computation of maximal projection constants*, J. Funct. Anal. 277 (2019)),

in the order in which they appear there. All results are proved in the other files of the
library; here we only give the statements, in the notation of the errata.

Notation (errata → Lean):

* `S ∈ 𝒜_d` : `Grunbaum.IsSignMatrix S`;
* `D = Diag(d₁, …, d_d) ∈ 𝒟_d` : `Grunbaum.IsWeight d`;
* `√D S √D` : `Grunbaum.weightedMatrix S d`;
* `π₂(M)` : `π₂ M`, i.e. `Grunbaum.sumTopTwo M`;
* `Π(2, S)` : `Grunbaum.supWeights S`;
* `Π(2, d)` : `ProjectionConstants.maxRelProjConst ℝ 2 d`;
* `Π₂` : `ProjectionConstants.maxProjConst ℝ 2`;
* a maximizer `(S, D)` of `Π(2, d)` : `Grunbaum.IsMaximizer S d`;
* the two-graph `[S]` : `Grunbaum.twoGraph S`;
* coherent triples, cocliques, cliques of order `4` and twins : `Grunbaum.Coherent`,
  `Grunbaum.IsCoclique`, `Grunbaum.K4Free`, `Grunbaum.IsTwin`;
* `R_{2N+1}` : the block matrix `Grunbaum.blockR N` of [JFA, Section 4.1], which after
  relabelling and switching is `Grunbaum.polygonMatrix N` (the version used in the proofs);
* `R₃`, `R₅`, `A₆` : `Grunbaum.R3`, `Grunbaum.R5` (`= 𝟙₅ + S(C₅)`, see (R2)), `Grunbaum.A6`;
* the vectors `uᵢ ∈ ℝ²` of Lemma B (the rows of `U`, where `P = UUᵗ`) : the pairs `(u i, v i)`
  for an orthonormal pair `u, v` of top eigenvectors.

The indices of `R₅` and `A₆` run over `0, …, 4` and `0, …, 5`, respectively.
-/

open Finset Matrix ProjectionConstants

namespace Grunbaum.Errata

/-! ### Basic notation and results -/

/-- The formula of Chalmers and Lewicki ([JFA, Theorem 2.1] for `n = 2`):
`Π(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }`.
@isnad1 id=eq.0h1v.s4.2ebeac22311a from=translated src=- shape=a6d581ba vocab=be1e9a87
-/
theorem chalmers_lewicki (d : ℕ) : maxRelProjConst ℝ 2 d = supConfigs (Fin d) :=
  maxRelProjConst_two_eq_supConfigs d

/-- `Π₂ = sup_d Π(2, d)`.
@isnad1 id=eq.0h0v.s4.5564c09c38c7 from=translated src=- shape=3f922ecf vocab=57f87571
-/
theorem maxProjConst_two_eq : maxProjConst ℝ 2 = ⨆ d : ℕ, supConfigs (Fin d) :=
  maxProjConst_two_eq_iSup

/-- **Fan's maximum principle**: `π₂(M)` is the sum of the two largest eigenvalues of `M`.
@isnad1 id=eq.2h2v.s6.ca635cb880c4 from=translated src=- shape=91302700 vocab=60e5b6f3
-/
theorem fan {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (h2 : 2 ≤ Fintype.card ι) :
    π₂ M = hM.eigenvalues₀ ⟨0, by omega⟩ + hM.eigenvalues₀ ⟨1, by omega⟩ :=
  sumTopTwo_eq_eigenvalues₀ hM h2

/-- Switching and relabelling: `Π(2, QᵗSQ) = Π(2, S)` for a signed permutation matrix `Q`.
@isnad1 id=eq.4h6v.s6.065fcc821479 from=translated src=- shape=8fdf9e2b vocab=6860c32c
-/
theorem supWeights_switch_relabel {ι κ : Type*} [Fintype ι] [Fintype κ] {S : Matrix ι ι ℝ}
    {T : Matrix κ κ ℝ} (hS : IsSignMatrix S) (hT : IsSignMatrix T) (e : ι ≃ κ) {ε : ι → ℝ}
    (hε : IsSignVector ε) (hST : ∀ i j, S i j = ε i * ε j * T (e i) (e j)) :
    supWeights S = supWeights T :=
  supWeights_eq_of_equiv hS hT e hε.mul_self hST

/-- If `B` is a principal submatrix of `S` (up to switching and permutation), then
`Π(2, B) ≤ Π(2, S)`: extend the weights by zero.
@isnad1 id=le.4h6v.s6.ef8e92c4eff1 from=translated src=- shape=16c381aa vocab=ec5a4b13
-/
theorem supWeights_principal {ι κ : Type*} [Fintype ι] [Fintype κ] {B : Matrix ι ι ℝ}
    {S : Matrix κ κ ℝ} (hS : IsSignMatrix S) {f : ι → κ} (hf : Function.Injective f)
    {ε : ι → ℝ} (hε : IsSignVector ε) (hBS : ∀ i j, B i j = ε i * ε j * S (f i) (f j)) :
    supWeights B ≤ supWeights S :=
  supWeights_le_of_transfer hS hf hε.mul_self hBS

/-- A coclique of `[S]`: equivalently, after switching, `S[C, C] = J_C`.
@isnad1 id=iff.1h3v.s6.6a747b05c366 from=translated src=- shape=27487bf4 vocab=b4e83466
-/
theorem coclique_iff {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (C : Set ι) :
    IsCoclique S C ↔ ∃ ε : ι → ℝ, IsSignVector ε ∧ ∀ i ∈ C, ∀ j ∈ C, S i j = ε i * ε j :=
  isCoclique_iff_exists_switch hS C

/-- A clique: equivalently, after switching, all off-diagonal entries of `S` on it equal `-1`.
@isnad1 id=iff.1h3v.s6.4d50216c9e37 from=translated src=- shape=031b8d61 vocab=0c2564bc
-/
theorem clique_iff {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (C : Set ι) :
    IsClique S C ↔ ∃ ε : ι → ℝ, IsSignVector ε ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε x * ε y * S x y = -1 :=
  isClique_iff_exists_switch hS C

/-- Twins: after switching `j`, the rows of `i` and `j` coincide.
@isnad1 id=ex.2h4v.s6.2ae3f593bc85 from=translated src=- shape=ff47b142 vocab=6d494b04
-/
theorem twins_switch {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    {i j : ι} (h : IsTwin S i j) :
    ∃ ε : ι → ℝ, IsSignVector ε ∧ (∀ k, k ≠ j → ε k = 1) ∧
      ∀ k, switch S ε j k = switch S ε i k :=
  h.exists_switch hS

/-- `[R_{2N+1}] = T_{2N+1}`: a triple is coherent iff the centre of the regular `(2N+1)`-gon lies
in the convex hull of the corresponding vertices.
@isnad1 id=eq.0h1v.s7.dc50a84b876a from=translated src=- shape=4e293382 vocab=1e141f36
-/
theorem twoGraph_R (N : ℕ) :
    twoGraph (polygonMatrix N) = FranklFuredi.circleGraph (regularPolygon N) :=
  twoGraph_polygonMatrix N

/-- "By Section 4.1, we may label the indices of `R_{2N+1}` by `p₀, …, p_{2N}` such that
`[R_{2N+1}] = T_{2N+1}`", for the block matrix `R_{2N+1}` of [JFA, Section 4.1] (with the
misprint of item 8) corrected).
@isnad1 id=eq.0h1v.s7.7610b9782c70 from=translated src=- shape=8c448589 vocab=3970c908
-/
theorem twoGraph_R_JFA (N : ℕ) :
    twoGraph (blockR N) =
      (FranklFuredi.circleGraph (regularPolygon N)).pullback (blockLabel N) :=
  twoGraph_blockR N

/-- **(R1)** `{p₀, …, p_N}` is a coclique of `[R_{2N+1}]` with `N + 1` elements.
@isnad1 id=iscocliq.0h1v.s6.40e8f1730847 from=translated src=- shape=465d15a4 vocab=8679ff59
-/
theorem fact_R1 (N : ℕ) :
    IsCoclique (polygonMatrix N) (Set.range (Fin.castLE (by omega : N + 1 ≤ 2 * N + 1))) :=
  isCoclique_polygonMatrix N

/-- **(R2)** `R₅ = 𝟙₅ + S(C₅)` up to switching.
@isnad1 id=switcheq.0h0v.s5.169e7c5f8451 from=translated src=- shape=a21020ea vocab=08e8cdda
-/
theorem fact_R2 : SwitchEquiv (polygonMatrix 2) R5 :=
  switchEquiv_polygonMatrix_two

/-- **(A1)** Every `5 × 5` principal submatrix of `A₆` equals `R₅` up to switching and
permutation.
@isnad1 id=ex.0h1v.s7.a23ef6980e6d from=translated src=- shape=12e3eb7e vocab=b3f866f8
-/
theorem fact_A1 (k : Fin 6) :
    ∃ (f : Fin 6 → Fin 5) (ε : Fin 6 → ℝ), (∀ a b, a ≠ k → b ≠ k → f a = f b → a = b) ∧
      IsSignVector ε ∧ ∀ a b, a ≠ k → b ≠ k → A6 a b = ε a * ε b * R5 (f a) (f b) := by
  refine ⟨certMap k, certSign k, fun a b ha hb h => certMap_injective k a b ha hb h,
    fun a => ?_, fun a b ha hb => A6_eq_certificate k a b ha hb⟩
  fin_cases k <;> fin_cases a <;> simp [certSign]

/-- **(FF)** Every `K₄`-free two-graph with at least one coherent triple is, up to switching and
permutation, a blow-up of `R_{2N+1}` for some `N ≥ 1`, or of a principal submatrix of `A₆`.
@isnad1 id=or.3h2v.s7.88db3f057f7c from=translated src=- shape=951014ee vocab=5769c9b3
-/
theorem fact_FF {ι : Type*} [Finite ι] {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (hK4 : K4Free S) (hcoh : HasCoherent S) :
    (∃ (N : ℕ) (f : ι → Fin (2 * N + 1)), 1 ≤ N ∧ Function.Surjective f ∧
        SwitchEquiv S ((polygonMatrix N).submatrix f f)) ∨
      ∃ f : ι → Fin 6, SwitchEquiv S (A6.submatrix f f) :=
  classification hS hK4 hcoh

/-! ### Theorem A -/

/-- **Theorem A** (Reduction). `Π₂ = max {Π(2, R₃), Π(2, R₅)}`.
@isnad1 id=eq.0h0v.s5.d62a3021feff from=translated src=- shape=e28af53a vocab=51aa1ab0
-/
theorem theorem_A : maxProjConst ℝ 2 = max (supWeights R3) (supWeights R5) :=
  maxProjConst_two_eq_max

/-- **Theorem A**, with `R₃` and `R₅` the block matrices of [JFA, Section 4.1].
@isnad1 id=eq.0h0v.s7.7507e98b9029 from=translated src=- shape=c2f46728 vocab=6b82ab08
-/
theorem theorem_A' :
    maxProjConst ℝ 2 = max (supWeights (blockR 1)) (supWeights (blockR 2)) :=
  maxProjConst_two_eq_max_blockR

/-! ### Three lemmas -/

/-- **Lemma B** (Structure of maximizers), for `n = 2`. Let `d > 2` and let `(S, D)` be a
maximizer of `Π(2, d)` with `D` positive definite. Put `M := √D S √D`, let `u, v` be an
orthonormal pair of top eigenvectors of `M` (more generally, any orthonormal pair with
`uᵀMu + vᵀMv = π₂(M)`), `P := uuᵀ + vvᵀ`, and `xᵢ := (uᵢ, vᵢ) ∈ ℝ²`, so that
`Pᵢⱼ = ⟨xᵢ, xⱼ⟩`. Then:
a) `PM = MP` and `Tr(MP) = π₂(M) = Π(2, d)`;
b) `sᵢⱼ = sgn⟨xᵢ, xⱼ⟩ ≠ 0` for all `i, j`;
c) `Π(2, d) = ∑ᵢⱼ √dᵢ √dⱼ |⟨xᵢ, xⱼ⟩|`;
d) the two-graph `[S]` is `K₄`-free.
@isnad1 id=and.5h5v.s8.c0af0777fd4b from=translated src=- shape=e05097df vocab=66b03e5a
-/
theorem lemma_B {d : ℕ} (hd : 2 < d) {S : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ}
    (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i) {u v : Fin d → ℝ}
    (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) :
    (projPair u v * weightedMatrix S w = weightedMatrix S w * projPair u v ∧
      (weightedMatrix S w * projPair u v).trace = π₂ (weightedMatrix S w) ∧
      π₂ (weightedMatrix S w) = maxRelProjConst ℝ 2 d) ∧
    (∀ i j, 0 < S i j * (u i * u j + v i * v j)) ∧
    maxRelProjConst ℝ 2 d = ∑ i, ∑ j, √(w i) * √(w j) * |u i * u j + v i * v j| ∧
    K4Free S := by
  have hsign := hmax.mul_projPair_pos hpos (by simpa using hd) huv hval
  have hPi : π₂ (weightedMatrix S w) = maxRelProjConst ℝ 2 d := by
    rw [maxRelProjConst_two_eq_supConfigs, hmax.sumTopTwo_eq]
  refine ⟨⟨(mul_projPair_comm (weightedMatrix_symm hmax.isSignMatrix w) huv
      fun x y hxy => hval ▸ fanValue_le_sumTopTwo _ hxy).symm,
    by rw [trace_mul_projPair, hval], hPi⟩, hsign, ?_,
    k4Free_of_mul_projPair_pos hmax.isSignMatrix hsign⟩
  rw [← hPi, sumTopTwo_eq_sum_abs hmax.isSignMatrix hval hsign]

/-- **Lemma C** (Cloning [KMMP, Claim 2.4]), for `n = 2`. Let `m > 2`, let `(S, D)` be a
maximizer of `Π(2, m)` with `D` positive definite, and let `xᵢ = (uᵢ, vᵢ)` be as in Lemma B.
Let `C ⊆ {0, …, m - 1}` be such that `⟨xᵢ, xⱼ⟩ ≥ 0` for all `i, j ∈ C`. Let `c₁, …, c_m ≥ 0` with
`cᵢ = 1` for `i ∉ C` and `∑_{i ∈ C} cᵢ xᵢ xᵢᵀ = ∑_{i ∈ C} xᵢ xᵢᵀ`. Then
`D' := Diag(c₁d₁, …, c_m d_m)` lies in `𝒟_m`, and `(S, D')` is again a maximizer of `Π(2, m)`.
@isnad1 id=and.9h7v.s9.f317028747f5 from=translated src=- shape=e458f38a vocab=ecdd92af
-/
theorem lemma_C {m : ℕ} (hm : 2 < m) {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i) {u v : Fin m → ℝ}
    (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) {C : Finset (Fin m)}
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ u i * u j + v i * v j) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec ![u i, v i] ![u i, v i] =
      ∑ i ∈ C, vecMulVec ![u i, v i] ![u i, v i]) :
    IsWeight (fun i => c i * w i) ∧ IsMaximizer S fun i => c i * w i :=
  have h := hmax.clone hpos hm huv hval hC hc hc1 hcC
  ⟨h.isWeight, h⟩

/-- **Lemma D.** `A₆` is not, up to switching and permutation, the sign pattern
`(sgn⟨xᵢ, xⱼ⟩)ᵢⱼ` of six vectors `xᵢ = (uᵢ, vᵢ) ∈ ℝ²` with pairwise non-zero inner products.
@isnad1 id=not.1h4v.s7.229a8a643b3e from=translated src=- shape=91464982 vocab=af05744b
-/
theorem lemma_D (u v : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 6)) {ε : Fin 6 → ℝ}
    (hε : IsSignVector ε) :
    ¬∀ i j, 0 < ε i * ε j * A6 (σ i) (σ j) * (u i * u j + v i * v j) := by
  intro h
  refine not_signPattern_A6_of_switch (S := fun i j => ε i * ε j * A6 (σ i) (σ j)) h σ.symm
    (fun a => ε (σ.symm a)) (fun a => hε.mul_self _) fun a b => ?_
  simp

/-! ### Proof of Theorem A -/

/-- **Step 1**: a maximizer of `Π(2, m) > 1` lives on at least three indices.
@isnad1 id=le.2h3v.s5.d1c676afa3fd from=translated src=- shape=ccf50e7c vocab=cd0e974d
-/
theorem step_1 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ} (hmax : IsMaximizer S w)
    (h1 : 1 < supConfigs (Fin m)) : 3 ≤ m :=
  three_le_of_isMaximizer hmax h1

/-- **Step 2** (no twins).
@isnad1 id=not.3h5v.s6.6825b2a98fd9 from=translated src=- shape=67e0079f vocab=e3f042cc
-/
theorem step_2 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ} (hmax : IsMaximizer S w)
    (h1 : 1 < supConfigs (Fin m))
    (hmin : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsMaximizer S' w' → ∀ i, 0 < w' i)
    (i j : Fin m) : ¬IsTwin S i j :=
  not_isTwin_of_minimal hmax h1 hmin i j

/-- **Step 3** (no coclique of order `4`).
@isnad1 id=le.5h4v.s6.4092a4c3992d from=translated src=- shape=92badae3 vocab=58ea8737
-/
theorem step_3 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ} (hmax : IsMaximizer S w)
    (hpos : ∀ i, 0 < w i) (hm : 2 < m)
    (hmin : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsMaximizer S' w' → ∀ i, 0 < w' i)
    {C : Finset (Fin m)} (hC : IsCoclique S (C : Set (Fin m))) : C.card ≤ 3 :=
  card_le_three_of_isCoclique hmax hpos hm hmin hC

/-- **Step 4** (classification).
@isnad1 id=le.6h4v.s7.a5429972adf3 from=translated src=- shape=a9adbe53 vocab=62089141
-/
theorem step_4 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : IsSignMatrix S) (hm : 2 < m)
    (hK4 : K4Free S) (htw : ∀ i j, ¬IsTwin S i j)
    (hcocl : ∀ C : Finset (Fin m), IsCoclique S (C : Set (Fin m)) → C.card ≤ 3) {u v : Fin m → ℝ}
    (hsign : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) :
    supWeights S ≤ max (supWeights R3) (supWeights R5) :=
  supWeights_le_max_of_minimal hS hm hK4 htw hcocl hsign

/-- The blow-up lemma [JFA, Lemma 2.2], used in Step 2: for `S = T(f, f)` and the merged weights
`D'` of `D`, `X^{|κ|} χ(√D S √D) = X^{|ι|} χ(√D' T √D')`.
@isnad1 id=eq.1h5v.s8.5174f9b5f10d from=translated src=- shape=cf9f3366 vocab=906be2c2
-/
theorem blow_up {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix κ κ ℝ) (f : ι → κ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Polynomial.X ^ Fintype.card κ * (weightedMatrix (T.submatrix f f) w).charpoly =
      Polynomial.X ^ Fintype.card ι * (weightedMatrix T (mergeWeight f w)).charpoly :=
  charpoly_weightedMatrix_submatrix T f hw

/-- The cloning lemma of Kumar, Mohar, Mojallal and Pragada ([KMMP, Claim 2.4]), for every
rank `r ≥ 1`, used in Lemma C.
@isnad1 id=ismaximi.6h6v.s8.a3598b77a30d from=translated src=- shape=ca21b1eb vocab=a15b2eda
-/
theorem kmmp_cloning {n r : ℕ} {U : Matrix (Fin n) (Fin r) ℝ} {w : Fin n → ℝ}
    (h : KMMP.IsMaximizingPair U w) (hr : 0 < r) {C : Finset (Fin n)}
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ U i ⬝ᵥ U j) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec (U i) (U i) = ∑ i ∈ C, vecMulVec (U i) (U i)) :
    KMMP.IsMaximizingPair (KMMP.cloneMatrix U c) (KMMP.cloneWeight w c) :=
  h.clone hr hC hc hc1 hcC

/-! ### The remaining computation: `Π(2, R₅)` -/

/-- **Lemma E.** For `D ∈ 𝒟₅`, `det(x 𝟙₅ - √D R₅ √D) = x⁵ - x⁴ + 4τx² - 16δ`, where
`δ = d₁ ⋯ d₅` and `τ = ∑_{{i, j, k} coherent} dᵢ dⱼ dₖ`.
@isnad1 id=eq.1h1v.s8.6b513af699b5 from=translated src=- shape=8116952d vocab=61b5d4e0
-/
theorem lemma_E {d : Fin 5 → ℝ} (hd : IsWeight d) :
    (weightedMatrix R5 d).charpoly = Polynomial.X ^ 5 - Polynomial.X ^ 4 +
      Polynomial.C (4 * tauR5 d) * Polynomial.X ^ 2 - Polynomial.C (16 * ∏ i, d i) :=
  charpoly_weightedMatrix_R5 hd

end Grunbaum.Errata
