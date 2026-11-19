/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.Grunbaum.Maximizer
import Tengoku.GrunbaumLean.ProjectionConstants.ChalmersLewicki.Absolute

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The formula of Chalmers and Lewicki for `n = 2`

Let `Π₂ = λ_ℝ(2)` be the maximal absolute projection constant of two-dimensional real normed
spaces and `Π(2, d) = λ_ℝ(2, d)` the maximal relative projection constant of two-dimensional
subspaces of `ℓ∞^d` (`ProjectionConstants.maxProjConst` and
`ProjectionConstants.maxRelProjConst`). The formula of Chalmers and Lewicki, in the form of
[JFA, Theorem 2.1], states

`Π(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }`   and   `Π₂ = sup_d Π(2, d)`.

We deduce it from the version `λ_ℝ(m, N) = max ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` of *Projection constants in
Lean* (`ProjectionConstants.maxRelProjConst_eq_clConst`): an orthonormal pair `u, v` gives the
orthogonal projection `P = uuᵀ + vvᵀ` with `uᵀAu + vᵀAv = ∑ᵢⱼ Aᵢⱼ Pᵢⱼ`, and for fixed `P` and
`tᵢ = √dᵢ` the best sign matrix is the sign pattern of `P`.

## Main results

* `Grunbaum.clConst_two_eq_supConfigs` : `sup ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| = Π(2, ι)`;
* `Grunbaum.maxRelProjConst_two_eq_supConfigs` : `Π(2, d) = λ_ℝ(2, d)`;
* `Grunbaum.maxProjConst_two_eq_iSup` : `Π₂ = λ_ℝ(2) = sup_d Π(2, d)`.
-/

open Finset Matrix ProjectionConstants

namespace Grunbaum

variable {ι : Type*} [Fintype ι]

/-- The matrix `uuᵀ + vvᵀ`; for an orthonormal pair it is the orthogonal projection onto the
plane spanned by `u` and `v`.-/
def projPair (u v : ι → ℝ) : Matrix ι ι ℝ := of fun i j => u i * u j + v i * v j

omit [Fintype ι] in
/--
@isnad1 id=eq.0h5v.s5.345b0fb6ff71 from=translated src=- shape=d54086ba vocab=34f43a58
-/
lemma projPair_apply (u v : ι → ℝ) (i j : ι) : projPair u v i j = u i * u j + v i * v j := rfl

/-- The `2 × ι` matrix with rows `u` and `v`.-/
def rowsPair (u v : ι → ℝ) : Matrix (Fin 2) ι ℝ := of ![u, v]

/--
@isnad1 id=eq.1h3v.s7.4de488e4b371 from=translated src=- shape=d88071a4 vocab=9afbfb61
-/
lemma rowsPair_mul_conjTranspose {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    rowsPair u v * (rowsPair u v)ᴴ = 1 := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [rowsPair, mul_apply, dotProduct] using h.norm_left
  · simpa [rowsPair, mul_apply, dotProduct] using h.orth
  · simpa [rowsPair, mul_apply, dotProduct, dotProduct_comm] using
      (dotProduct_comm u v ▸ h.orth : v ⬝ᵥ u = 0)
  · simpa [rowsPair, mul_apply, dotProduct] using h.norm_right

omit [Fintype ι] in
/--
@isnad1 id=eq.0h3v.s6.79b3bf27a440 from=translated src=- shape=779d1ff7 vocab=9be9848b
-/
lemma conjTranspose_rowsPair_mul (u v : ι → ℝ) :
    (rowsPair u v)ᴴ * rowsPair u v = projPair u v := by
  ext i j
  simp [rowsPair, projPair, mul_apply, Fin.sum_univ_two]

/-- For an orthonormal pair, `uuᵀ + vvᵀ ∈ 𝒫₂`.
@isnad1 id=mem.1h3v.s5.4b899c03d0b6 from=translated src=- shape=316ca4b9 vocab=6869c7a5
-/
lemma projPair_mem_orthProjs {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    projPair u v ∈ orthProjs ℝ ι 2 := by
  rw [← conjTranspose_rowsPair_mul]
  exact conjTranspose_mul_self_mem_orthProjs (rowsPair_mul_conjTranspose h)

/-- Every `P ∈ 𝒫₂` is `uuᵀ + vvᵀ` for an orthonormal pair `u, v`.
@isnad1 id=ex.1h2v.s6.0b9182543978 from=translated src=- shape=58dbf80f vocab=6869c7a5
-/
lemma exists_projPair_eq {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι 2) :
    ∃ u v, IsOrthonormalPair u v ∧ projPair u v = P := by
  classical
  obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
  refine ⟨U 0, U 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [mul_apply, dotProduct] using congrFun (congrFun hU 0) 0
  · simpa [mul_apply, dotProduct] using congrFun (congrFun hU 1) 1
  · simpa [mul_apply, dotProduct] using congrFun (congrFun hU 0) 1
  · ext i j
    simp [projPair, mul_apply, Fin.sum_univ_two]

/-- `uᵀAu + vᵀAv = ∑ᵢⱼ Aᵢⱼ Pᵢⱼ` for `P = uuᵀ + vvᵀ`.
@isnad1 id=eq.0h4v.s5.96e9d332e1e9 from=translated src=- shape=89806e3f vocab=9acffbab
-/
lemma fanValue_eq_sum_projPair (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    fanValue A u v = ∑ i, ∑ j, A i j * projPair u v i j :=
  fanValue_eq_sum A u v

/--
@isnad1 id=isunitwe.1h2v.s4.fcfdb2129f08 from=translated src=- shape=e4f3f015 vocab=14768794
-/
lemma isUnitWeight_sqrt {w : ι → ℝ} (hw : IsWeight w) : IsUnitWeight fun i => √(w i) :=
  ⟨fun _ => Real.sqrt_nonneg _, by simp [Real.sq_sqrt (hw.nonneg _), hw.sum_eq]⟩

/-- `π₂(√D S √D) ≤ sup ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`.
@isnad1 id=le.2h3v.s5.2ba760c91f77 from=translated src=- shape=9f192bb8 vocab=a4d3af9f
-/
theorem sumTopTwo_weightedMatrix_le_clConst {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : π₂ (weightedMatrix S w) ≤ clConst ℝ ι 2 := by
  refine sumTopTwo_le' clConst_nonneg fun u v huv => ?_
  refine le_trans ?_ (le_clConst (isUnitWeight_sqrt hw) (projPair_mem_orthProjs huv))
  rw [fanValue_eq_sum_projPair]
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  have h1 : S i j * projPair u v i j ≤ |projPair u v i j| := by
    rcases hS.sign i j with h | h
    · rw [h, one_mul]; exact le_abs_self _
    · rw [h, neg_one_mul]; exact neg_le_abs _
  have h2 : 0 ≤ √(w i) * √(w j) := by positivity
  calc weightedMatrix S w i j * projPair u v i j
      = (√(w i) * √(w j)) * (S i j * projPair u v i j) := by
        simp only [weightedMatrix, of_apply]; ring
    _ ≤ (√(w i) * √(w j)) * |projPair u v i j| := mul_le_mul_of_nonneg_left h1 h2
    _ = √(w i) * √(w j) * ‖projPair u v i j‖ := by rw [Real.norm_eq_abs]

/-- The sign pattern `Sgn(P)` of a real matrix, with the convention `sgn 0 = 1`.-/
noncomputable def signPattern (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  of fun i j => if 0 ≤ P i j then 1 else -1

omit [Fintype ι] in
/--
@isnad1 id=issignma.0h3v.s4.66c1c5f621de from=translated src=- shape=2f9fbb9f vocab=8b14cbf5
-/
lemma isSignMatrix_signPattern {u v : ι → ℝ} : IsSignMatrix (signPattern (projPair u v)) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · have h : projPair u v j i = projPair u v i j := by simp only [projPair_apply]; ring
    simp only [signPattern, of_apply, h]
  · simp only [signPattern, of_apply]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [signPattern, projPair, of_apply]
    exact ite_eq_left (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

omit [Fintype ι] in
/--
@isnad1 id=eq.0h4v.s5.8ea4d5b463d4 from=translated src=- shape=c315c652 vocab=751612c2
-/
lemma signPattern_mul_self (P : Matrix ι ι ℝ) (i j : ι) : signPattern P i j * P i j = |P i j| := by
  simp only [signPattern, of_apply]
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.mp h)]

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ Π(2, ι)` for every unit weight `t` and every `P ∈ 𝒫₂`.
@isnad1 id=le.2h3v.s5.53999ed25ba7 from=translated src=- shape=b120fadf vocab=59535429
-/
theorem weightedAbsSum_le_supConfigs {t : ι → ℝ} (ht : IsUnitWeight t)
    {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι 2) : weightedAbsSum t P ≤ supConfigs ι := by
  obtain ⟨u, v, huv, rfl⟩ := exists_projPair_eq hP
  set w : ι → ℝ := fun i => t i ^ 2 with hw_def
  have hw : IsWeight w := ⟨fun i => sq_nonneg _, ht.sum_sq⟩
  have e : weightedAbsSum t (projPair u v) =
      fanValue (weightedMatrix (signPattern (projPair u v)) w) u v := by
    rw [fanValue_eq_sum_projPair]
    unfold weightedAbsSum
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [weightedMatrix, of_apply, hw_def, Real.sqrt_sq (ht.nonneg _), Real.norm_eq_abs,
      ← signPattern_mul_self]
    ring
  rw [e]
  exact (fanValue_le_sumTopTwo _ huv).trans
    (sumTopTwo_le_supConfigs isSignMatrix_signPattern hw)

/-- `sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖ = 1, P ∈ 𝒫₂ } = Π(2, ι)`.
@isnad1 id=eq.0h1v.s4.b3855f17e585 from=translated src=- shape=71ee8ff5 vocab=a33f7f23
-/
theorem clConst_two_eq_supConfigs : clConst ℝ ι 2 = supConfigs ι :=
  le_antisymm (clConst_le supConfigs_nonneg fun _ _ ht hP => weightedAbsSum_le_supConfigs ht hP)
    (supConfigs_le clConst_nonneg fun _ _ hS hw => sumTopTwo_weightedMatrix_le_clConst hS hw)

/-- **The formula of Chalmers and Lewicki** ([JFA, Theorem 2.1] for `n = 2`):
`Π(2, d) = λ_ℝ(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }`.
@isnad1 id=eq.0h1v.s4.2ebeac22311a from=translated src=- shape=a6d581ba vocab=be1e9a87
-/
theorem maxRelProjConst_two_eq_supConfigs (d : ℕ) :
    maxRelProjConst ℝ 2 d = supConfigs (Fin d) := by
  rw [maxRelProjConst_eq_clConst, clConst_two_eq_supConfigs]

/-- `Π₂ = λ_ℝ(2) = sup_d Π(2, d)`.
@isnad1 id=eq.0h0v.s4.5564c09c38c7 from=translated src=- shape=3f922ecf vocab=57f87571
-/
theorem maxProjConst_two_eq_iSup : maxProjConst ℝ 2 = ⨆ d : ℕ, supConfigs (Fin d) := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  simp_rw [maxRelProjConst_two_eq_supConfigs]

/--
@isnad1 id=bddabove.0h0v.s3.2e41ba6f50ee from=translated src=- shape=7eea9464 vocab=b7955941
-/
lemma bddAbove_range_supConfigs : BddAbove (Set.range fun d : ℕ => supConfigs (Fin d)) :=
  ⟨2, by
    rintro _ ⟨d, rfl⟩
    exact supConfigs_le (by norm_num) fun _ _ hS hw => sumTopTwo_weightedMatrix_le_two hS hw⟩

/--
@isnad1 id=le.0h1v.s4.18d945dc7683 from=translated src=- shape=e08e372a vocab=50663651
-/
lemma supConfigs_le_maxProjConst_two (ι : Type*) [Fintype ι] :
    supConfigs ι ≤ maxProjConst ℝ 2 := by
  rw [maxProjConst_two_eq_iSup, ← supConfigs_congr (Fintype.equivFin ι).symm]
  exact le_ciSup bddAbove_range_supConfigs _

/--
@isnad1 id=le.1h1v.s4.ebc76ebae1c8 from=translated src=- shape=51a34924 vocab=93c50bea
-/
lemma maxProjConst_two_le {c : ℝ} (h : ∀ d : ℕ, supConfigs (Fin d) ≤ c) :
    maxProjConst ℝ 2 ≤ c := by
  rw [maxProjConst_two_eq_iSup]
  exact ciSup_le h

end Grunbaum
