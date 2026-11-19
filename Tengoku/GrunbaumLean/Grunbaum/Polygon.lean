/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.Grunbaum.TwoGraph
import Tengoku.GrunbaumLean.Grunbaum.ThreeGraph
import Tengoku.GrunbaumLean.FranklFuredi.Circle
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.Data.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The matrices `R_{2N+1}`, `R₅` and `A₆`

Let `p₀, …, p_{2N}` be the vertices, in cyclic order, of the regular `(2N+1)`-gon, and let
`T_{2N+1}` be the two-graph on them in which a triple is an edge iff the centre lies in its
convex hull ([JFA, Section 4.1]). "By Section 4.1, we may label the indices of `R_{2N+1}` by
`p₀, …, p_{2N}` such that `[R_{2N+1}] = T_{2N+1}`":

* `Grunbaum.blockR N` is the block matrix `R_{2N+1}` of [JFA, Section 4.1], with the misprint of
  item 8) of the errata corrected, and `Grunbaum.twoGraph_blockR` labels its indices by the
  vertices `p₀, …, p_{2N}` such that `[R_{2N+1}] = T_{2N+1}`. More precisely,
  `Grunbaum.blockR_eq` shows that after this relabelling `R_{2N+1}` becomes, up to switching,
* `Grunbaum.polygonMatrix N`, with `sᵢⱼ = 1` iff `|i - j| ≤ N` for the indices `0, …, 2N`. This
  is the version of `R_{2N+1}` with which we work;
* `Grunbaum.twoGraph_polygonMatrix` : `[R_{2N+1}] = T_{2N+1}`, where `T_{2N+1}` is the circle
  3-graph (Example 2 of Frankl and Füredi, `FranklFuredi.circleGraph`) of the regular polygon
  `Grunbaum.regularPolygon N`;
* **(R1)** `Grunbaum.isCoclique_polygonMatrix` : `{p₀, …, p_N}` is a coclique of `[R_{2N+1}]` with
  `N + 1` elements;
* `Grunbaum.R5 = 𝟙₅ + S(C₅) = J₅ - 2E`, and **(R2)** `Grunbaum.polygonMatrix_two_eq` : `R₅` is
  `R_{2·2+1}` up to switching;
* `Grunbaum.A6 = 𝟙₆ + S(K₁ ∪ C₅)`, and `Grunbaum.pullback_twoGraph_A6` : the 3-graph `S(6)` of
  Frankl and Füredi is `[A₆]` up to relabelling;
* **(A1)** `Grunbaum.A6_eq_certificate` : every `5 × 5` principal submatrix of `A₆` equals `R₅`
  up to switching and permutation (checked with explicit certificates, as in
  *Projection constants in Lean*).
-/

open Finset Matrix Real

namespace Grunbaum

/-! ### `R_{2N+1}` -/

/-- `R_{2N+1}`, with the indices labelled by the vertices `p₀, …, p_{2N}` of the regular
`(2N+1)`-gon in cyclic order: `sᵢⱼ = 1` if `|i - j| ≤ N` and `sᵢⱼ = -1` otherwise.-/
def polygonMatrix (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  of fun i j => if (i : ℕ) ≤ j + N ∧ (j : ℕ) ≤ i + N then 1 else -1

/--
@isnad1 id=issignma.0h1v.s4.30a0ecb502db from=translated src=- shape=a97f289f vocab=7edc7a3f
-/
lemma isSignMatrix_polygonMatrix (N : ℕ) : IsSignMatrix (polygonMatrix N) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · simp only [polygonMatrix, of_apply, and_comm]
  · simp only [polygonMatrix, of_apply]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp [polygonMatrix]

/-- The coherent triples of `R_{2N+1}`: for `i < j < k`, the triple is coherent iff each of the
three gaps `j - i`, `k - j` and `2N + 1 - (k - i)` is at most `N`, i.e. iff the triangle
`pᵢ pⱼ pₖ` contains the centre.
@isnad1 id=iff.2h4v.s8.e1f064a67538 from=translated src=- shape=e993610e vocab=f95ba3c5
-/
theorem coherent_polygonMatrix_iff {N : ℕ} {i j k : Fin (2 * N + 1)} (hij : i < j)
    (hjk : j < k) :
    Coherent (polygonMatrix N) i j k ↔ (j : ℕ) ≤ i + N ∧ (k : ℕ) ≤ j + N ∧ (i : ℕ) + N < k := by
  have hij' : (i : ℕ) < j := hij
  have hjk' : (j : ℕ) < k := hjk
  unfold Coherent polygonMatrix
  simp only [of_apply]
  split_ifs <;> norm_num <;> omega

/-! ### `T_{2N+1}`: the regular polygon -/

/-- The vertices `p₀, …, p_{2N}` of the regular `(2N+1)`-gon on the unit circle.-/
noncomputable def regularPolygon (N : ℕ) (k : Fin (2 * N + 1)) : ℝ × ℝ :=
  (cos (2 * π * k / (2 * N + 1)), sin (2 * π * k / (2 * N + 1)))

/--
@isnad1 id=eq.0h3v.s7.fc9612cd1de6 from=translated src=- shape=aa558d48 vocab=274baf20
-/
lemma det2_regularPolygon (N : ℕ) (i j : Fin (2 * N + 1)) :
    FranklFuredi.det2 (regularPolygon N i) (regularPolygon N j) =
      sin (2 * π * ((j : ℝ) - i) / (2 * N + 1)) := by
  simp only [FranklFuredi.det2, regularPolygon]
  rw [show 2 * π * ((j : ℝ) - i) / (2 * N + 1)
      = 2 * π * j / (2 * N + 1) - 2 * π * i / (2 * N + 1) by ring, sin_sub]
  ring

/--
@isnad1 id=lt.2h2v.s6.7645a659c266 from=translated src=- shape=863e28a7 vocab=afcf4f1f
-/
lemma sin_two_pi_mul_div_pos {n d : ℕ} (hd : 0 < d) (h : 2 * d < n) :
    0 < sin (2 * π * d / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply sin_pos_of_pos_of_lt_pi
  · have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  · rw [div_lt_iff₀ hn]
    have : (2 * d : ℝ) < n := by exact_mod_cast h
    nlinarith [pi_pos]

/--
@isnad1 id=lt.2h2v.s6.2f3c998a9fa5 from=translated src=- shape=d42f7568 vocab=afcf4f1f
-/
lemma sin_two_pi_mul_div_neg {n d : ℕ} (h1 : n < 2 * d) (h2 : d < n) :
    sin (2 * π * d / n) < 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [← sin_sub_two_pi]
  apply sin_neg_of_neg_of_neg_pi_lt
  · have : (d : ℝ) < n := by exact_mod_cast h2
    have : 2 * π * d / n < 2 * π := by
      rw [div_lt_iff₀ hn]
      nlinarith [pi_pos]
    linarith
  · have : (n : ℝ) < 2 * d := by exact_mod_cast h1
    have : π < 2 * π * d / n := by
      rw [lt_div_iff₀ hn]
      nlinarith [pi_pos]
    linarith

/-- For `i < j`, `det(pᵢ, pⱼ) > 0` iff `j - i ≤ N`.
@isnad1 id=iff.1h3v.s7.0181f70f9f7b from=translated src=- shape=0d69575c vocab=f4552840
-/
lemma det2_regularPolygon_pos_iff {N : ℕ} {i j : Fin (2 * N + 1)} (hij : i < j) :
    0 < FranklFuredi.det2 (regularPolygon N i) (regularPolygon N j) ↔ (j : ℕ) ≤ i + N := by
  have hij' : (i : ℕ) < j := hij
  have hj : (j : ℕ) < 2 * N + 1 := j.2
  have e : (j : ℝ) - i = ((j - i : ℕ) : ℝ) := by
    rw [Nat.cast_sub hij'.le]
  rw [det2_regularPolygon, e, show (2 * (N : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring]
  constructor
  · intro h
    by_contra hcon
    exact absurd h (not_lt.mpr (sin_two_pi_mul_div_neg (by omega) (by omega)).le)
  · intro h
    exact sin_two_pi_mul_div_pos (by omega) (by omega)

/--
@isnad1 id=ne.1h3v.s6.b282470c3e14 from=translated src=- shape=943448c8 vocab=163d9192
-/
lemma det2_regularPolygon_ne_zero {N : ℕ} {i j : Fin (2 * N + 1)} (hij : i ≠ j) :
    FranklFuredi.det2 (regularPolygon N i) (regularPolygon N j) ≠ 0 := by
  have key : ∀ a b : Fin (2 * N + 1), a < b →
      FranklFuredi.det2 (regularPolygon N a) (regularPolygon N b) ≠ 0 := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hb : (b : ℕ) < 2 * N + 1 := b.2
    have e : (b : ℝ) - a = ((b - a : ℕ) : ℝ) := by rw [Nat.cast_sub hab'.le]
    rw [det2_regularPolygon, e, show (2 * (N : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring]
    rcases le_or_gt (b - a : ℕ) N with h | h
    · exact (sin_two_pi_mul_div_pos (by omega) (by omega)).ne'
    · exact (sin_two_pi_mul_div_neg (by omega) (by omega)).ne
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [FranklFuredi.det2_antisymm]
    exact neg_ne_zero.mpr (key j i h)

/--
@isnad1 id=genpos.0h1v.s4.920f531caa8b from=translated src=- shape=a97f289f vocab=ebe38ffc
-/
lemma genPos_regularPolygon (N : ℕ) : FranklFuredi.GenPos (regularPolygon N) :=
  fun _ _ h => det2_regularPolygon_ne_zero h

/-- **`[R_{2N+1}] = T_{2N+1}`**: a triple is coherent for `R_{2N+1}` iff the triangle on the
corresponding vertices of the regular `(2N+1)`-gon contains the centre.
@isnad1 id=eq.0h1v.s7.dc50a84b876a from=translated src=- shape=4e293382 vocab=1e141f36
-/
theorem twoGraph_polygonMatrix (N : ℕ) :
    twoGraph (polygonMatrix N) = FranklFuredi.circleGraph (regularPolygon N) := by
  apply FranklFuredi.ThreeGraph.ext_of_lt
  intro a b c hab hbc
  have hac : a < c := hab.trans hbc
  rw [isEdge_twoGraph (isSignMatrix_polygonMatrix N), coherent_polygonMatrix_iff hab hbc,
    FranklFuredi.isEdge_circleGraph_iff_cyc (genPos_regularPolygon N) hab.ne hac.ne hbc.ne]
  have neg_iff : ∀ {p q : Fin (2 * N + 1)}, p < q →
      (FranklFuredi.det2 (regularPolygon N p) (regularPolygon N q) < 0 ↔ ¬(q : ℕ) ≤ p + N) := by
    intro p q hpq
    rw [← det2_regularPolygon_pos_iff hpq, not_lt]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (det2_regularPolygon_ne_zero hpq.ne)⟩
  rw [FranklFuredi.det2_antisymm (regularPolygon N a) (regularPolygon N c)]
  simp only [FranklFuredi.Cyc, neg_pos, neg_lt_zero, det2_regularPolygon_pos_iff hab,
    det2_regularPolygon_pos_iff hbc, det2_regularPolygon_pos_iff hac, neg_iff hab, neg_iff hbc,
    neg_iff hac]
  have hab' : (a : ℕ) < b := hab
  have hbc' : (b : ℕ) < c := hbc
  omega

/-- The regular `(2N+1)`-gon, `N ≥ 1`, is a configuration as in Example 2 of Frankl and Füredi.
@isnad1 id=iscircle.1h1v.s5.8d8eff9efc2c from=translated src=- shape=0ef2f2b2 vocab=3090c74e
-/
theorem isCircleConfig_regularPolygon {N : ℕ} (hN : 1 ≤ N) :
    FranklFuredi.IsCircleConfig (regularPolygon N) where
  injective i j h := by
    by_contra hij
    have := det2_regularPolygon_ne_zero (N := N) hij
    rw [h, FranklFuredi.det2_self] at this
    exact this rfl
  on_circle k := by simp [regularPolygon, cos_sq_add_sin_sq]
  not_mem_line v w hvw :=
    FranklFuredi.not_mem_line_of_det_ne_zero (by simp [regularPolygon, cos_sq_add_sin_sq])
      (det2_regularPolygon_ne_zero hvw)
  mem_convexHull := by
    -- the triangle `p₀ p_N p_{N+1}` contains the centre
    let a : Fin (2 * N + 1) := ⟨0, by omega⟩
    let b : Fin (2 * N + 1) := ⟨N, by omega⟩
    let c : Fin (2 * N + 1) := ⟨N + 1, by omega⟩
    have hab : a < b := Fin.mk_lt_mk.mpr (by omega)
    have hbc : b < c := Fin.mk_lt_mk.mpr (by omega)
    have hedge : (twoGraph (polygonMatrix N)).IsEdge a b c := by
      rw [isEdge_twoGraph (isSignMatrix_polygonMatrix N), coherent_polygonMatrix_iff hab hbc]
      exact ⟨hab.ne, (hab.trans hbc).ne, hbc.ne, by simp [a, b, c]; omega⟩
    rw [twoGraph_polygonMatrix, FranklFuredi.isEdge_circleGraph] at hedge
    refine convexHull_mono ?_ hedge.2.2.2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _

/-! ### (R1) -/

/-- **(R1)** The `N + 1` consecutive vertices `p₀, …, p_N` form a coclique of `[R_{2N+1}]`: they
lie on an open half-circle, so no triangle on them contains the centre.
@isnad1 id=iscocliq.0h1v.s6.40e8f1730847 from=translated src=- shape=465d15a4 vocab=aef74385
-/
theorem isCoclique_polygonMatrix (N : ℕ) :
    IsCoclique (polygonMatrix N)
      (Set.range (Fin.castLE (by omega : N + 1 ≤ 2 * N + 1))) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
  have hi := i.2
  have hj := j.2
  have hk := k.2
  unfold Coherent polygonMatrix
  simp only [of_apply, Fin.val_castLE]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
  norm_num

/-! ### The block matrix `R_{2N+1}` of [JFA, Section 4.1] -/

/-- The matrix `L_N` of [JFA, Section 4.1]: `-1` strictly below the diagonal and `0` elsewhere.-/
def matrixL (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := of fun a b => if b < a then -1 else 0

/-- The block matrix `R_{2N+1}` of [JFA, Section 4.1], with the misprint corrected as in item 8)
of the errata:
`R_{2N+1} = [[1, jᵗ, -jᵗ], [j, J_N, J_N + 2L_N], [-j, J_N + 2L_Nᵗ, J_N]]`,
where `j` is the all-ones vector and `J_N` the all-ones matrix. The first row has the index
`inl ()`, the second block the indices `inr (inl a)` and the third block the indices
`inr (inr b)`.-/
def blockR (N : ℕ) : Matrix (Unit ⊕ (Fin N ⊕ Fin N)) (Unit ⊕ (Fin N ⊕ Fin N)) ℝ :=
  fromBlocks (of fun _ _ => 1) (of fun _ k => Sum.elim (fun _ => 1) (fun _ => -1) k)
    (of fun k _ => Sum.elim (fun _ => 1) (fun _ => -1) k)
    (fromBlocks (of fun _ _ => 1) (of (fun _ _ => 1) + (2 : ℝ) • matrixL N)
      (of (fun _ _ => 1) + (2 : ℝ) • (matrixL N)ᵀ) (of fun _ _ => 1))

/-- The labelling of the indices of `R_{2N+1}` by the vertices `p₀, …, p_{2N}`: the first index
is `p₀`, the second block is `p_{N+1}, …, p_{2N}` and the third block is `p₁, …, p_N`.-/
def blockLabel (N : ℕ) : Unit ⊕ (Fin N ⊕ Fin N) → Fin (2 * N + 1)
  | Sum.inl _ => ⟨0, by omega⟩
  | Sum.inr (Sum.inl a) => ⟨N + 1 + a, by omega⟩
  | Sum.inr (Sum.inr b) => ⟨1 + b, by omega⟩

/-- The switching that relates `R_{2N+1}` to `Grunbaum.polygonMatrix N`: switch the first
index.-/
def blockSign (N : ℕ) : Unit ⊕ (Fin N ⊕ Fin N) → ℝ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

/--
@isnad1 id=issignve.0h1v.s3.f124ca821453 from=translated src=- shape=7daf9227 vocab=042efaf7
-/
lemma isSignVector_blockSign (N : ℕ) : IsSignVector (blockSign N) := by
  rintro (_ | _) <;> simp [blockSign]

/-- `R_{2N+1}` is `polygonMatrix N`, up to switching the first index and relabelling.
@isnad1 id=eq.0h3v.s5.5cca7fe044b3 from=translated src=- shape=629dc6ec vocab=6e0e181f
-/
theorem blockR_eq (N : ℕ) (x y : Unit ⊕ (Fin N ⊕ Fin N)) :
    blockR N x y =
      blockSign N x * blockSign N y * polygonMatrix N (blockLabel N x) (blockLabel N y) := by
  rcases x with _ | a | a <;> rcases y with _ | b | b <;>
    simp only [blockR, blockSign, blockLabel, polygonMatrix, matrixL, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Sum.elim_inl,
      Sum.elim_inr, Matrix.add_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul] <;>
    split_ifs <;> (try norm_num) <;> omega

/--
@isnad1 id=injectiv.0h1v.s5.e0326c19405f from=translated src=- shape=97b4ca62 vocab=1f1ef5b0
-/
lemma blockLabel_injective (N : ℕ) : Function.Injective (blockLabel N) := by
  rintro (_ | a | a) (_ | b | b) h <;>
    simp only [blockLabel, Fin.mk.injEq] at h <;> first | rfl | omega | (congr; ext; omega)

/--
@isnad1 id=bijectiv.0h1v.s5.ce9fd41bcd99 from=translated src=- shape=97b4ca62 vocab=59f954bb
-/
lemma blockLabel_bijective (N : ℕ) : Function.Bijective (blockLabel N) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨blockLabel_injective N, by simp; omega⟩

/--
@isnad1 id=issignma.0h1v.s3.8e7cfa30e178 from=translated src=- shape=7daf9227 vocab=286a822b
-/
lemma isSignMatrix_blockR (N : ℕ) : IsSignMatrix (blockR N) := by
  have h : blockR N = switch ((polygonMatrix N).submatrix (blockLabel N) (blockLabel N))
      (blockSign N) := by
    ext x y
    rw [blockR_eq]
    rfl
  rw [h]
  exact ((isSignMatrix_polygonMatrix N).submatrix _).switch (isSignVector_blockSign N)

/-- **[JFA, Section 4.1]** The indices of `R_{2N+1}` can be labelled by the vertices
`p₀, …, p_{2N}` of the regular `(2N+1)`-gon such that `[R_{2N+1}] = T_{2N+1}`.
@isnad1 id=eq.0h1v.s7.7610b9782c70 from=translated src=- shape=8c448589 vocab=3970c908
-/
theorem twoGraph_blockR (N : ℕ) :
    twoGraph (blockR N) =
      (FranklFuredi.circleGraph (regularPolygon N)).pullback (blockLabel N) := by
  rw [twoGraph_eq_of_switchEquiv (isSignMatrix_blockR N)
      ((isSignMatrix_polygonMatrix N).submatrix (blockLabel N))
      ⟨blockSign N, isSignVector_blockSign N, blockR_eq N⟩,
    twoGraph_submatrix (isSignMatrix_polygonMatrix N), twoGraph_polygonMatrix]

/-! ### `R₅` and (R2) -/

/-- `R₅ = 𝟙₅ + S(C₅) = J₅ - 2E`, where `E` is the adjacency matrix of the `5`-cycle
`0 - 1 - 2 - 3 - 4 - 0`.-/
def R5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ 1, -1,  1,  1, -1;
     -1,  1, -1,  1,  1;
      1, -1,  1, -1,  1;
      1,  1, -1,  1, -1;
     -1,  1,  1, -1,  1]

/--
@isnad1 id=issignma.0h0v.s3.693767512f7c from=translated src=- shape=06f63001 vocab=727bf28e
-/
lemma isSignMatrix_R5 : IsSignMatrix R5 := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [R5]
  · fin_cases a <;> fin_cases b <;> simp [R5]
  · fin_cases a <;> simp [R5]

/-- The signs `(-1)^i` of the switching in (R2).-/
def signsR2 : Fin 5 → ℝ := ![1, -1, 1, -1, 1]

/--
@isnad1 id=issignve.0h0v.s3.71b1cbb13c74 from=translated src=- shape=06f63001 vocab=f59668c2
-/
lemma isSignVector_signsR2 : IsSignVector signsR2 := by
  intro i; fin_cases i <;> simp [signsR2]

/-- **(R2)** `R₅ = 𝟙₅ + S(C₅)` up to switching, where `C₅` is the cycle `p₀p₁p₂p₃p₄`: a triangle
of the regular pentagon contains the centre iff its vertices are not three consecutive ones.
@isnad1 id=eq.0h2v.s5.305214fce267 from=translated src=- shape=b835c8cc vocab=880b9b51
-/
theorem polygonMatrix_two_eq (i j : Fin 5) :
    polygonMatrix 2 i j = signsR2 i * signsR2 j * R5 i j := by
  fin_cases i <;> fin_cases j <;> simp [polygonMatrix, signsR2, R5]

/--
@isnad1 id=switcheq.0h0v.s5.169e7c5f8451 from=translated src=- shape=a21020ea vocab=08e8cdda
-/
lemma switchEquiv_polygonMatrix_two : SwitchEquiv (polygonMatrix 2) R5 :=
  ⟨signsR2, isSignVector_signsR2, polygonMatrix_two_eq⟩

/-! ### `A₆` -/

/-- The integer matrix `A₆`; see `Grunbaum.A6`.-/
def A6Int : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1,  1,  1,  1,  1,  1;
     1,  1,  1,  1, -1, -1;
     1,  1,  1, -1,  1, -1;
     1,  1, -1,  1, -1,  1;
     1, -1,  1, -1,  1,  1;
     1, -1, -1,  1,  1,  1]

/-- The matrix `A₆ = 𝟙₆ + S(K₁ ∪ C₅)` of [JFA, Section 4.1], with indices `0, …, 5`: the vertex
`0` is isolated and `1 - 4 - 3 - 2 - 5 - 1` is a `5`-cycle.-/
def A6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,  1,  1,  1,  1,  1;
     1,  1,  1,  1, -1, -1;
     1,  1,  1, -1,  1, -1;
     1,  1, -1,  1, -1,  1;
     1, -1,  1, -1,  1,  1;
     1, -1, -1,  1,  1,  1]

/--
@isnad1 id=eq.0h2v.s4.6f154c870f50 from=translated src=- shape=3276f4fe vocab=fdcf173c
-/
lemma A6_eq_cast (i j : Fin 6) : A6 i j = (A6Int i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [A6, A6Int]

/--
@isnad1 id=issignma.0h0v.s3.d9238106629a from=translated src=- shape=06f63001 vocab=e28667fa
-/
lemma isSignMatrix_A6 : IsSignMatrix A6 := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [A6]
  · fin_cases a <;> fin_cases b <;> simp [A6]
  · fin_cases a <;> simp [A6]

/--
@isnad1 id=iff.0h3v.s6.cdb90075eb7c from=translated src=- shape=a5b9e43c vocab=a3b9f5dd
-/
lemma coherent_A6_iff (a b c : Fin 6) :
    Coherent A6 a b c ↔ A6Int a b * A6Int a c * A6Int b c = -1 := by
  unfold Coherent
  simp only [A6_eq_cast]
  exact_mod_cast Iff.rfl

/-- The relabelling of `S(6)` onto `[A₆]`: the link `1 - 2 - 4 - 5 - 3` of the vertex `0` in
`S(6)` goes to the link `1 - 4 - 3 - 2 - 5` of `0` in `[A₆]`.-/
def relabelS6 : Fin 6 → Fin 6 := ![0, 1, 4, 5, 3, 2]

/--
@isnad1 id=injectiv.0h0v.s3.9ff419519a0e from=translated src=- shape=44762807 vocab=03af2d49
-/
lemma relabelS6_injective : Function.Injective relabelS6 := by decide

/-- The finite check behind `Grunbaum.pullback_twoGraph_A6`.
@isnad1 id=iff.3h3v.s7.5cd43396a8bb from=translated src=- shape=cb7297f7 vocab=e35e6de3
-/
lemma S6_isEdge_iff_A6Int : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
    (({a, b, c} : Finset (Fin 6)) ∈ FranklFuredi.S6.edges ↔
      A6Int (relabelS6 a) (relabelS6 b) * A6Int (relabelS6 a) (relabelS6 c) *
        A6Int (relabelS6 b) (relabelS6 c) = -1) := by
  decide

/-- The 3-graph `S(6)` of Frankl and Füredi (Example 1) is the two-graph `[A₆]`, up to
relabelling.
@isnad1 id=eq.0h0v.s5.ce2e2ea83b2f from=translated src=- shape=8830befa vocab=0403e157
-/
theorem pullback_twoGraph_A6 : (twoGraph A6).pullback relabelS6 = FranklFuredi.S6 := by
  apply FranklFuredi.ThreeGraph.ext_of_isEdge
  intro a b c hab hac hbc
  rw [FranklFuredi.ThreeGraph.isEdge_pullback, isEdge_twoGraph isSignMatrix_A6, coherent_A6_iff]
  simp only [hab, hac, hbc, ne_eq, not_false_eq_true, true_and,
    relabelS6_injective.ne hab, relabelS6_injective.ne hac, relabelS6_injective.ne hbc]
  exact (S6_isEdge_iff_A6Int a b c hab hac hbc).symm

/-! ### (A1) -/

/-- (A1): relabelling maps `A₆ ∖ {k} → R₅`.-/
def certMap : Fin 6 → Fin 6 → Fin 5 :=
  ![![0, 0, 2, 3, 4, 1], ![0, 0, 2, 3, 1, 4], ![0, 2, 0, 1, 3, 4], ![0, 2, 1, 0, 4, 3],
    ![0, 1, 2, 4, 0, 3], ![0, 1, 4, 2, 3, 0]]

/-- (A1): switching signs for `A₆ ∖ {k} → R₅`.-/
def certSign : Fin 6 → Fin 6 → ℝ :=
  ![![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, -1, -1], ![1, 1, 1, -1, 1, -1], ![1, 1, -1, 1, -1, 1],
    ![1, -1, 1, -1, 1, 1], ![1, -1, -1, 1, 1, 1]]

/--
@isnad1 id=eq.0h2v.s5.58ec2abe8a3a from=translated src=- shape=51ae6a03 vocab=6a2f4fbd
-/
lemma certSign_mul_self (k a : Fin 6) : certSign k a * certSign k a = 1 := by
  fin_cases k <;> fin_cases a <;> simp [certSign]

/-- **(A1)** Every `5 × 5` principal submatrix of `A₆` equals `R₅` up to switching and
permutation. Deleting the isolated vertex leaves `𝟙₅ + S(C₅)`; deleting a vertex of the
`5`-cycle leaves `𝟙₅ + S(K₁ ∪ P₄)`, which becomes a `5`-cycle after switching at the ends of the
path. The certificates `certMap`, `certSign` record these relabellings and switchings.
@isnad1 id=eq.2h3v.s6.17ca158394f6 from=translated src=- shape=d5a63785 vocab=5193050d
-/
theorem A6_eq_certificate (k a b : Fin 6) (ha : a ≠ k) (hb : b ≠ k) :
    A6 a b = certSign k a * certSign k b * R5 (certMap k a) (certMap k b) := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp_all [A6, R5, certMap, certSign]

/--
@isnad1 id=eq.3h3v.s6.439c0be2d541 from=translated src=- shape=bc53314c vocab=56f5ddbc
-/
lemma certMap_injective (k a b : Fin 6) (ha : a ≠ k) (hb : b ≠ k)
    (h : certMap k a = certMap k b) : a = b := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp_all [certMap]

end Grunbaum
