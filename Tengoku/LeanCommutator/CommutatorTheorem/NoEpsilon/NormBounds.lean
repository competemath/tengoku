import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.BlockAlgebra
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.Riccati
import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.Analysis.Normed.Algebra.Basic
import Tengoku.Seed.Data.Matrix.ColumnRowPartitioned
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norm budgets for the identity-corner construction

The ring estimates use any submultiplicative norm. Matrix estimates below explicitly
activate the Euclidean operator norm, including for rectangular embedding matrices.
-/

namespace NoEpsilon

section RingBounds

variable {E : Type*} [NormedRing E]

/--
@isnad1 id=le.0h3v.s5.61f7e3ac6dbf from=translated src=- shape=c7d696db vocab=4244dc11
-/
theorem norm_ringCommutator_le (X Y : E) :
    ‖ringCommutator X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc
    ‖ringCommutator X Y‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- A similarity costs at most the product of the norms of its two explicit factors.
@isnad1 id=le.0h4v.s6.9e1970419781 from=translated src=- shape=3bda670b vocab=986bbf18
-/
theorem norm_conjugation_le (S X S' : E) :
    ‖S * X * S'‖ ≤ (‖S‖ * ‖S'‖) * ‖X‖ := by
  calc
    ‖S * X * S'‖ ≤ ‖S * X‖ * ‖S'‖ := norm_mul_le _ _
    _ ≤ (‖S‖ * ‖X‖) * ‖S'‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = (‖S‖ * ‖S'‖) * ‖X‖ := by ring

/--
@isnad1 id=le.3h6v.s6.ddc1d1de604d from=translated src=- shape=59096fd6 vocab=91c9f7e1
-/
theorem norm_firstDefect_le (A U V : E) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ p) :
    ‖ringCommutator U V - A‖ ≤ 2 * p + a := by
  calc
    ‖ringCommutator U V - A‖ ≤ ‖ringCommutator U V‖ + ‖A‖ := norm_sub_le _ _
    _ ≤ 2 * ‖U‖ * ‖V‖ + a := add_le_add (norm_ringCommutator_le _ _) hA
    _ ≤ 2 * 1 * p + a := by gcongr
    _ = 2 * p + a := by ring

/--
@isnad1 id=le.6h9v.s8.14cf5fe3671a from=translated src=- shape=873d8e32 vocab=91c9f7e1
-/
theorem norm_secondDefect_le (A F U K V T : E) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hF : ‖F‖ ≤ a) (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1)
    (hV : ‖V‖ ≤ p) (hT : ‖T‖ ≤ p) :
    ‖ringCommutator K V + (ringCommutator U V - A) * U - K +
      ringCommutator U (T * K) - F‖ ≤ 6 * p + 2 * a + 1 := by
  have hp : 0 ≤ p := (norm_nonneg V).trans hV
  have ha : 0 ≤ a := (norm_nonneg A).trans hA
  have hTK : ‖T * K‖ ≤ p := by
    calc
      ‖T * K‖ ≤ ‖T‖ * ‖K‖ := norm_mul_le _ _
      _ ≤ p * 1 := by gcongr
      _ = p := mul_one p
  have hFirst := norm_firstDefect_le A U V a p hA hU hV
  have hFirstMul : ‖(ringCommutator U V - A) * U‖ ≤ 2 * p + a := by
    calc
      ‖(ringCommutator U V - A) * U‖ ≤ ‖ringCommutator U V - A‖ * ‖U‖ :=
        norm_mul_le _ _
      _ ≤ (2 * p + a) * 1 := by gcongr
      _ = 2 * p + a := mul_one _
  have hCommKV : ‖ringCommutator K V‖ ≤ 2 * p := by
    apply (norm_ringCommutator_le K V).trans
    calc
      2 * ‖K‖ * ‖V‖ ≤ 2 * 1 * p := by gcongr
      _ = 2 * p := by ring
  have hCommUTK : ‖ringCommutator U (T * K)‖ ≤ 2 * p := by
    apply (norm_ringCommutator_le U (T * K)).trans
    calc
      2 * ‖U‖ * ‖T * K‖ ≤ 2 * 1 * p := by gcongr
      _ = 2 * p := by ring
  calc
    ‖ringCommutator K V + (ringCommutator U V - A) * U - K +
        ringCommutator U (T * K) - F‖ ≤
      ‖ringCommutator K V‖ + ‖(ringCommutator U V - A) * U‖ + ‖K‖ +
        ‖ringCommutator U (T * K)‖ + ‖F‖ := by
      calc
        _ ≤ ‖ringCommutator K V + (ringCommutator U V - A) * U - K +
            ringCommutator U (T * K)‖ + ‖F‖ := norm_sub_le _ _
        _ ≤ (‖ringCommutator K V + (ringCommutator U V - A) * U - K‖ +
            ‖ringCommutator U (T * K)‖) + ‖F‖ := by gcongr; apply norm_add_le
        _ ≤ ((‖ringCommutator K V + (ringCommutator U V - A) * U‖ + ‖K‖) +
            ‖ringCommutator U (T * K)‖) + ‖F‖ := by gcongr; apply norm_sub_le
        _ ≤ _ := by gcongr; apply norm_add_le
    _ ≤ 6 * p + 2 * a + 1 := by linarith

/--
@isnad1 id=le.3h8v.s7.df745dcd4c60 from=translated src=- shape=7ce9c417 vocab=b1b4991d
-/
theorem norm_companion_lowerLeft_le (A U K V T Q : E) (p : ℝ)
    (hK : ‖K‖ ≤ 1) (hT : ‖T‖ ≤ p) (hQ : ‖Q - (ringCommutator U V - A)‖ ≤ 1) :
    ‖A + Q - ringCommutator U V + T * K‖ ≤ 1 + p := by
  have hp : 0 ≤ p := (norm_nonneg T).trans hT
  have hId : A + Q - ringCommutator U V + T * K =
      (Q - (ringCommutator U V - A)) + T * K := by noncomm_ring
  rw [hId]
  calc
    _ ≤ ‖Q - (ringCommutator U V - A)‖ + ‖T * K‖ := norm_add_le _ _
    _ ≤ 1 + ‖T‖ * ‖K‖ := add_le_add hQ (norm_mul_le _ _)
    _ ≤ 1 + p * 1 := by gcongr
    _ = 1 + p := by ring

end RingBounds

/-- The dimension-free scale with the two supplied second factors bounded by `2 * a`.-/
noncomputable def identityCornerScale (a : ℝ) : ℝ :=
  2 * max ((5 * a + 1) ^ 2 + (2 * a + 1) * (5 * a + 1) + (14 * a + 1))
    (2 * (5 * a + 1) + 2 * a + 1)

/-- The explicit uniform product budget used by the bounded identity-corner theorem.-/
noncomputable def identityCornerNormBudget (a : ℝ) : ℝ :=
  (1 + (5 * a + 1)) ^ 4 * (identityCornerScale a + 3) *
    ((identityCornerScale a + 5) * (2 * a) + 2)

section MatrixBounds

open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Valid also for an empty index type, where the identity matrix has norm zero.
@isnad1 id=le.0h1v.s5.49a270afe5bb from=translated src=- shape=a3de974d vocab=ddcde8d6
-/
theorem matrix_norm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ ↦ by simp)

/--
@isnad1 id=le.0h1v.s6.c39cfcba61d2 from=translated src=- shape=c1d243c3 vocab=d992d383
-/
theorem norm_rowEmbedding_left_le :
    ‖Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)‖ ≤ 1 := by
  let J := Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  have hJJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hNorm := Matrix.l2_opNorm_conjTranspose_mul_self J
  rw [hJJ] at hNorm
  have hOne : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := matrix_norm_one_le
  change ‖J‖ ≤ 1
  nlinarith [norm_nonneg J]

/--
@isnad1 id=le.0h1v.s6.ac74425e8ed4 from=translated src=- shape=c1d243c3 vocab=d992d383
-/
theorem norm_rowEmbedding_right_le :
    ‖Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  let J := Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
  have hJJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hNorm := Matrix.l2_opNorm_conjTranspose_mul_self J
  rw [hJJ] at hNorm
  have hOne : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := matrix_norm_one_le
  change ‖J‖ ≤ 1
  nlinarith [norm_nonneg J]

/--
@isnad1 id=le.2h3v.s7.c4741db1b67a from=translated src=- shape=413c6a04 vocab=24d6c485
-/
theorem norm_scalar_shift_le (lam : ℝ) (hLam : 0 ≤ lam) (U : Matrix ι ι ℂ)
    (hU : ‖U‖ ≤ 1) : ‖lam • 1 + U‖ ≤ lam + 1 := by
  letI : NormedSpace ℝ (Matrix ι ι ℂ) := NormedSpace.restrictScalars ℝ ℂ _
  calc
    ‖lam • 1 + U‖ ≤ ‖lam • (1 : Matrix ι ι ℂ)‖ + ‖U‖ := norm_add_le _ _
    _ ≤ ‖lam‖ * ‖(1 : Matrix ι ι ℂ)‖ + ‖U‖ :=
      add_le_add (NormedSpace.norm_smul_le lam (1 : Matrix ι ι ℂ)) le_rfl
    _ = lam * ‖(1 : Matrix ι ι ℂ)‖ + ‖U‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hLam]
    _ ≤ lam * 1 + 1 := by gcongr; exact matrix_norm_one_le
    _ = lam + 1 := by ring

/--
@isnad1 id=le.6h9v.s8.e51d00208687 from=translated src=- shape=12c5ebcc vocab=e371119f
-/
theorem norm_riccatiConstant_le (A F U K V T : Matrix ι ι ℂ) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hF : ‖F‖ ≤ a) (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1)
    (hV : ‖V‖ ≤ p) (hT : ‖T‖ ≤ p) :
    ‖riccatiConstant A F U K V T‖ ≤ 6 * p + 2 * a + 1 := by
  exact norm_secondDefect_le A F U K V T a p hA hF hU hK hV hT

/--
@isnad1 id=le.4h7v.s7.002ffc48c57e from=translated src=- shape=c803cce4 vocab=58966c97
-/
theorem norm_riccati_point_le (A U V Q : Matrix ι ι ℂ) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ p)
    (hQ : ‖Q - (ringCommutator U V - A)‖ ≤ 1) :
    ‖Q‖ ≤ 2 * p + a + 1 := by
  have hFirst := norm_firstDefect_le A U V a p hA hU hV
  have h := norm_le_norm_sub_add Q (ringCommutator U V - A)
  linarith

end MatrixBounds

end NoEpsilon
