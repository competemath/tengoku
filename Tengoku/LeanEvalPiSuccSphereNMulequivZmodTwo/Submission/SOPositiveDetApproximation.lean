import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOGramSchmidtSmooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative smooth approximation inside the positive-determinant matrices

The positive-determinant matrices form the domain of the smooth
Gram--Schmidt retraction constructed in `SOGramSchmidtSmooth`.  This file
proves the relative approximation step needed before applying that
retraction: a continuous positive-determinant matrix family which is already
smooth near a closed relative set can be approximated by a globally smooth
family, exactly on that set, without ever leaving `det > 0`.

The error tolerance at `x` is half the distance from `f x` to the closed set
`det ≤ 0`.  This avoids any compactness or dimension-dependent determinant
estimate.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff Topology

namespace Submission

set_option autoImplicit false

/-- Decode Euclidean matrix coordinates into an actual matrix.  We use a
Euclidean codomain for smooth approximation because the product-topological
`Matrix` type itself is not equipped with a normed-space instance.-/
def euclideanToMatrix {m : ℕ}
    (v : EuclideanSpace ℝ (Fin m × Fin m)) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => WithLp.ofLp v (i, j)

/-- Encode a matrix as Euclidean coordinates.-/
def matrixToEuclidean {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin m) :=
  WithLp.toLp 2 fun ij => M ij.1 ij.2

/--
@isnad1 id=continuo.0h1v.s6.246eb1b8d690 from=translated src=- shape=fe67561e vocab=c4285bb3
-/
theorem continuous_matrixToEuclidean {m : ℕ} :
    Continuous (matrixToEuclidean (m := m)) := by
  have hraw : Continuous fun M : Matrix (Fin m) (Fin m) ℝ =>
      fun ij : Fin m × Fin m => M ij.1 ij.2 := by
    apply continuous_pi
    intro ij
    exact (continuous_apply ij.2).comp (continuous_apply ij.1)
  unfold matrixToEuclidean
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin m => ℝ)).comp hraw

/--
@isnad1 id=eq.0h2v.s4.72284360029a from=translated src=- shape=257a1ee2 vocab=f8fa08ce
-/
@[simp] theorem euclideanToMatrix_matrixToEuclidean {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) :
    euclideanToMatrix (matrixToEuclidean M) = M := by
  ext i j
  rfl

/--
@isnad1 id=eq.0h2v.s4.a8d9bf1de148 from=translated src=- shape=327cf196 vocab=7e6c5d5b
-/
@[simp] theorem matrixToEuclidean_euclideanToMatrix {m : ℕ}
    (v : EuclideanSpace ℝ (Fin m × Fin m)) :
    matrixToEuclidean (euclideanToMatrix v) = v := by
  apply WithLp.ofLp_injective
  funext ij
  rfl

/--
@isnad1 id=continuo.0h1v.s6.614441c4c377 from=translated src=- shape=56a4c800 vocab=25f6043b
-/
theorem continuous_euclideanToMatrix {m : ℕ} :
    Continuous (euclideanToMatrix (m := m)) := by
  apply continuous_matrix
  intro i j
  exact (EuclideanSpace.proj (i, j)).continuous

/--
@isnad1 id=continuo.0h1v.s6.4c5964488171 from=translated src=- shape=1f80de7e vocab=d1a77c73
-/
theorem continuous_det_euclideanToMatrix {m : ℕ} :
    Continuous fun v : EuclideanSpace ℝ (Fin m × Fin m) =>
      (euclideanToMatrix v).det := by
  have hdet : Continuous fun M : Matrix (Fin m) (Fin m) ℝ => M.det := by
    fun_prop
  exact hdet.comp continuous_euclideanToMatrix

/-- A smooth Euclidean matrix-coordinate family decodes to a matrix with
smooth entries.
@isnad1 id=contdiff.1h5v.s7.21a024d4838d from=translated src=- shape=7f0b16f8 vocab=c86527cb
-/
theorem contDiff_euclideanToMatrix_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {m : ℕ} {g : P → EuclideanSpace ℝ (Fin m × Fin m)}
    (hg : ContDiff ℝ ∞ g) (i j : Fin m) :
    ContDiff ℝ ∞ fun x => euclideanToMatrix (g x) i j := by
  change ContDiff ℝ ∞ ((EuclideanSpace.proj (i, j)) ∘ g)
  exact (EuclideanSpace.proj (i, j)).contDiff.comp hg

/-- The Gram--Schmidt projection is independent of the proof of positivity
and respects equality of its underlying matrices.
@isnad1 id=eq.3h3v.s7.a710fd8ec49a from=translated src=- shape=1c17fd4f vocab=dc5e27e2
-/
theorem matrixGramSchmidtSO_congr {m : ℕ}
    {M N : Matrix (Fin m) (Fin m) ℝ}
    (hMN : M = N) (hM : 0 < M.det) (hN : 0 < N.det) :
    matrixGramSchmidtSO M hM = matrixGramSchmidtSO N hN := by
  subst N
  rfl

/-- Relative smooth approximation of a continuous matrix family inside the
open set of positive-determinant matrices.
@isnad1 id=ex.6h5v.s9.608c0efcbafb from=translated src=- shape=2923a952 vocab=200a612a
-/
theorem exists_contDiff_positiveDet_approx_and_eqOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    {m : ℕ} (hm : 0 < m)
    {f : P → EuclideanSpace ℝ (Fin m × Fin m)}
    (hf : Continuous f)
    (hpos : ∀ x, 0 < (euclideanToMatrix (f x)).det)
    {S U : Set P} (hS : IsClosed S) (hU : U ∈ nhdsSet S)
    (hfU : ContDiffOn ℝ ∞ f U) :
    ∃ g : P → EuclideanSpace ℝ (Fin m × Fin m),
      ContDiff ℝ ∞ g ∧
        (∀ x, 0 < (euclideanToMatrix (g x)).det) ∧ EqOn g f S := by
  let bad : Set (EuclideanSpace ℝ (Fin m × Fin m)) :=
    {v | (euclideanToMatrix v).det ≤ 0}
  have hbadClosed : IsClosed bad := by
    exact isClosed_le continuous_det_euclideanToMatrix continuous_const
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hbadNonempty : bad.Nonempty := by
    refine ⟨0, ?_⟩
    change (euclideanToMatrix (0 : EuclideanSpace ℝ (Fin m × Fin m))).det ≤ 0
    change (0 : Matrix (Fin m) (Fin m) ℝ).det ≤ 0
    simp
  have hfNotBad : ∀ x, f x ∉ bad := by
    intro x hx
    exact (not_le_of_gt (hpos x)) hx
  let eps : P → ℝ := fun x => Metric.infDist (f x) bad / 2
  have hepsContinuous : Continuous eps := by
    exact (Metric.continuous_infDist_pt bad).comp hf |>.div_const 2
  have hepsPos : ∀ x, 0 < eps x := by
    intro x
    have hd : 0 < Metric.infDist (f x) bad :=
      (hbadClosed.notMem_iff_infDist_pos hbadNonempty).mp (hfNotBad x)
    dsimp [eps]
    linarith
  obtain ⟨g, hg, hclose, heq, -⟩ :=
    hf.exists_contDiff_approx_and_eqOn (ε := eps) (⊤ : ℕ∞)
      hepsContinuous hepsPos hS hU hfU
  refine ⟨g, hg, ?_, heq⟩
  intro x
  have hgNotBad : g x ∉ bad := by
    intro hgBad
    have hle : Metric.infDist (f x) bad ≤ dist (f x) (g x) :=
      Metric.infDist_le_dist_of_mem hgBad
    have hlt := hclose x
    rw [dist_comm] at hlt
    dsimp [eps] at hlt
    have hd : 0 < Metric.infDist (f x) bad :=
      (hbadClosed.notMem_iff_infDist_pos hbadNonempty).mp (hfNotBad x)
    linarith
  exact lt_of_not_ge hgNotBad

/-- Relative smoothing of a continuous `SO(m)`-valued family.  The input is
required to be smoothly encoded near the closed relative set; the output is
globally coordinatewise smooth and agrees with the input exactly on that set.

The proof approximates in Euclidean matrix coordinates inside `det > 0` and
then applies the exact Gram--Schmidt retraction.
@isnad1 id=ex.5h5v.s10.1e5ef92b1506 from=translated src=- shape=03fb455f vocab=0f1278a0
-/
theorem exists_contDiff_SO_approx_and_eqOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    {m : ℕ} (hm : 0 < m)
    {R : P → SOGroup m} (hR : Continuous R)
    {S U : Set P} (hS : IsClosed S) (hU : U ∈ nhdsSet S)
    (hRU : ContDiffOn ℝ ∞
      (fun p => matrixToEuclidean
        ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ)) U) :
    ∃ Q : P → SOGroup m,
      (∀ i j, ContDiff ℝ ∞ fun p =>
        ((Q p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ) i j) ∧
      EqOn Q R S := by
  let f : P → EuclideanSpace ℝ (Fin m × Fin m) := fun p =>
    matrixToEuclidean
      ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ)
  have hf : Continuous f :=
    continuous_matrixToEuclidean.comp
      (continuous_SOGroup_val.comp hR)
  have hfpos : ∀ p, 0 < (euclideanToMatrix (f p)).det := by
    intro p
    change 0 < (euclideanToMatrix (matrixToEuclidean
      ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ))).det
    rw [euclideanToMatrix_matrixToEuclidean]
    exact SOGroup_det_pos (R p)
  obtain ⟨g, hg, hgpos, hgeq⟩ :=
    exists_contDiff_positiveDet_approx_and_eqOn hm hf hfpos hS hU hRU
  let Q : P → SOGroup m := fun p =>
    matrixGramSchmidtSO (euclideanToMatrix (g p)) (hgpos p)
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    apply contDiff_matrixGramSchmidtSO_apply
    intro a b
    exact contDiff_euclideanToMatrix_apply hg a b
  · intro p hp
    have hgp : g p = f p := hgeq hp
    have hmatrix : euclideanToMatrix (g p) =
        ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ) := by
      rw [hgp]
      exact euclideanToMatrix_matrixToEuclidean _
    apply Subtype.ext
    change ((matrixGramSchmidtSO (euclideanToMatrix (g p)) (hgpos p) :
      SOGroup m) : Matrix (Fin m) (Fin m) ℝ) =
        ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ)
    calc
      ((matrixGramSchmidtSO (euclideanToMatrix (g p)) (hgpos p) :
          SOGroup m) : Matrix (Fin m) (Fin m) ℝ) =
          ((matrixGramSchmidtSO
            ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ)
            (SOGroup_det_pos (R p)) : SOGroup m) :
              Matrix (Fin m) (Fin m) ℝ) :=
        congrArg Subtype.val
          (matrixGramSchmidtSO_congr hmatrix (hgpos p)
            (SOGroup_det_pos (R p)))
      _ = ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ) :=
        congrArg Subtype.val (matrixGramSchmidtSO_of_SOGroup (R p))

end Submission
