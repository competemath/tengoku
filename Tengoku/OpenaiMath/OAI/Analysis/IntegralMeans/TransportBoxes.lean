import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.GoodPairs

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def displacementWindow (N : ℝ) (z w : ℂ) : Prop :=
  z.im ≤ N*w.im ∧ w.im ≤ N*z.im ∧ |w.re-z.re| ≤ N*z.im

def transportWindow (k N : ℝ) : Set (DiskClass × halfPlane) :=
  {q | q ∈ pairingDomain k ∧
    displacementWindow N q.2 (criticalPair (classFun q.1) k q.2)}

lemma displacementWindow_affine (N : ℝ) {t : ℂ} (ht : t ∈ halfPlane) (z w : ℂ) :
    displacementWindow N (affine t z) (affine t w) ↔ displacementWindow N z w := by
  have him (v : ℂ) : (affine t v).im = t.im*v.im := by simp [affine]
  have hre : (affine t w).re-(affine t z).re = t.im*(w.re-z.re) := by simp [affine]; ring
  simp only [displacementWindow,him,hre,abs_mul,abs_of_pos (show 0<t.im from ht)]
  simp only [show N*(t.im*w.im) = t.im*(N*w.im) from by ring,
    show N*(t.im*z.im) = t.im*(N*z.im) from by ring,
    mul_le_mul_iff_right₀ (show 0<t.im from ht)]

lemma displacementWindow_mono {N M : ℝ} (hNM : N ≤ M) {z w : ℂ}
    (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (h : displacementWindow N z w) :
    displacementWindow M z w :=
  ⟨h.1.trans (mul_le_mul_of_nonneg_right hNM hw.le),
    h.2.1.trans (mul_le_mul_of_nonneg_right hNM hz.le),
    h.2.2.trans (mul_le_mul_of_nonneg_right hNM hz.le)⟩

lemma exists_displacementWindow {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    ∃ n : ℕ, displacementWindow (n+1) z w := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (z.im/w.im) (max (w.im/z.im) (|w.re-z.re|/z.im)))
  refine ⟨n,?_,?_,?_⟩
  · exact (div_le_iff₀ hw).mp ((le_max_left _ _).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_left _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_right _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))

def transportSlice (g : DiskClass) (k N : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ 0 < normalizedJacobian (classFun g) k z ∧
    GoodPair (classFun g) k (criticalMap (classFun g) k z) ∧
    displacementWindow N z (criticalPair (classFun g) k z)}

lemma transportSlice_iff (g : DiskClass) (k N : ℝ) (z : halfPlane) :
    z.val ∈ transportSlice g k N ↔ (g,z) ∈ transportWindow k N := by
  simp only [transportSlice,transportWindow,pairingDomain,mem_ofPred_eq,z.property,true_and,and_assoc]

def transportBox (R a b : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ a ≤ z.im ∧ z.im ≤ b}

lemma measurableSet_transportBox (R a b : ℝ) : MeasurableSet (transportBox R a b) :=
  (measurableSet_le Complex.measurable_re.abs measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const))

lemma pair_mem_enlargedBox {N R Y : ℝ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : z ∈ transportBox R 1 Y) (hw : displacementWindow N z w) :
    w ∈ transportBox (R+N*Y) (1/N) (N*Y) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hab : |w.re| ≤ |z.re|+|w.re-z.re| := by
    calc |w.re| = |z.re+(w.re-z.re)| := by congr 1; ring
         _ ≤ |z.re|+|w.re-z.re| := abs_add_le _ _
  refine ⟨hab.trans (add_le_add hz.1 (hw.2.2.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le))),?_,
    hw.2.1.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le)⟩
  rw [div_le_iff₀ hn]
  nlinarith [hw.1,hz.2.1]

end Brennan

end

end OAI
