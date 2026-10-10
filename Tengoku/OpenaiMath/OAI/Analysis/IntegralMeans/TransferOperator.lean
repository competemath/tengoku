import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.TransportBoxes

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

def halfMul (z w : halfPlane) : halfPlane := ⟨affine z w,affine_mem z.2 w.2⟩

def halfPoint (x y : ℝ) (hy : 0 < y) : halfPlane :=
  ⟨(x : ℂ)+(y : ℂ)*Complex.I,by simpa [halfPlane]⟩

def horizontal (x : ℝ) : halfPlane := halfPoint x 1 zero_lt_one

lemma halfPoint_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    halfMul (halfPoint x y hy) (halfPoint u v hv) = halfPoint (x+y*u) (y*v) (mul_pos hy hv) := by
  apply Subtype.ext
  apply Complex.ext <;> simp [halfMul,halfPoint,affine]

lemma halfMul_assoc (z w u : halfPlane) : halfMul (halfMul z w) u = halfMul z (halfMul w u) :=
  Subtype.ext (affine_assoc z w u)

lemma halfOne_mul (z : halfPlane) : halfMul halfOne z = z := Subtype.ext (I_affine z)

lemma halfMul_one (z : halfPlane) : halfMul z halfOne = z := Subtype.ext (affine_I z)

lemma continuous_halfPoint.{u_1} {Y : Type u_1} [TopologicalSpace Y] {x y : Y → ℝ}
    (hx : Continuous x) (hy : Continuous y) (hp : ∀ a, 0 < y a) :
    Continuous (fun a => halfPoint (x a) (y a) (hp a)) :=
  ((Complex.continuous_ofReal.comp hx).add ((Complex.continuous_ofReal.comp hy).mul continuous_const)).subtype_mk _

lemma rerootClass_one (g : DiskClass) : rerootClass g halfOne = g := by
  apply class_ext
  intro z hz
  rw [classFun_rerootClass _ _ hz]
  simp [reroot,halfOne,(classFun_schlicht g).2.1,(classFun_schlicht g).2.2]

lemma classWeight_one (g : DiskClass) : classWeight g halfOne = 1 := by
  simp [classWeight,reciprocalDeriv,halfOne,(classFun_schlicht g).2.2]

attribute [local irreducible] rerootClass

def weightAt (z : halfPlane) : C(DiskClass,ℝ) :=
  ⟨fun g => classWeight g z,by
    have hc : Continuous (fun g : DiskClass => (g,z)) := continuous_id.prodMk continuous_const
    exact continuous_classWeight.comp hc⟩

def actionAt (z : halfPlane) : C(DiskClass,DiskClass) :=
  ⟨fun g => rerootClass g z,by
    have hc : Continuous (fun g : DiskClass => (g,z)) := continuous_id.prodMk continuous_const
    exact continuous_rerootClass.comp hc⟩

lemma classFun_identityClass : EqOn (classFun identityClass) identityHalf halfPlane :=
  classFun_classOfHalf identityHalf_schlicht

lemma classWeight_identityClass (z : halfPlane) : classWeight identityClass z = 1 := by
  have hd := classFun_identityClass.deriv isOpen_halfPlane z.2
  have hi : deriv identityHalf z = 1 := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).deriv
  simp [classWeight,reciprocalDeriv,hd,hi]

lemma reroot_identityClass (z : halfPlane) : rerootClass identityClass z = identityClass := by
  apply class_ext
  intro w hw
  rw [classFun_rerootClass _ _ hw,reroot_congr classFun_identityClass z.2 hw,classFun_identityClass hw]
  have hd : deriv identityHalf z = 1 := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).deriv
  have he : (z.val.re : ℂ)+(z.val.im : ℂ)*Complex.I = z := by apply Complex.ext <;> simp
  dsimp [reroot,identityHalf,affine]
  rw [hd,mul_one]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt z.2))).mpr
  linear_combination he

def dyadicLeft : halfPlane := halfPoint (-1/2) (1/2) (by norm_num)

def dyadicRight : halfPlane := halfPoint (1/2) (1/2) (by norm_num)

lemma diskCayley_norm_sq_identity {z : ℂ} (hz : z ∈ halfPlane) :
    (1-‖diskCayley z‖^2)*‖z+Complex.I‖^2 = 4*z.im := by
  have hd : ‖z+Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_den_ne_zero hz)
  rw [diskCayley,norm_div,div_pow]
  field_simp
  rw [Complex.sq_norm,Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

lemma classFun_deriv_norm (g : DiskClass) (z : halfPlane) :
    ‖deriv (classFun g) z‖ = 4*‖deriv (diskExtend g.1) (diskCayley z)‖/‖z.val+Complex.I‖^2 := by
  have hd := (hasDerivAt_diskToHalf g.2.1.1 z.2).deriv
  rw [classFun]
  rw [hd,norm_div,norm_mul,norm_neg,norm_pow]
  norm_num

lemma classFun_reciprocal_norm (g : DiskClass) (z : halfPlane) :
    ‖reciprocalDeriv (classFun g) z‖ = ‖z.val+Complex.I‖^2/
      (4*‖deriv (diskExtend g.1) (diskCayley z)‖) := by
  rw [reciprocalDeriv,norm_inv,classFun_deriv_norm,inv_div]

end Brennan

end

end OAI
