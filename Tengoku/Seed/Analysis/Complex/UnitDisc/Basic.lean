/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Complex.Circle
public import Tengoku.Seed.Analysis.Normed.Module.Ball.Action
public import Tengoku.Seed.Algebra.Group.NatPowAssoc
public import Tengoku.Seed.Algebra.Group.PNatPowAssoc

/-!
# Poincaré disc

In this file we define `Complex.UnitDisc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/

@[expose] public section

open Set Function Metric Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Complex

/-- The complex unit disc, denoted as `𝔻` within the Complex namespace -/
def UnitDisc : Type :=
  Subsemigroup.unitBall ℂ deriving TopologicalSpace

/-- The complex closed unit disc, denoted as `𝕔𝔻` within the Complex namespace -/
def UnitClosedDisc : Type :=
  Submonoid.unitClosedBall ℂ deriving TopologicalSpace

@[inherit_doc] scoped[Complex.UnitDisc] notation "𝔻" => Complex.UnitDisc
@[inherit_doc] scoped[Complex.UnitDisc] notation "𝕔𝔻" => Complex.UnitClosedDisc

open UnitDisc

namespace UnitDisc

/-- Coercion to `ℂ`. -/
@[coe] protected def coe : 𝔻 → ℂ := Subtype.val

instance instCommSemigroup : CommSemigroup UnitDisc := inferInstanceAs <| CommSemigroup (ball _ _)

instance instSemigroupWithZero : SemigroupWithZero UnitDisc :=
  inferInstanceAs <| SemigroupWithZero (ball _ _)

/--
@isnad1 id=iscancel.0h0v.s3.b9c5a83245bd from=seed src=0 shape=49959d42 vocab=7e1d7a27
-/
instance instIsCancelMulZero : IsCancelMulZero UnitDisc :=
  inferInstanceAs <| IsCancelMulZero (ball _ _)

instance instHasDistribNeg : HasDistribNeg UnitDisc :=
  inferInstanceAs <| HasDistribNeg (ball _ _)

instance instCoe : Coe UnitDisc ℂ := ⟨UnitDisc.coe⟩

/--
@isnad1 id=injectiv.0h0v.s2.5091dfef556f from=seed src=0 shape=54c8eceb vocab=34b49e8f
-/
@[ext]
theorem coe_injective : Injective ((↑) : 𝔻 → ℂ) :=
  Subtype.coe_injective

/--
@isnad1 id=iff.0h2v.s3.e6e2b9a29bd9 from=seed src=0 shape=e5555f7a vocab=2db65abb
-/
@[simp, norm_cast]
theorem coe_inj {z w : 𝔻} : (z : ℂ) = w ↔ z = w := Subtype.val_inj

/--
@isnad1 id=isembedd.0h0v.s4.8a1db35722a1 from=seed src=0 shape=54c8eceb vocab=f0d25a1a
-/
@[fun_prop]
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝔻 → ℂ) := .subtypeVal

/--
@isnad1 id=continuo.0h0v.s4.1389ed4d0e81 from=seed src=0 shape=54c8eceb vocab=373844ef
-/
@[fun_prop]
theorem continuous_coe : Continuous ((↑) : 𝔻 → ℂ) := isEmbedding_coe.continuous

/--
@isnad1 id=lt.0h1v.s4.cdce654b6c84 from=seed src=0 shape=8e1bdd70 vocab=5d4f9304
-/
theorem norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ < 1 :=
  mem_ball_zero_iff.1 z.2

/--
@isnad1 id=ne.0h1v.s3.f32390df547b from=seed src=0 shape=8e1bdd70 vocab=f51084c8
-/
theorem norm_ne_one (z : 𝔻) : ‖(z : ℂ)‖ ≠ 1 :=
  z.norm_lt_one.ne

/--
@isnad1 id=lt.0h1v.s5.2f06c9539211 from=seed src=0 shape=4e514d93 vocab=17c93710
-/
theorem sq_norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one, abs_norm]
  exact z.norm_lt_one

/--
@isnad1 id=lt.0h1v.s5.f62421aa7154 from=seed src=0 shape=7f9308c0 vocab=75fcf154
-/
theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  rw [← Complex.norm_mul_self_eq_normSq, ← sq]
  exact z.sq_norm_lt_one

/--
@isnad1 id=ne.0h1v.s3.9ded09242916 from=seed src=0 shape=a311c14d vocab=2db65abb
-/
theorem coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
  ne_of_apply_ne (‖·‖) <| by simp [z.norm_ne_one]

/--
@isnad1 id=ne.0h1v.s3.9b3d5c6b3a8d from=seed src=0 shape=febfe86d vocab=27d85720
-/
theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne (‖·‖) <| by simpa [norm_neg] using z.norm_ne_one

/--
@isnad1 id=ne.0h1v.s4.b3411c706295 from=seed src=0 shape=5d131662 vocab=493e5dd7
-/
theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

/--
@isnad1 id=eq.0h2v.s4.826be48f0875 from=seed src=0 shape=0438c7a3 vocab=bff9bcf1
-/
@[simp, norm_cast]
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.f57b21b77608 from=seed src=0 shape=5a02da31 vocab=27d85720
-/
@[simp, norm_cast]
theorem coe_neg (z : 𝔻) : ↑(-z) = (-z : ℂ) := rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : ‖z‖ < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

instance : CanLift ℂ 𝔻 (↑) (‖·‖ < 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
protected def casesOn {motive : 𝔻 → Sort*} (mk : ∀ z hz, motive (.mk z hz)) (z : 𝔻) :
    motive z :=
  mk z z.norm_lt_one

/--
@isnad1 id=eq.1h3v.s5.596dcd73ba63 from=seed src=0 shape=fb7dcb7d vocab=bab12c47
-/
@[simp]
theorem casesOn_mk {motive : 𝔻 → Sort*} (mk' : ∀ z hz, motive (.mk z hz)) {z : ℂ} (hz : ‖z‖ < 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

/--
@isnad1 id=eq.1h1v.s4.4b8151c1f83a from=seed src=0 shape=21d6d4cc vocab=9f6f9af0
-/
@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ < 1) : (mk z hz : ℂ) = z :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.1dddc81ccc34 from=seed src=0 shape=59614351 vocab=58d081f6
-/
@[simp]
theorem mk_coe (z : 𝔻) (hz : ‖(z : ℂ)‖ < 1 := z.norm_lt_one) : mk z hz = z :=
  Subtype.eta _ _

/--
@isnad1 id=iff.2h2v.s5.cb58013e5be7 from=seed src=0 shape=3359be94 vocab=3bf6a3b9
-/
@[simp]
theorem mk_inj {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk

protected theorem «forall» {p : 𝔻 → Prop} : (∀ z, p z) ↔ ∀ z hz, p (mk z hz) :=
  ⟨fun h z hz ↦ h (mk z hz), fun h z ↦ h z z.norm_lt_one⟩

protected theorem «exists» {p : 𝔻 → Prop} : (∃ z, p z) ↔ ∃ z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ ↦ ⟨z, z.norm_lt_one, hz⟩, fun ⟨z, hz, h⟩ ↦ ⟨mk z hz, h⟩⟩

/--
@isnad1 id=eq.1h1v.s7.b8194b7d7899 from=seed src=0 shape=eb1723de vocab=9f4a49dc
-/
@[simp]
theorem mk_neg (z : ℂ) (hz : ‖-z‖ < 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

/--
@isnad1 id=eq.0h0v.s4.edc4f0e9f150 from=seed src=0 shape=1ac31801 vocab=2db65abb
-/
@[simp]
theorem coe_zero : ((0 : 𝔻) : ℂ) = 0 :=
  rfl

/--
@isnad1 id=iff.0h1v.s4.6a7407ab311b from=seed src=0 shape=3a75f94e vocab=2db65abb
-/
@[simp]
theorem coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

/--
@isnad1 id=eq.0h0v.s4.975e9fc1422c from=seed src=0 shape=7733297d vocab=e5be2656
-/
@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl

/--
@isnad1 id=iff.1h1v.s5.3eaf67c03cf5 from=seed src=0 shape=8bcea562 vocab=3bf6a3b9
-/
@[simp] theorem mk_eq_zero {z : ℂ} (hz : ‖z‖ < 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

instance : Inhabited 𝔻 :=
  ⟨0⟩

instance instMulActionCircle : MulAction Circle 𝔻 :=
  inferInstanceAs <| MulAction (sphere _ _) (ball _ _)

/--
@isnad1 id=isscalar.0h0v.s6.95448a39bb77 from=seed src=0 shape=e3d48bcb vocab=fc1dce59
-/
instance instIsScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
  inferInstanceAs <| IsScalarTower (sphere _ _) (sphere _ _) (ball _ _)

/--
@isnad1 id=isscalar.0h0v.s5.3782f7a5ba47 from=seed src=0 shape=54c8eceb vocab=fc1dce59
-/
instance instIsScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
  inferInstanceAs <| IsScalarTower (sphere _ _) (ball _ _) (ball _ _)

/--
@isnad1 id=smulcomm.0h0v.s5.409437de1b5c from=seed src=0 shape=54c8eceb vocab=796c9210
-/
instance instSMulCommClass_circle_left : SMulCommClass Circle 𝔻 𝔻 :=
  inferInstanceAs <| SMulCommClass (sphere _ _) (ball _ _) (ball _ _)

/--
@isnad1 id=smulcomm.0h0v.s5.c56d5491395e from=seed src=0 shape=e3d48bcb vocab=796c9210
-/
instance instSMulCommClass_circle_right : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

/--
@isnad1 id=eq.0h2v.s6.c35beee6b49f from=seed src=0 shape=a70ceace vocab=d3fc04fa
-/
@[simp, norm_cast]
theorem coe_circle_smul (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

instance : Pow UnitDisc ℕ+ where
  pow z n := ⟨z ^ (n : ℕ), by simp [pow_lt_one_iff_of_nonneg, z.norm_lt_one]⟩

/--
@isnad1 id=eq.0h2v.s5.65092d15d758 from=seed src=0 shape=4f7f24ce vocab=34fd69ee
-/
@[simp, norm_cast]
theorem coe_pow (z : 𝔻) (n : ℕ+) : ((z ^ n : 𝔻) : ℂ) = z ^ (n : ℕ) := rfl

/--
@isnad1 id=continuo.0h1v.s4.f517cb297a78 from=seed src=0 shape=786514b0 vocab=8a8e7674
-/
@[fun_prop]
theorem continuous_pow (n : ℕ+) : Continuous (· ^ n : 𝔻 → 𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

/--
@isnad1 id=iff.0h2v.s5.0f13a0276c05 from=seed src=0 shape=6c54eb55 vocab=b6734755
-/
@[simp]
theorem pow_eq_zero {z : 𝔻} {n : ℕ+} : z ^ n = 0 ↔ z = 0 := by
  rw [← coe_inj, coe_pow]
  simp

instance : PNatPowAssoc 𝔻 where
  ppow_add m n z := mod_cast pow_add (z : ℂ) m n
  ppow_one z := by simp [← coe_inj]

/--
@isnad1 id=tendsto.0h1v.s5.59abe6182230 from=seed src=0 shape=2eaeda17 vocab=cc44171c
-/
theorem tendsto_pow_atTop_nhds_zero (z : 𝔻) :
    Tendsto (fun n : ℕ+ ↦ z ^ n) atTop (𝓝 0) := by
  simp only [isEmbedding_coe.tendsto_nhds_iff, comp_def, coe_pow]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr z.norm_lt_one
    |>.comp tendsto_PNat_val_atTop_atTop

/-- Real part of a point of the unit disc. -/
def re (z : 𝔻) : ℝ :=
  Complex.re z

/-- Imaginary part of a point of the unit disc. -/
def im (z : 𝔻) : ℝ :=
  Complex.im z

/--
@isnad1 id=eq.0h1v.s3.1159bdac9f66 from=seed src=0 shape=7718e021 vocab=bd47fe73
-/
@[simp, norm_cast]
theorem re_coe (z : 𝔻) : (z : ℂ).re = z.re :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.d7fb20d90872 from=seed src=0 shape=7718e021 vocab=bf6949df
-/
@[simp, norm_cast]
theorem im_coe (z : 𝔻) : (z : ℂ).im = z.im :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.68de2857bbae from=seed src=0 shape=5a02da31 vocab=b0bb0c92
-/
@[simp]
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.300efe6180b3 from=seed src=0 shape=5a02da31 vocab=ae6e0541
-/
@[simp]
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl

/--
@isnad1 id=eq.0h0v.s4.9102cd033e77 from=seed src=0 shape=1ac31801 vocab=c76c83f8
-/
@[simp] theorem re_zero : re 0 = 0 := rfl
/--
@isnad1 id=eq.0h0v.s4.e549a5cccc53 from=seed src=0 shape=1ac31801 vocab=1e4f9b75
-/
@[simp] theorem im_zero : im 0 = 0 := rfl

/-- Conjugate point of the unit disc. -/
instance : Star 𝔻 where
  star z := mk (conj z) <| (norm_conj z).symm ▸ z.norm_lt_one

/--
@isnad1 id=eq.0h1v.s5.d3d9fa11342c from=seed src=0 shape=40757b00 vocab=685407b2
-/
@[simp] theorem coe_star (z : 𝔻) : (↑(star z) : ℂ) = conj ↑z := rfl

/--
@isnad1 id=iff.0h1v.s5.fac2cc285bd9 from=seed src=0 shape=c7b1302f vocab=d09e8c71
-/
@[simp]
protected theorem star_eq_zero {z : 𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

/--
@isnad1 id=eq.0h0v.s4.45372cf19a36 from=seed src=0 shape=d8786388 vocab=d09e8c71
-/
@[simp]
protected theorem star_zero : star (0 : 𝔻) = 0 := by simp

instance : InvolutiveStar 𝔻 where
  star_involutive z := by ext; simp

/--
@isnad1 id=eq.0h1v.s5.ffe5fa545e4c from=seed src=0 shape=d7ff289e vocab=9bb04c3f
-/
@[simp] protected theorem star_neg (z : 𝔻) : star (-z) = -(star z) := rfl

/--
@isnad1 id=eq.0h1v.s3.7f71a3ec9a89 from=seed src=0 shape=8fc7e33b vocab=277cab97
-/
@[simp] protected theorem re_star (z : 𝔻) : (star z).re = z.re := rfl

/--
@isnad1 id=eq.0h1v.s3.966df1a67251 from=seed src=0 shape=5a02da31 vocab=b6eeeec0
-/
@[simp] protected theorem im_star (z : 𝔻) : (star z).im = -z.im := rfl

instance : StarMul 𝔻 where
  star_mul z w := coe_injective <| by simp [mul_comm]

end UnitDisc

namespace UnitClosedDisc

/-- Coercion to `ℂ`. -/
@[coe] protected def coe : 𝕔𝔻 → ℂ := Subtype.val

instance : MonoidWithZero 𝕔𝔻 := inferInstanceAs <| MonoidWithZero (closedBall _ _)

instance : IsCancelMulZero 𝕔𝔻 :=
  inferInstanceAs <| IsCancelMulZero (closedBall _ _)

instance : HasDistribNeg 𝕔𝔻 :=
  inferInstanceAs <| HasDistribNeg (closedBall _ _)

instance : Coe 𝕔𝔻 ℂ := ⟨UnitClosedDisc.coe⟩

/--
@isnad1 id=injectiv.0h0v.s2.06633ef6e58a from=seed src=0 shape=54c8eceb vocab=404fc296
-/
@[ext]
theorem coe_injective : Injective ((↑) : 𝕔𝔻 → ℂ) :=
  Subtype.coe_injective

/--
@isnad1 id=iff.0h2v.s3.2a3060018542 from=seed src=0 shape=e5555f7a vocab=39d023c4
-/
@[simp, norm_cast]
theorem coe_inj {z w : 𝕔𝔻} : (z : ℂ) = w ↔ z = w := Subtype.val_inj

/--
@isnad1 id=isembedd.0h0v.s4.84a4d92a5bfe from=seed src=0 shape=54c8eceb vocab=252c2f36
-/
@[fun_prop]
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝕔𝔻 → ℂ) := .subtypeVal

/--
@isnad1 id=continuo.0h0v.s4.b522f018056f from=seed src=0 shape=54c8eceb vocab=01371ca9
-/
@[fun_prop]
theorem continuous_coe : Continuous ((↑) : 𝕔𝔻 → ℂ) := isEmbedding_coe.continuous

/--
@isnad1 id=le.0h1v.s4.ce010c55cdd1 from=seed src=0 shape=8e1bdd70 vocab=a4474bad
-/
theorem norm_le_one (z : 𝕔𝔻) : ‖(z : ℂ)‖ ≤ 1 :=
  mem_closedBall_zero_iff.1 z.2

/--
@isnad1 id=le.0h1v.s5.54ca125fcb28 from=seed src=0 shape=4e514d93 vocab=6529c1b1
-/
theorem sq_norm_lt_one (z : 𝕔𝔻) : ‖(z : ℂ)‖ ^ 2 ≤ 1 := by
  rw [sq_le_one_iff_abs_le_one, abs_norm]
  exact z.norm_le_one

/--
@isnad1 id=le.0h1v.s5.5aa97fe90a4a from=seed src=0 shape=7f9308c0 vocab=b27f8394
-/
theorem normSq_lt_one (z : 𝕔𝔻) : normSq z ≤ 1 := by
  rw [← Complex.norm_mul_self_eq_normSq, ← sq]
  exact z.sq_norm_lt_one

/--
@isnad1 id=eq.0h2v.s5.d29016b54076 from=seed src=0 shape=0438c7a3 vocab=89461864
-/
@[simp, norm_cast]
theorem coe_mul (z w : 𝕔𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.acd8c507d83b from=seed src=0 shape=5a02da31 vocab=89eb7bd1
-/
@[simp, norm_cast]
theorem coe_neg (z : 𝕔𝔻) : ↑(-z) = (-z : ℂ) := rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝕔𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : ‖z‖ ≤ 1) : 𝕔𝔻 :=
  ⟨z, mem_closedBall_zero_iff.2 hz⟩

instance : CanLift ℂ 𝕔𝔻 (↑) (‖·‖ ≤ 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitClosedDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
protected def casesOn {motive : 𝕔𝔻 → Sort*} (mk : ∀ z hz, motive (.mk z hz)) (z : 𝕔𝔻) :
    motive z :=
  mk z z.norm_le_one

/--
@isnad1 id=eq.1h3v.s5.1dbfa98b2c54 from=seed src=0 shape=fb7dcb7d vocab=7c768b57
-/
@[simp]
theorem casesOn_mk {motive : 𝕔𝔻 → Sort*} (mk' : ∀ z hz, motive (.mk z hz)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

/--
@isnad1 id=eq.1h1v.s4.f2078d0c5ae8 from=seed src=0 shape=21d6d4cc vocab=dfb27525
-/
@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ ≤ 1) : (mk z hz : ℂ) = z :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.6d500be3c4d7 from=seed src=0 shape=59614351 vocab=163d3387
-/
@[simp]
theorem mk_coe (z : 𝕔𝔻) (hz : ‖(z : ℂ)‖ ≤ 1 := z.norm_le_one) : mk z hz = z :=
  Subtype.eta _ _

/--
@isnad1 id=iff.2h2v.s5.52f871e5972c from=seed src=0 shape=3359be94 vocab=e8c5077a
-/
@[simp]
theorem mk_inj {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk

protected theorem «forall» {p : 𝕔𝔻 → Prop} : (∀ z, p z) ↔ ∀ z hz, p (mk z hz) :=
  ⟨fun h z hz ↦ h (mk z hz), fun h z ↦ h z z.norm_le_one⟩

protected theorem «exists» {p : 𝕔𝔻 → Prop} : (∃ z, p z) ↔ ∃ z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ ↦ ⟨z, z.norm_le_one, hz⟩, fun ⟨z, hz, h⟩ ↦ ⟨mk z hz, h⟩⟩

/--
@isnad1 id=eq.1h1v.s7.ce96692036eb from=seed src=0 shape=eb1723de vocab=4d4e24d8
-/
@[simp]
theorem mk_neg (z : ℂ) (hz : ‖-z‖ ≤ 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

/--
@isnad1 id=eq.0h0v.s4.4115855c7c85 from=seed src=0 shape=1ac31801 vocab=39d023c4
-/
@[simp]
theorem coe_zero : ((0 : 𝕔𝔻) : ℂ) = 0 :=
  rfl

/--
@isnad1 id=iff.0h1v.s4.cfd5be2a48c6 from=seed src=0 shape=3a75f94e vocab=39d023c4
-/
@[simp]
theorem coe_eq_zero {z : 𝕔𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

/--
@isnad1 id=eq.0h0v.s4.9196bbee3099 from=seed src=0 shape=7733297d vocab=7083a915
-/
@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl

/--
@isnad1 id=iff.1h1v.s5.fb7fb671012b from=seed src=0 shape=8bcea562 vocab=e8c5077a
-/
@[simp] theorem mk_eq_zero {z : ℂ} (hz : ‖z‖ ≤ 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

/--
@isnad1 id=eq.0h0v.s4.f6b96da44272 from=seed src=0 shape=1ac31801 vocab=39d023c4
-/
@[simp]
theorem coe_one : ((1 : 𝕔𝔻) : ℂ) = 1 :=
  rfl

/--
@isnad1 id=iff.0h1v.s4.a180637987f2 from=seed src=0 shape=3a75f94e vocab=39d023c4
-/
@[simp]
theorem coe_eq_one {z : 𝕔𝔻} : (z : ℂ) = 1 ↔ z = 1 :=
  coe_injective.eq_iff' coe_one

/--
@isnad1 id=eq.0h0v.s4.986b33bcb8d0 from=seed src=0 shape=7733297d vocab=939be4f3
-/
@[simp] theorem mk_one : mk 1 (by simp) = 1 := rfl

/--
@isnad1 id=iff.1h1v.s5.5427b4fee5ca from=seed src=0 shape=8bcea562 vocab=e8c5077a
-/
@[simp] theorem mk_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1) : mk z hz = 1 ↔ z = 1 := by simp [← coe_inj]

instance : Inhabited 𝕔𝔻 :=
  ⟨0⟩

instance : MulAction Circle 𝕔𝔻 :=
  inferInstanceAs <| MulAction (sphere _ _) (closedBall _ _)

instance : IsScalarTower Circle Circle 𝕔𝔻 :=
  inferInstanceAs <| IsScalarTower (sphere _ _) (sphere _ _) (closedBall _ _)

instance : IsScalarTower Circle 𝕔𝔻 𝕔𝔻 :=
  isScalarTower_sphere_closedBall_closedBall

instance : SMulCommClass Circle 𝕔𝔻 𝕔𝔻 :=
  instSMulCommClass_sphere_closedBall_closedBall

instance : SMulCommClass 𝕔𝔻 Circle 𝕔𝔻 :=
  SMulCommClass.symm _ _ _

instance instMulActionClosedBall : MulAction 𝕔𝔻 𝔻 :=
  inferInstanceAs <| MulAction (closedBall _ _) (ball _ _)

/--
@isnad1 id=isscalar.0h0v.s5.f02e02162144 from=seed src=0 shape=e3d48bcb vocab=33569349
-/
instance instIsScalarTower_closedBall_closedBall :
    IsScalarTower 𝕔𝔻 𝕔𝔻 𝔻 :=
  inferInstanceAs <| IsScalarTower (closedBall _ _) (closedBall _ _) (ball _ _)

/--
@isnad1 id=isscalar.0h0v.s5.5f0976740a2e from=seed src=0 shape=54c8eceb vocab=33569349
-/
instance instIsScalarTower_closedBall : IsScalarTower 𝕔𝔻 𝔻 𝔻 :=
  inferInstanceAs <| IsScalarTower (closedBall _ _) (ball _ _) (ball _ _)

/--
@isnad1 id=smulcomm.0h0v.s4.b351fe47720e from=seed src=0 shape=54c8eceb vocab=3f2126df
-/
instance instSMulCommClass_closedBall_left : SMulCommClass 𝕔𝔻 𝔻 𝔻 :=
  ⟨fun _ _ _ => Subtype.ext <| mul_left_comm _ _ _⟩

/--
@isnad1 id=smulcomm.0h0v.s4.305db3e9acd9 from=seed src=0 shape=e3d48bcb vocab=3f2126df
-/
instance instSMulCommClass_closedBall_right : SMulCommClass 𝔻 𝕔𝔻 𝔻 :=
  SMulCommClass.symm _ _ _

/--
@isnad1 id=smulcomm.0h0v.s5.03c36d9edb4a from=seed src=0 shape=54c8eceb vocab=318c0d2f
-/
instance instSMulCommClass_circle_closedBall : SMulCommClass Circle 𝕔𝔻 𝔻 :=
  inferInstanceAs <| SMulCommClass (sphere _ _) (closedBall _ _) (ball _ _)

/--
@isnad1 id=smulcomm.0h0v.s5.1fed10523756 from=seed src=0 shape=54c8eceb vocab=318c0d2f
-/
instance instSMulCommClass_closedBall_circle : SMulCommClass 𝕔𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

/--
@isnad1 id=eq.0h2v.s5.efec1657b5ff from=seed src=0 shape=9625df87 vocab=f89847f4
-/
@[simp, norm_cast]
theorem coe_closedBall_smul (z : 𝕔𝔻) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.ca10729da2a4 from=seed src=0 shape=a70ceace vocab=135973f7
-/
@[simp, norm_cast]
theorem coe_circle_smul (z : Circle) (w : 𝕔𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

instance : SMulCommClass 𝕔𝔻 Circle 𝕔𝔻 :=
  SMulCommClass.symm _ _ _

instance : Pow 𝕔𝔻 ℕ where
  pow z n := ⟨z ^ n, by simp [pow_le_one₀ (norm_nonneg _) z.norm_le_one]⟩

/--
@isnad1 id=eq.0h2v.s5.c557a75b5530 from=seed src=0 shape=d14eb2af vocab=40f12fe2
-/
@[simp, norm_cast]
theorem coe_pow (z : 𝕔𝔻) (n : ℕ) : ((z ^ n : 𝕔𝔻) : ℂ) = z ^ (n : ℕ) := rfl

/--
@isnad1 id=continuo.0h1v.s4.a35bc97adda7 from=seed src=0 shape=786514b0 vocab=1ff58e4b
-/
@[fun_prop]
theorem continuous_pow (n : ℕ) : Continuous (· ^ n : 𝕔𝔻 → 𝕔𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

instance : NatPowAssoc 𝕔𝔻 where
  npow_add m n z := mod_cast pow_add (z : ℂ) m n
  npow_one z := by simp [← coe_inj]
  npow_zero z := by simp [← coe_inj]

/-- Real part of a point of the unit disc. -/
def re (z : 𝕔𝔻) : ℝ :=
  Complex.re z

/-- Imaginary part of a point of the unit disc. -/
def im (z : 𝕔𝔻) : ℝ :=
  Complex.im z

/--
@isnad1 id=eq.0h1v.s3.4e15190d4c06 from=seed src=0 shape=7718e021 vocab=c5267e44
-/
@[simp, norm_cast]
theorem re_coe (z : 𝕔𝔻) : (z : ℂ).re = z.re :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.fad05244b36c from=seed src=0 shape=7718e021 vocab=c482c175
-/
@[simp, norm_cast]
theorem im_coe (z : 𝕔𝔻) : (z : ℂ).im = z.im :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.f15d386f8dbb from=seed src=0 shape=5a02da31 vocab=ce60f7f2
-/
@[simp]
theorem re_neg (z : 𝕔𝔻) : (-z).re = -z.re :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.79bf0a1fd104 from=seed src=0 shape=5a02da31 vocab=cfd8f839
-/
@[simp]
theorem im_neg (z : 𝕔𝔻) : (-z).im = -z.im :=
  rfl

/--
@isnad1 id=eq.0h0v.s4.22f516347847 from=seed src=0 shape=1ac31801 vocab=d8704154
-/
@[simp] theorem re_zero : re 0 = 0 := rfl
/--
@isnad1 id=eq.0h0v.s4.94aa4aa181da from=seed src=0 shape=1ac31801 vocab=021e9aae
-/
@[simp] theorem im_zero : im 0 = 0 := rfl

/-- Conjugate point of the unit disc. -/
instance : Star 𝕔𝔻 where
  star z := mk (conj z) <| (norm_conj z).symm ▸ z.norm_le_one

/--
@isnad1 id=eq.0h1v.s5.3158b2c7e697 from=seed src=0 shape=40757b00 vocab=d0b77a05
-/
@[simp] theorem coe_star (z : 𝕔𝔻) : (↑(star z) : ℂ) = conj ↑z := rfl

/--
@isnad1 id=iff.0h1v.s5.684898de4ab6 from=seed src=0 shape=c7b1302f vocab=d50dec84
-/
@[simp]
protected theorem star_eq_zero {z : 𝕔𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

/--
@isnad1 id=eq.0h0v.s4.57790938a0f3 from=seed src=0 shape=d8786388 vocab=d50dec84
-/
@[simp]
protected theorem star_zero : star (0 : 𝕔𝔻) = 0 := by simp

instance : InvolutiveStar 𝕔𝔻 where
  star_involutive z := by ext; simp

/--
@isnad1 id=eq.0h1v.s5.738ef1c2807e from=seed src=0 shape=d7ff289e vocab=b6e8c943
-/
@[simp] protected theorem star_neg (z : 𝕔𝔻) : star (-z) = -(star z) := rfl

/--
@isnad1 id=eq.0h1v.s3.bf5ce36fc24e from=seed src=0 shape=8fc7e33b vocab=39216943
-/
@[simp] protected theorem re_star (z : 𝕔𝔻) : (star z).re = z.re := rfl

/--
@isnad1 id=eq.0h1v.s3.caaa88319cdb from=seed src=0 shape=5a02da31 vocab=7f51caaa
-/
@[simp] protected theorem im_star (z : 𝕔𝔻) : (star z).im = -z.im := rfl

instance : StarMul 𝕔𝔻 where
  star_mul z w := coe_injective <| by simp [mul_comm]

end UnitClosedDisc

end Complex
