import Tengoku.OddcyclegoodmanLean.OddCycleBound.Kernel
import Tengoku.Seed.MeasureTheory.Function.L2Space
import Tengoku.Seed.MeasureTheory.Function.SimpleFuncDenseLp
import Tengoku.Seed.Analysis.InnerProductSpace.Symmetric
import Tengoku.Seed.Analysis.Normed.Operator.Extend

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped InnerProductSpace
open scoped ENNReal

noncomputable section

namespace OddCycleBound
namespace Spectral
namespace L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/--
@isnad1 id=memlp.1h3v.s6.e06e20619229 from=translated src=- shape=6ff9b21f vocab=f653c04f
-/
lemma good_memLp_two {f : Omega -> Real} (hf : Good f) :
    MemLp f 2 mu := by
  obtain ⟨C, _hC0, hC⟩ := hf.bdd
  exact MemLp.of_bound hf.meas.aestronglyMeasurable C
    (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hC x)

/--
@isnad1 id=good.1h2v.s4.0a04a916402d from=translated src=- shape=d73c887a vocab=67dcd420
-/
lemma good_abs {f : Omega -> Real} (hf : Good f) :
    Good (fun x => |f x|) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨continuous_abs.comp_stronglyMeasurable hf.meas, ⟨C, hC0, fun x => ?_⟩⟩
  simpa [abs_abs] using hC x

/--
@isnad1 id=good.1h2v.s4.35608b39d7f1 from=translated src=- shape=d73c887a vocab=2275fe4a
-/
lemma good_neg {f : Omega -> Real} (hf : Good f) :
    Good (fun x => - f x) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.neg, C, hC0, fun x => ?_⟩
  simpa using hC x

/--
@isnad1 id=good.2h3v.s5.73ffbd0948f2 from=translated src=- shape=e7bce992 vocab=a8ffae14
-/
lemma good_sub {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    Good (fun x => f x - g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨hf.meas.sub hg.meas, Cf + Cg, add_nonneg hCf0 hCg0, fun x => ?_⟩
  calc
    |f x - g x| <= |f x| + |g x| := abs_sub _ _
    _ <= Cf + Cg := add_le_add (hCf x) (hCg x)

def goodL2 {f : Omega -> Real} (hf : Good f) :
    Lp Real 2 mu :=
  (good_memLp_two hf).toLp f

/--
@isnad1 id=eventual.1h3v.s7.9e8239254d27 from=translated src=- shape=66d5664d vocab=d714e79d
-/
lemma goodL2_ae_eq {f : Omega -> Real} (hf : Good f) :
    (goodL2 (mu := mu) hf : Omega -> Real) =ᵐ[mu] f :=
  MemLp.coeFn_toLp (good_memLp_two hf)

/--
@isnad1 id=eq.2h4v.s8.de65fa4ee258 from=translated src=- shape=001151e9 vocab=25940c79
-/
lemma inner_goodL2_eq_integral_mul {f g : Omega -> Real}
    (hf : Good f) (hg : Good g) :
    inner Real (goodL2 (mu := mu) hf) (goodL2 (mu := mu) hg) =
      ∫ x, f x * g x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hfae := goodL2_ae_eq (mu := mu) hf
  have hgae := goodL2_ae_eq (mu := mu) hg
  refine integral_congr_ae ?_
  filter_upwards [hfae, hgae] with x hfx hgx
  rw [hfx, hgx]
  simp [RCLike.inner_apply, mul_comm]

/--
@isnad1 id=eq.1h3v.s8.9cb002eeb2d0 from=translated src=- shape=97bae290 vocab=34f94db9
-/
lemma norm_goodL2_sq_eq_integral_mul {f : Omega -> Real}
    (hf : Good f) :
    ‖goodL2 (mu := mu) hf‖ ^ 2 =
      ∫ x, f x * f x ∂mu := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_goodL2_eq_integral_mul hf hf

/--
@isnad1 id=eq.2h4v.s10.d62ecbb36292 from=translated src=- shape=38914f0e vocab=d46ad0ce
-/
lemma goodL2_sub {f g : Omega -> Real}
    (hf : Good f) (hg : Good g) :
    goodL2 (mu := mu) (good_sub hf hg) =
      goodL2 (mu := mu) hf - goodL2 (mu := mu) hg := by
  calc
    goodL2 (mu := mu) (good_sub hf hg)
        =
          ((good_memLp_two hf).sub (good_memLp_two hg)).toLp (f - g) := by
          exact MemLp.toLp_congr
            (good_memLp_two (good_sub hf hg))
            ((good_memLp_two hf).sub (good_memLp_two hg))
            (ae_of_all _ fun _ => rfl)
    _ = goodL2 (mu := mu) hf - goodL2 (mu := mu) hg := by
          exact MemLp.toLp_sub (good_memLp_two hf) (good_memLp_two hg)

/--
@isnad1 id=eq.1h3v.s8.72df8767705e from=translated src=- shape=f3be5e18 vocab=aeea98c5
-/
lemma goodL2_abs {f : Omega -> Real} (hf : Good f) :
    goodL2 (mu := mu) (good_abs hf) =
      |goodL2 (mu := mu) hf| := by
  rw [Lp.ext_iff]
  filter_upwards [goodL2_ae_eq (mu := mu) (good_abs hf),
    Lp.coeFn_abs (goodL2 (mu := mu) hf),
    goodL2_ae_eq (mu := mu) hf] with x hgood hLp hbase
  rw [hgood, hLp, hbase]

/--
@isnad1 id=eq.1h4v.s11.439762719218 from=translated src=- shape=ae940935 vocab=e5089b14
-/
lemma goodL2_smul (c : Real) {f : Omega -> Real} (hf : Good f) :
    goodL2 (mu := mu) (good_smul c hf) =
      c • goodL2 (mu := mu) hf := by
  calc
    goodL2 (mu := mu) (good_smul c hf)
        =
          ((good_memLp_two hf).const_smul c).toLp (c • f) := by
          exact MemLp.toLp_congr
            (good_memLp_two (good_smul c hf))
            ((good_memLp_two hf).const_smul c)
            (ae_of_all _ fun _ => rfl)
    _ = c • goodL2 (mu := mu) hf := by
          exact MemLp.toLp_const_smul c (good_memLp_two hf)

def oneL2 (mu : Measure Omega) [IsProbabilityMeasure mu] :
    Lp Real 2 mu :=
  (memLp_const (1 : Real)).toLp (fun _ : Omega => 1)

/--
@isnad1 id=eventual.0h2v.s7.7174c3a89284 from=translated src=- shape=5ce2f297 vocab=840ee49d
-/
lemma oneL2_ae_eq_one :
    (oneL2 (Omega := Omega) mu : Omega -> Real) =ᵐ[mu]
      fun _ : Omega => 1 :=
  MemLp.coeFn_toLp (memLp_const (1 : Real))

/--
@isnad1 id=eq.0h2v.s7.270cdc3bff07 from=translated src=- shape=6594fe98 vocab=2b1a4f6a
-/
lemma goodL2_one_eq_oneL2 :
    goodL2 (mu := mu) (good_one (Ω := Omega)) =
      oneL2 (Omega := Omega) mu := by
  exact MemLp.toLp_congr
    (good_memLp_two (good_one (Ω := Omega)))
    (memLp_const (1 : Real))
    (ae_of_all _ fun _ => rfl)

/--
@isnad1 id=memlp.1h3v.s6.3a56631ed2c0 from=translated src=- shape=26e24470 vocab=c4631707
-/
lemma degree_memLp_two (hW : IsGraphon W mu) :
    MemLp (degree W mu) 2 mu :=
  good_memLp_two (good_degree hW)

def degreeL2 (hW : IsGraphon W mu) : Lp Real 2 mu :=
  (degree_memLp_two hW).toLp (degree W mu)

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=le.1h5v.s5.f32822d0d810 from=translated src=- shape=c7c54887 vocab=3849e258
-/
lemma graphon_abs_le_one (hW : IsGraphon W mu) :
    forall x y, |W x y| <= 1 := by
  intro x y
  rw [abs_of_nonneg (hW.nonneg x y)]
  exact hW.le_one x y

/--
@isnad1 id=good.2h4v.s5.fe1418e3470e from=translated src=- shape=37ae2534 vocab=5c41a44d
-/
lemma good_kernelOp_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    Good (kernelOp K mu f) := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  refine ⟨?_, ⟨CK * Cf, mul_nonneg hCK0 hCf0, fun x => ?_⟩⟩
  · have hSM : StronglyMeasurable
        (fun p : Omega × Omega => K p.1 p.2 * f p.2) :=
      hK.meas.stronglyMeasurable.mul
        (hf.meas.comp_measurable measurable_snd)
    exact hSM.integral_prod_right'
  · have hint : Integrable (fun y => K x y * f y) mu := by
      have hmK : Measurable (fun y => K x y) :=
        hK.meas.comp measurable_prodMk_left
      refine (integrable_const (CK * Cf)).mono'
        (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      change |K x y * f y| <= CK * Cf
      rw [abs_mul]
      exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0
    calc
      |kernelOp K mu f x|
          <= ∫ y, |K x y * f y| ∂mu := abs_integral_le_integral_abs
      _ <= ∫ _y, CK * Cf ∂mu := by
          refine integral_mono hint.abs (integrable_const (CK * Cf)) ?_
          intro y
          change |K x y * f y| <= CK * Cf
          rw [abs_mul]
          exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0
      _ = CK * Cf := by simp

/--
@isnad1 id=memlp.2h4v.s6.4ad19cdc3b93 from=translated src=- shape=d5dff2f6 vocab=7d0fd0ee
-/
lemma kernelOpGoodK_memLp_two {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    MemLp (kernelOp K mu f) 2 mu :=
  good_memLp_two (good_kernelOp_goodK (mu := mu) hK hf)

def kernelOpL2OfGoodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    Lp Real 2 mu :=
  (kernelOpGoodK_memLp_two (mu := mu) hK hf).toLp (kernelOp K mu f)

/--
@isnad1 id=eventual.2h4v.s8.b3213910e54a from=translated src=- shape=4a51e8bc vocab=5553e13a
-/
lemma kernelOpL2OfGoodK_ae_eq {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    (kernelOpL2OfGoodK (mu := mu) hK hf : Omega -> Real) =ᵐ[mu]
      kernelOp K mu f :=
  MemLp.coeFn_toLp (kernelOpGoodK_memLp_two (mu := mu) hK hf)

/--
@isnad1 id=integrab.2h5v.s6.7cd0a38f5cbb from=translated src=- shape=101d485c vocab=9180146e
-/
lemma integrable_Kf {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    Integrable (fun y => K x y * f y) mu := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨Cf, _hCf0, hCf⟩ := hf.bdd
  have hmK : Measurable (fun y => K x y) :=
    hK.meas.comp measurable_prodMk_left
  refine (integrable_const (CK * Cf)).mono'
    (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  change |K x y * f y| <= CK * Cf
  rw [abs_mul]
  exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.1h5v.s5.9562198fd691 from=translated src=- shape=68a288b7 vocab=ca5b8956
-/
lemma kernelOpGoodK_congr_ae {K : Omega -> Omega -> Real}
    {f g : Omega -> Real} (hfg : f =ᵐ[mu] g) :
    kernelOp K mu f = kernelOp K mu g := by
  funext x
  simp only [kernelOp]
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.0h4v.s5.d3ffa2a2b94e from=translated src=- shape=2ddef6d1 vocab=7e00ff48
-/
lemma comp_rowBroadcast_eq_kernelOp {K : Omega -> Omega -> Real}
    (f : Omega -> Real) :
    comp mu K (fun z _y => f z) = fun x _y => kernelOp K mu f x := by
  rfl

/--
@isnad1 id=eq.3h5v.s6.cad5deed6035 from=translated src=- shape=fb6cf2ff vocab=87802c47
-/
lemma kernelOp_comp_eq_kernelOp_kernelOp {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {f : Omega -> Real} (hf : Good f) :
    kernelOp (comp mu K L) mu f =
      kernelOp K mu (kernelOp L mu f) := by
  have hassoc :=
    comp_assoc (μ := mu) hK hL (goodK_rowBroadcast (Ω := Omega) hf)
  have hleft :
      comp mu (comp mu K L) (fun z _y => f z) =
        fun x _y => kernelOp (comp mu K L) mu f x := by
    exact comp_rowBroadcast_eq_kernelOp (mu := mu) f
  have hright :
      comp mu L (fun z _y => f z) =
        fun x _y => kernelOp L mu f x := by
    exact comp_rowBroadcast_eq_kernelOp (mu := mu) f
  funext x
  have hx := congrFun (congrFun hassoc x) x
  rw [hleft] at hx
  rw [hright] at hx
  simpa [comp, kernelOp] using hx

noncomputable def kernelOpIter (mu : Measure Omega)
    (K : Omega -> Omega -> Real) : Nat -> (Omega -> Real) -> Omega -> Real
  | 0, f => f
  | n + 1, f => kernelOp K mu (kernelOpIter mu K n f)

/--
@isnad1 id=good.2h5v.s5.3cb02afbdf0f from=translated src=- shape=97a5987b vocab=f0fb1c66
-/
lemma good_kernelOpIter_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    forall n, Good (kernelOpIter mu K n f)
  | 0 => hf
  | n + 1 =>
      good_kernelOp_goodK (mu := mu) hK
        (good_kernelOpIter_goodK hK hf n)

/--
@isnad1 id=eq.2h5v.s6.329c131fec34 from=translated src=- shape=0772a13a vocab=2e89ddc5
-/
lemma kernelOp_compPow_eq_kernelOpIter_succ
    {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    forall n,
      kernelOp (compPow mu K n) mu f =
        kernelOpIter mu K (n + 1) f
  | 0 => rfl
  | n + 1 => by
      rw [compPow]
      calc
        kernelOp (comp mu K (compPow mu K n)) mu f
            =
              kernelOp K mu (kernelOp (compPow mu K n) mu f) := by
              exact kernelOp_comp_eq_kernelOp_kernelOp
                (mu := mu) hK (goodK_compPow (μ := mu) hK n) hf
        _ =
              kernelOp K mu (kernelOpIter mu K (n + 1) f) := by
              rw [kernelOp_compPow_eq_kernelOpIter_succ hK hf n]
        _ =
              kernelOpIter mu K (n + 2) f := rfl

/--
@isnad1 id=eq.2h5v.s8.a5729d067ee4 from=translated src=- shape=ffd3b186 vocab=986ef063
-/
lemma kernelOpL2OfGoodK_compPow_eq_goodL2_iter_succ
    {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) (n : Nat) :
    kernelOpL2OfGoodK (mu := mu) (goodK_compPow (μ := mu) hK n) hf =
      goodL2 (mu := mu)
        (good_kernelOpIter_goodK (mu := mu) hK hf (n + 1)) := by
  exact MemLp.toLp_congr
    (kernelOpGoodK_memLp_two (mu := mu)
      (goodK_compPow (μ := mu) hK n) hf)
    (good_memLp_two
      (good_kernelOpIter_goodK (mu := mu) hK hf (n + 1)))
    (ae_of_all _ fun x =>
      congrFun (kernelOp_compPow_eq_kernelOpIter_succ
        (mu := mu) hK hf n) x)

/--
@isnad1 id=goodk.2h3v.s5.f43e5c91aa1e from=translated src=- shape=71704a98 vocab=3b3df24a
-/
lemma goodK_sub {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L) :
    GoodK (fun x y => K x y - L x y) := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨CL, hCL0, hCL⟩ := hL.bdd
  refine ⟨hK.meas.sub hL.meas, ⟨CK + CL, add_nonneg hCK0 hCL0, ?_⟩⟩
  intro x y
  calc
    |K x y - L x y| <= |K x y| + |L x y| := abs_sub _ _
    _ <= CK + CL := add_le_add (hCK x y) (hCL x y)

/--
@isnad1 id=eq.4h5v.s8.972e0a4536f4 from=translated src=- shape=056d46f9 vocab=ee8b2dfa
-/
lemma kernelOpL2OfGoodK_congr {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g)
    (hfg : f =ᵐ[mu] g) :
    kernelOpL2OfGoodK (mu := mu) hK hf =
      kernelOpL2OfGoodK (mu := mu) hK hg := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x =>
    congrFun (kernelOpGoodK_congr_ae (mu := mu) (K := K) hfg) x

/--
@isnad1 id=eq.3h6v.s6.f15b75fe9352 from=translated src=- shape=cba100db vocab=4c1d78a6
-/
lemma kernelOpGoodK_add' {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f g : Omega -> Real}
    (hf : Good f) (hg : Good g) (x : Omega) :
    kernelOp K mu (f + g) x =
      kernelOp K mu f x + kernelOp K mu g x := by
  simp only [kernelOp, Pi.add_apply]
  rw [← integral_add (integrable_Kf (mu := mu) hK hf x)
    (integrable_Kf (mu := mu) hK hg x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.0h6v.s6.f04067ec736a from=translated src=- shape=17657479 vocab=2217cdcf
-/
lemma kernelOpGoodK_smul' {K : Omega -> Omega -> Real}
    (c : Real) (f : Omega -> Real) (x : Omega) :
    kernelOp K mu (c • f) x = c * kernelOp K mu f x := by
  simp only [kernelOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/--
@isnad1 id=eq.3h6v.s6.3bbe138cf5fc from=translated src=- shape=6b666ffe vocab=df2e1d91
-/
lemma kernelOpGoodK_sub_kernel' {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L) {f : Omega -> Real}
    (hf : Good f) (x : Omega) :
    kernelOp (fun x y => K x y - L x y) mu f x =
      kernelOp K mu f x - kernelOp L mu f x := by
  simp only [kernelOp]
  rw [← integral_sub
    (integrable_Kf (mu := mu) hK hf x)
    (integrable_Kf (mu := mu) hL hf x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/--
@isnad1 id=eq.3h5v.s10.e7cb6455c01a from=translated src=- shape=2f597a7e vocab=0dc7599e
-/
lemma kernelOpL2OfGoodK_add {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    kernelOpL2OfGoodK (mu := mu) hK (good_add hf hg) =
      kernelOpL2OfGoodK (mu := mu) hK hf +
        kernelOpL2OfGoodK (mu := mu) hK hg := by
  calc
    kernelOpL2OfGoodK (mu := mu) hK (good_add hf hg)
        =
          ((kernelOpGoodK_memLp_two (mu := mu) hK hf).add
            (kernelOpGoodK_memLp_two (mu := mu) hK hg)).toLp
            (kernelOp K mu f + kernelOp K mu g) := by
          exact MemLp.toLp_congr
            (kernelOpGoodK_memLp_two (mu := mu) hK (good_add hf hg))
            ((kernelOpGoodK_memLp_two (mu := mu) hK hf).add
              (kernelOpGoodK_memLp_two (mu := mu) hK hg))
            (ae_of_all _ fun x => kernelOpGoodK_add' (mu := mu) hK hf hg x)
    _ =
      kernelOpL2OfGoodK (mu := mu) hK hf +
        kernelOpL2OfGoodK (mu := mu) hK hg := by
          exact MemLp.toLp_add
            (kernelOpGoodK_memLp_two (mu := mu) hK hf)
            (kernelOpGoodK_memLp_two (mu := mu) hK hg)

/--
@isnad1 id=eq.2h5v.s11.fb90dc721717 from=translated src=- shape=407e385b vocab=474688ed
-/
lemma kernelOpL2OfGoodK_smul {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (c : Real) {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGoodK (mu := mu) hK (good_smul c hf) =
      c • kernelOpL2OfGoodK (mu := mu) hK hf := by
  calc
    kernelOpL2OfGoodK (mu := mu) hK (good_smul c hf)
        =
          ((kernelOpGoodK_memLp_two (mu := mu) hK hf).const_smul c).toLp
            (c • kernelOp K mu f) := by
          exact MemLp.toLp_congr
            (kernelOpGoodK_memLp_two (mu := mu) hK (good_smul c hf))
            ((kernelOpGoodK_memLp_two (mu := mu) hK hf).const_smul c)
            (ae_of_all _ fun x => kernelOpGoodK_smul' (mu := mu) c f x)
    _ = c • kernelOpL2OfGoodK (mu := mu) hK hf := by
          exact MemLp.toLp_const_smul c
            (kernelOpGoodK_memLp_two (mu := mu) hK hf)

/--
@isnad1 id=eq.3h5v.s10.68e90b434e88 from=translated src=- shape=69589768 vocab=8f2e8d11
-/
lemma kernelOpL2OfGoodK_sub_input {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    kernelOpL2OfGoodK (mu := mu) hK (good_sub hf hg) =
      kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hK hg := by
  calc
    kernelOpL2OfGoodK (mu := mu) hK (good_sub hf hg)
        =
          kernelOpL2OfGoodK (mu := mu) hK
            (good_add hf (good_neg hg)) := by
          exact kernelOpL2OfGoodK_congr (mu := mu) hK
            (good_sub hf hg)
            (good_add hf (good_neg hg))
            (ae_of_all _ fun x => by simp [sub_eq_add_neg])
    _ =
        kernelOpL2OfGoodK (mu := mu) hK hf +
          kernelOpL2OfGoodK (mu := mu) hK
            (good_neg hg) := by
          exact kernelOpL2OfGoodK_add (mu := mu) hK hf
            (good_neg hg)
    _ =
        kernelOpL2OfGoodK (mu := mu) hK hf -
          kernelOpL2OfGoodK (mu := mu) hK hg := by
          have hneg :
              kernelOpL2OfGoodK (mu := mu) hK (good_neg hg) =
                kernelOpL2OfGoodK (mu := mu) hK (good_smul (-1 : Real) hg) := by
            exact kernelOpL2OfGoodK_congr (mu := mu) hK
              (good_neg hg) (good_smul (-1 : Real) hg)
              (ae_of_all _ fun x => by simp)
          rw [hneg, kernelOpL2OfGoodK_smul (mu := mu) hK (-1) hg]
          simp [sub_eq_add_neg]

/--
@isnad1 id=eq.3h5v.s10.1c9df6f12e32 from=translated src=- shape=3e28b38e vocab=8a12f992
-/
lemma kernelOpL2OfGoodK_sub_kernel {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGoodK (mu := mu) (goodK_sub hK hL) hf =
      kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hL hf := by
  calc
    kernelOpL2OfGoodK (mu := mu) (goodK_sub hK hL) hf
        =
          ((kernelOpGoodK_memLp_two (mu := mu) hK hf).sub
            (kernelOpGoodK_memLp_two (mu := mu) hL hf)).toLp
            (kernelOp K mu f - kernelOp L mu f) := by
          exact MemLp.toLp_congr
            (kernelOpGoodK_memLp_two (mu := mu)
              (goodK_sub hK hL) hf)
            ((kernelOpGoodK_memLp_two (mu := mu) hK hf).sub
              (kernelOpGoodK_memLp_two (mu := mu) hL hf))
            (ae_of_all _ fun x =>
              kernelOpGoodK_sub_kernel' (mu := mu) hK hL hf x)
    _ =
      kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hL hf := by
          exact MemLp.toLp_sub
            (kernelOpGoodK_memLp_two (mu := mu) hK hf)
            (kernelOpGoodK_memLp_two (mu := mu) hL hf)

/--
@isnad1 id=le.4h6v.s6.df00ebc52d80 from=translated src=- shape=0767713b vocab=2d4fcc93
-/
lemma abs_kernelOpGoodK_le_const_integral_abs
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    |kernelOp K mu f x| <= C * ∫ y, |f y| ∂mu := by
  have hint : Integrable (fun y => K x y * f y) mu := by
    have hmK : Measurable (fun y => K x y) :=
      hK.meas.comp measurable_prodMk_left
    obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
    refine (integrable_const (C * Cf)).mono'
      (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    change |K x y * f y| <= C * Cf
    rw [abs_mul]
    exact mul_le_mul (hKC x y) (hCf y) (abs_nonneg _) hC0
  calc
    |kernelOp K mu f x|
        <= ∫ y, |K x y * f y| ∂mu := abs_integral_le_integral_abs
    _ <= ∫ y, C * |f y| ∂mu := by
        refine integral_mono hint.abs ((good_abs hf).integrable.const_mul C) ?_
        intro y
        change |K x y * f y| <= C * |f y|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hKC x y) (abs_nonneg _)
    _ = C * ∫ y, |f y| ∂mu := by
        rw [integral_const_mul]

/--
@isnad1 id=eq.2h4v.s8.6884ea90f4c0 from=translated src=- shape=f8c7b998 vocab=86556288
-/
lemma norm_kernelOpL2OfGoodK_sq_eq_integral_mul
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 =
      ∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu := by
  rw [← norm_goodL2_sq_eq_integral_mul
    (mu := mu) (good_kernelOp_goodK (mu := mu) hK hf)]
  rfl

/--
@isnad1 id=memlp.2h4v.s6.586e088c68a6 from=translated src=- shape=c5e5512b vocab=ac99453b
-/
lemma kernelOp_memLp_two (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    MemLp (kernelOp W mu f) 2 mu :=
  good_memLp_two (good_kernelOp hW hf)

def kernelOpL2OfGood (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    Lp Real 2 mu :=
  (kernelOp_memLp_two hW hf).toLp (kernelOp W mu f)

/--
@isnad1 id=eventual.2h4v.s8.6b2bb57c6b58 from=translated src=- shape=4ac86dcd vocab=612ed747
-/
lemma kernelOpL2OfGood_ae_eq (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    (kernelOpL2OfGood (mu := mu) hW hf : Omega -> Real) =ᵐ[mu]
      kernelOp W mu f :=
  MemLp.coeFn_toLp (kernelOp_memLp_two hW hf)

/--
@isnad1 id=eq.2h4v.s7.ea3fb2418fa2 from=translated src=- shape=8a903259 vocab=315fa6de
-/
lemma kernelOpL2OfGood_eq_kernelOpL2OfGoodK
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGood (mu := mu) hW hf =
      kernelOpL2OfGoodK (mu := mu) (goodK_of_isGraphon hW) hf := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun _ => rfl

/--
@isnad1 id=le.2h5v.s6.5f975c2af584 from=translated src=- shape=b82e5bff vocab=055ceb2b
-/
lemma abs_kernelOp_le_integral_abs (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    |kernelOp W mu f x| <= ∫ y, |f y| ∂mu := by
  calc
    |kernelOp W mu f x|
        <= ∫ y, |W x y * f y| ∂mu := by
          simpa [kernelOp] using
            (abs_integral_le_integral_abs
              (μ := mu) (f := fun y : Omega => W x y * f y))
    _ <= ∫ y, |f y| ∂mu := by
          refine integral_mono (integrable_Uf hW hf x).abs hf.integrable.abs ?_
          intro y
          change |W x y * f y| <= |f y|
          rw [abs_mul, abs_of_nonneg (hW.nonneg x y)]
          exact mul_le_of_le_one_left (abs_nonneg (f y)) (hW.le_one x y)

/--
@isnad1 id=le.2h5v.s6.4673075dfba9 from=translated src=- shape=2c5a12e4 vocab=841c0c4d
-/
lemma abs_kernelOp_le_kernelOp_abs (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    |kernelOp W mu f x| <=
      kernelOp W mu (fun y : Omega => |f y|) x := by
  calc
    |kernelOp W mu f x|
        <= ∫ y, |W x y * f y| ∂mu := by
          simpa [kernelOp] using
            (abs_integral_le_integral_abs
              (μ := mu) (f := fun y : Omega => W x y * f y))
    _ <= ∫ y, W x y * |f y| ∂mu := by
          refine integral_mono
            (integrable_Uf hW hf x).abs
            (integrable_Uf hW (good_abs hf) x) ?_
          intro y
          change |W x y * f y| <= W x y * |f y|
          rw [abs_mul, abs_of_nonneg (hW.nonneg x y)]

/--
@isnad1 id=eq.2h4v.s8.ecfcce52b4f6 from=translated src=- shape=87b5cf7c vocab=b322f94b
-/
lemma norm_kernelOpL2OfGood_sq_eq_integral_mul
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2 =
      ∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu := by
  rw [← norm_goodL2_sq_eq_integral_mul (mu := mu) (good_kernelOp hW hf)]
  rfl

/--
@isnad1 id=le.2h4v.s8.2e1eb2551c6e from=translated src=- shape=e660e293 vocab=51b9bd80
-/
lemma norm_kernelOpL2OfGood_sq_le_integral_abs_sq
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2 <=
      (∫ y, |f y| ∂mu) ^ 2 := by
  rw [norm_kernelOpL2OfGood_sq_eq_integral_mul]
  let A : Real := ∫ y, |f y| ∂mu
  have hA0 : 0 <= A := by
    dsimp [A]
    exact integral_nonneg fun y => abs_nonneg (f y)
  have hmono :
      (∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu) <=
        ∫ _x : Omega, A * A ∂mu := by
    refine integral_mono
      ((good_kernelOp hW hf).mul (good_kernelOp hW hf)).integrable
      (integrable_const (A * A)) ?_
    intro x
    have hx : |kernelOp W mu f x| <= A := by
      simpa [A] using abs_kernelOp_le_integral_abs hW hf x
    calc
      kernelOp W mu f x * kernelOp W mu f x
          = |kernelOp W mu f x| * |kernelOp W mu f x| := by
            rw [← pow_two, ← pow_two, sq_abs]
      _ <= A * A :=
            mul_le_mul hx hx (abs_nonneg _) hA0
  calc
    (∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu)
        <= ∫ _x : Omega, A * A ∂mu := hmono
    _ = A ^ 2 := by simp [A, pow_two]

/--
@isnad1 id=le.1h3v.s6.dbd87df4df5e from=translated src=- shape=3b6673fb vocab=62274403
-/
lemma integral_abs_sq_le_integral_mul_self
    {f : Omega -> Real} (hf : Good f) :
    (∫ x, |f x| ∂mu) ^ 2 <= ∫ x, f x * f x ∂mu := by
  let h1 : Good (fun _ : Omega => (1 : Real)) := good_one (Ω := Omega)
  let habs : Good (fun x : Omega => |f x|) := good_abs hf
  have hcs :=
    real_inner_mul_inner_self_le
      (goodL2 (mu := mu) h1) (goodL2 (mu := mu) habs)
  have honeabs :
      inner Real (goodL2 (mu := mu) h1) (goodL2 (mu := mu) habs) =
        ∫ x, |f x| ∂mu := by
    rw [inner_goodL2_eq_integral_mul h1 habs]
    simp
  have honeone :
      inner Real (goodL2 (mu := mu) h1) (goodL2 (mu := mu) h1) =
        1 := by
    rw [inner_goodL2_eq_integral_mul h1 h1]
    simp
  have habsabs :
      inner Real (goodL2 (mu := mu) habs) (goodL2 (mu := mu) habs) =
        ∫ x, f x * f x ∂mu := by
    rw [inner_goodL2_eq_integral_mul habs habs]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change |f x| * |f x| = f x * f x
    rw [← pow_two, ← pow_two, sq_abs]
  rw [honeabs, honeone, habsabs] at hcs
  simpa [pow_two] using hcs

/--
@isnad1 id=le.4h5v.s9.9e594d0e59f1 from=translated src=- shape=22f1939c vocab=a2877d8d
-/
lemma norm_kernelOpL2OfGoodK_sq_le_const_mul_norm_goodL2_sq
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
      C ^ 2 * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  rw [norm_kernelOpL2OfGoodK_sq_eq_integral_mul]
  let A : Real := ∫ y, |f y| ∂mu
  have hA0 : 0 <= A := by
    dsimp [A]
    exact integral_nonneg fun y => abs_nonneg (f y)
  have hCA0 : 0 <= C * A := mul_nonneg hC0 hA0
  have hmono :
      (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu) <=
        ∫ _x : Omega, (C * A) * (C * A) ∂mu := by
    refine integral_mono
      ((good_kernelOp_goodK (mu := mu) hK hf).mul
        (good_kernelOp_goodK (mu := mu) hK hf)).integrable
      (integrable_const ((C * A) * (C * A))) ?_
    intro x
    have hx : |kernelOp K mu f x| <= C * A := by
      simpa [A] using
        abs_kernelOpGoodK_le_const_integral_abs
          (mu := mu) hK hC0 hKC hf x
    calc
      kernelOp K mu f x * kernelOp K mu f x
          = |kernelOp K mu f x| * |kernelOp K mu f x| := by
            rw [← pow_two, ← pow_two, sq_abs]
      _ <= (C * A) * (C * A) :=
            mul_le_mul hx hx (abs_nonneg _) hCA0
  calc
    (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu)
        <= ∫ _x : Omega, (C * A) * (C * A) ∂mu := hmono
    _ = (C * A) ^ 2 := by simp [pow_two]
    _ = C ^ 2 * A ^ 2 := by ring
    _ <= C ^ 2 * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
          have hA := integral_abs_sq_le_integral_mul_self (mu := mu) hf
          rw [norm_goodL2_sq_eq_integral_mul (mu := mu) hf]
          exact mul_le_mul_of_nonneg_left hA (sq_nonneg C)

/--
@isnad1 id=le.4h5v.s8.6c3dc06773a2 from=translated src=- shape=a4bf23e1 vocab=128c91d6
-/
lemma norm_kernelOpL2OfGoodK_le_const_mul_norm_goodL2
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ <=
      C * ‖goodL2 (mu := mu) hf‖ := by
  have hsq :=
    norm_kernelOpL2OfGoodK_sq_le_const_mul_norm_goodL2_sq
      (mu := mu) hK hC0 hKC hf
  have hsq' :
      ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
        (C * ‖goodL2 (mu := mu) hf‖) ^ 2 := by
    simpa [mul_pow] using hsq
  have hrhs0 : 0 <= C * ‖goodL2 (mu := mu) hf‖ :=
    mul_nonneg hC0 (norm_nonneg _)
  exact le_of_sq_le_sq hsq' hrhs0

/--
@isnad1 id=le.5h6v.s11.887fc8846df6 from=translated src=- shape=5ce753e9 vocab=87fd2c92
-/
lemma norm_kernelOpL2OfGoodK_sub_le_const_mul_norm_goodL2_sub
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hK hg‖ <=
      C * ‖goodL2 (mu := mu) hf - goodL2 (mu := mu) hg‖ := by
  calc
    ‖kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hK hg‖
        =
          ‖kernelOpL2OfGoodK (mu := mu) hK
            (good_sub hf hg)‖ := by
          rw [kernelOpL2OfGoodK_sub_input (mu := mu) hK hf hg]
    _ <=
        C * ‖goodL2 (mu := mu) (good_sub hf hg)‖ :=
          norm_kernelOpL2OfGoodK_le_const_mul_norm_goodL2
            (mu := mu) hK hC0 hKC (good_sub hf hg)
    _ =
        C * ‖goodL2 (mu := mu) hf - goodL2 (mu := mu) hg‖ := by
          rw [goodL2_sub (mu := mu) hf hg]

noncomputable def kernelSqNorm (mu : Measure Omega)
    (K : Omega -> Omega -> Real) : Real :=
  ∫ x, ∫ y, K x y * K x y ∂mu ∂mu

/--
@isnad1 id=integrab.1h3v.s6.a2a8d07c7d79 from=translated src=- shape=510c0396 vocab=a7126426
-/
lemma integrable_uncurry_mul_self_of_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    Integrable
      (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2)
      (mu.prod mu) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  have hSM : StronglyMeasurable
      (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2) :=
    hK.meas.stronglyMeasurable.mul hK.meas.stronglyMeasurable
  refine (integrable_const (C * C)).mono'
    hSM.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC p.1 p.2) (hC p.1 p.2) (abs_nonneg _) hC0

/--
@isnad1 id=eq.1h3v.s6.c2aec83e6ca0 from=translated src=- shape=5534cdcd vocab=8f5cbd0e
-/
lemma kernelSqNorm_eq_integral_prod_of_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    kernelSqNorm mu K =
      ∫ p : Omega × Omega, K p.1 p.2 * K p.1 p.2 ∂(mu.prod mu) := by
  rw [kernelSqNorm]
  exact (integral_prod
    (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2)
    (integrable_uncurry_mul_self_of_goodK (mu := mu) hK)).symm

/--
@isnad1 id=memlp.1h3v.s6.944e0afc05b8 from=translated src=- shape=fe444346 vocab=5553c9f6
-/
lemma goodK_memLp_prod_two {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    MemLp (Function.uncurry K) 2 (mu.prod mu) := by
  obtain ⟨C, _hC0, hC⟩ := hK.bdd
  exact MemLp.of_bound (μ := mu.prod mu) hK.meas.aestronglyMeasurable C
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hC p.1 p.2)

/--
@isnad1 id=eq.1h3v.s6.3e2d48e99eb4 from=translated src=- shape=956b8ba2 vocab=59fe92b4
-/
lemma lpNorm_two_eq_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α -> Real} (hf : AEStronglyMeasurable f ν) :
    lpNorm f 2 ν = Real.sqrt (∫ x, f x * f x ∂ν) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ENNReal)) (by norm_num) (by simp) hf]
  rw [Real.sqrt_eq_rpow]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp [Real.norm_eq_abs, abs_mul_abs_self, sq]
  · norm_num

/--
@isnad1 id=lt.3h4v.s6.d58991885668 from=translated src=- shape=188790ac vocab=fe2e9c14
-/
lemma lpNorm_two_lt_of_integral_sq_lt
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α -> Real} (hf : AEStronglyMeasurable f ν)
    {ε : Real} (hε : 0 < ε)
    (hsmall : (∫ x, f x * f x ∂ν) < ε ^ 2) :
    lpNorm f 2 ν < ε := by
  rw [lpNorm_two_eq_sqrt_integral_sq hf]
  exact (Real.sqrt_lt
    (integral_nonneg fun x => mul_self_nonneg (f x))
    hε.le).2 hsmall

/--
@isnad1 id=eq.1h3v.s6.af583808da93 from=translated src=- shape=80e02d48 vocab=62f4773c
-/
lemma lpNorm_uncurry_two_eq_sqrt_kernelSqNorm_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K) :
    lpNorm (Function.uncurry K) 2 (mu.prod mu) =
      Real.sqrt (kernelSqNorm mu K) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ENNReal)) (by norm_num) (by simp)
    (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable]
  rw [kernelSqNorm_eq_integral_prod_of_goodK (mu := mu) hK,
    Real.sqrt_eq_rpow]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun p => by
      simp [Function.uncurry, Real.norm_eq_abs, abs_mul_abs_self, sq]
  · norm_num

/--
@isnad1 id=eq.2h4v.s7.aa23931cbf6a from=translated src=- shape=03dbb5f6 vocab=485f18ff
-/
lemma lpNorm_uncurry_sub_two_eq_sqrt_kernelSqNorm_sub_of_goodK
    {K L : Omega -> Omega -> Real} (hK : GoodK K) (hL : GoodK L) :
    lpNorm (Function.uncurry K - Function.uncurry L) 2 (mu.prod mu) =
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - L x y)) := by
  calc
    lpNorm (Function.uncurry K - Function.uncurry L) 2 (mu.prod mu)
        =
      lpNorm (Function.uncurry (fun x y => K x y - L x y)) 2 (mu.prod mu) := by
        rfl
    _ =
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - L x y)) :=
        lpNorm_uncurry_two_eq_sqrt_kernelSqNorm_of_goodK
          (mu := mu) (goodK_sub hK hL)

/--
@isnad1 id=ex.2h4v.s8.b5851c4d8faa from=translated src=- shape=00f77e15 vocab=68c1a777
-/
lemma exists_simpleFunc_eLpNorm_uncurry_sub_lt_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ S : SimpleFunc (Omega × Omega) Real,
      eLpNorm (Function.uncurry K - ⇑S) 2 (mu.prod mu) < ε ∧
        MemLp S 2 (mu.prod mu) := by
  have htop := ENNReal.ofNat_ne_top (n := 2)
  exact (goodK_memLp_prod_two (mu := mu) hK).exists_simpleFunc_eLpNorm_sub_lt
    htop hε

/--
@isnad1 id=ex.2h4v.s8.ed5a3c400eb5 from=translated src=- shape=66326902 vocab=6120a1b6
-/
lemma exists_simpleFunc_lpNorm_uncurry_sub_lt_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {δ : Real} (hδ : 0 < δ) :
    ∃ S : SimpleFunc (Omega × Omega) Real,
      lpNorm (Function.uncurry K - ⇑S) 2 (mu.prod mu) < δ ∧
        MemLp S 2 (mu.prod mu) := by
  rcases exists_simpleFunc_eLpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK (ε := ENNReal.ofReal δ)
      (ENNReal.ofReal_ne_zero_iff.mpr hδ) with ⟨S, hSlt, hSmem⟩
  refine ⟨S, ?_, hSmem⟩
  have hSM :
      AEStronglyMeasurable (Function.uncurry K - ⇑S) (mu.prod mu) :=
    (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable.sub
      hSmem.aestronglyMeasurable
  rw [← MeasureTheory.toReal_eLpNorm hSM]
  exact ENNReal.toReal_lt_of_lt_ofReal hSlt

/--
@isnad1 id=ex.2h4v.s7.8c1514f922aa from=translated src=- shape=d548ef3f vocab=b3b8e44b
-/
lemma exists_finiteRank_kernel_lpNorm_uncurry_sub_lt_of_goodK
    {K0 : Omega -> Omega -> Real} (hK0 : GoodK K0)
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Omega -> Omega -> Real, ∃ B : Real,
    ∃ a b : J -> Omega -> Real,
      GoodK K ∧
      0 ≤ B ∧
      (∀ x y, |K x y| ≤ B) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      lpNorm (Function.uncurry K - Function.uncurry K0) 2 (mu.prod mu) < ε := by
  classical
  have hhalf : 0 < ε / 2 := by linarith
  rcases exists_simpleFunc_lpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK0 hhalf with
    ⟨S, hSlt, hSmem⟩
  let A : Real :=
    ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
      ((SimpleFunc.range S).card : Real)
  let η : Real := (ε / 2) ^ 2 / (A + 1)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hA1 : 0 < A + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (sq_pos_of_pos hhalf) hA1
  rcases exists_simpleFunc_rectangular_finiteRank_data_integral_sq_bound
      (Ω := Omega) mu S hη with
    ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, -, -, hsep, hInt⟩
  have hCoeff_lt :
      ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card * η) < (ε / 2) ^ 2 := by
    have hmain : A * ((ε / 2) ^ 2 / (A + 1)) < (ε / 2) ^ 2 := by
      rw [show A * ((ε / 2) ^ 2 / (A + 1)) =
          A * (ε / 2) ^ 2 / (A + 1) by ring]
      rw [div_lt_iff₀ hA1]
      nlinarith [sq_pos_of_pos hhalf]
    dsimp [η]
    rw [show ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card *
            ((ε / 2) ^ 2 / (A + 1))) =
        A * ((ε / 2) ^ 2 / (A + 1)) by
          dsimp [A]
          ring]
    exact hmain
  have hInt_lt :
      (∫ p : Omega × Omega, (S p - K p.1 p.2) ^ 2 ∂(mu.prod mu))
        < (ε / 2) ^ 2 :=
    lt_of_le_of_lt hInt hCoeff_lt
  have hRectLp :
      lpNorm (fun p : Omega × Omega => S p - K p.1 p.2) 2 (mu.prod mu) < ε / 2 := by
    have hSM :
        AEStronglyMeasurable
          (fun p : Omega × Omega => S p - K p.1 p.2) (mu.prod mu) :=
      hSmem.aestronglyMeasurable.sub
        (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable
    refine lpNorm_two_lt_of_integral_sq_lt (ν := mu.prod mu) hSM hhalf ?_
    simpa [pow_two] using hInt_lt
  have hKmem : MemLp (Function.uncurry K) 2 (mu.prod mu) :=
    goodK_memLp_prod_two (mu := mu) hK
  have htri :
      lpNorm (Function.uncurry K - Function.uncurry K0) 2 (mu.prod mu) ≤
        lpNorm (Function.uncurry K - (S : Omega × Omega -> Real)) 2 (mu.prod mu) +
          lpNorm ((S : Omega × Omega -> Real) - Function.uncurry K0) 2 (mu.prod mu) := by
    exact lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
      (μ := mu.prod mu) (p := (2 : ENNReal))
      (f := Function.uncurry K) (g := (S : Omega × Omega -> Real))
      (h := Function.uncurry K0)
      hKmem hSmem (by norm_num)
  have hKS :
      lpNorm (Function.uncurry K - (S : Omega × Omega -> Real)) 2 (mu.prod mu) <
        ε / 2 := by
    rw [MeasureTheory.lpNorm_sub_comm]
    change lpNorm (fun p : Omega × Omega => S p - K p.1 p.2) 2
      (mu.prod mu) < ε / 2
    exact hRectLp
  have hSW :
      lpNorm ((S : Omega × Omega -> Real) - Function.uncurry K0) 2 (mu.prod mu) <
        ε / 2 := by
    simpa [MeasureTheory.lpNorm_sub_comm] using hSlt
  refine ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, hsep, ?_⟩
  calc
    lpNorm (Function.uncurry K - Function.uncurry K0) 2 (mu.prod mu)
        ≤ lpNorm (Function.uncurry K - (S : Omega × Omega -> Real)) 2 (mu.prod mu) +
          lpNorm ((S : Omega × Omega -> Real) - Function.uncurry K0) 2
            (mu.prod mu) := htri
    _ < ε := by linarith

/--
@isnad1 id=ex.2h4v.s7.1006f63d3e9c from=translated src=- shape=c4e4c9f2 vocab=5fa6b4ab
-/
lemma exists_finiteRank_kernel_sqrt_kernelSqNorm_sub_lt_of_goodK
    {K0 : Omega -> Omega -> Real} (hK0 : GoodK K0)
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Omega -> Omega -> Real, ∃ B : Real,
    ∃ a b : J -> Omega -> Real,
      GoodK K ∧
      0 ≤ B ∧
      (∀ x y, |K x y| ≤ B) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - K0 x y)) < ε := by
  rcases exists_finiteRank_kernel_lpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK0 hε with
    ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, hsep, hlt⟩
  refine ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, hsep, ?_⟩
  rw [← lpNorm_uncurry_sub_two_eq_sqrt_kernelSqNorm_sub_of_goodK
    (mu := mu) hK hK0]
  exact hlt

/--
@isnad1 id=good.1h3v.s4.d73c6dc9fc1b from=translated src=- shape=489868df vocab=9d55f5b6
-/
lemma goodK_row {K : Omega -> Omega -> Real}
    (hK : GoodK K) (x : Omega) :
    Good (fun y => K x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  exact ⟨(hK.meas.comp measurable_prodMk_left).stronglyMeasurable,
    C, hC0, fun y => hC x y⟩

/--
@isnad1 id=good.1h3v.s5.dbcd461cac6a from=translated src=- shape=b5e74e3b vocab=e204b4fc
-/
lemma good_kernelSqRow {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    Good (fun x => ∫ y, K x y * K x y ∂mu) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  refine ⟨?_, C * C, mul_nonneg hC0 hC0, ?_⟩
  · have hSM :
        StronglyMeasurable
          (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2) :=
      hK.meas.stronglyMeasurable.mul hK.meas.stronglyMeasurable
    exact hSM.integral_prod_right'
  · intro x
    have hrow : Good (fun y => K x y) := goodK_row hK x
    calc
      |∫ y, K x y * K x y ∂mu|
          <= ∫ y, |K x y * K x y| ∂mu := abs_integral_le_integral_abs
      _ <= ∫ _y : Omega, C * C ∂mu := by
          refine integral_mono (hrow.mul hrow).integrable.abs
            (integrable_const (C * C)) ?_
          intro y
          change |K x y * K x y| <= C * C
          rw [abs_mul]
          exact mul_le_mul (hC x y) (hC x y) (abs_nonneg _) hC0
      _ = C * C := by simp

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=le.0h3v.s4.79cc5e2b1cd3 from=translated src=- shape=261090db vocab=0b46372a
-/
lemma kernelSqNorm_nonneg {K : Omega -> Omega -> Real} :
    0 <= kernelSqNorm mu K := by
  unfold kernelSqNorm
  exact integral_nonneg fun x =>
    integral_nonneg fun y => mul_self_nonneg (K x y)

/--
@isnad1 id=le.2h5v.s7.8ed38e8bf2f1 from=translated src=- shape=2300c34f vocab=60eb55cb
-/
lemma kernelOpGoodK_apply_mul_self_le_rowSq_mul_integral
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    kernelOp K mu f x * kernelOp K mu f x <=
      (∫ y, K x y * K x y ∂mu) * (∫ y, f y * f y ∂mu) := by
  let hrow : Good (fun y => K x y) := goodK_row hK x
  have hcs :=
    real_inner_mul_inner_self_le
      (goodL2 (mu := mu) hrow) (goodL2 (mu := mu) hf)
  have hrowf :
      inner Real (goodL2 (mu := mu) hrow) (goodL2 (mu := mu) hf) =
        ∫ y, K x y * f y ∂mu := by
    exact inner_goodL2_eq_integral_mul hrow hf
  have hrowrow :
      inner Real (goodL2 (mu := mu) hrow) (goodL2 (mu := mu) hrow) =
        ∫ y, K x y * K x y ∂mu := by
    exact inner_goodL2_eq_integral_mul hrow hrow
  have hff :
      inner Real (goodL2 (mu := mu) hf) (goodL2 (mu := mu) hf) =
        ∫ y, f y * f y ∂mu := by
    exact inner_goodL2_eq_integral_mul hf hf
  rw [hrowf, hrowrow, hff] at hcs
  simpa [kernelOp] using hcs

/--
@isnad1 id=le.2h4v.s8.56bb706ee9d9 from=translated src=- shape=979f0f1b vocab=6a9c5680
-/
lemma norm_kernelOpL2OfGoodK_sq_le_kernelSqNorm_mul_norm_goodL2_sq
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
      kernelSqNorm mu K * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  rw [norm_kernelOpL2OfGoodK_sq_eq_integral_mul]
  let B : Real := ∫ y, f y * f y ∂mu
  have hBnorm : B = ‖goodL2 (mu := mu) hf‖ ^ 2 := by
    rw [norm_goodL2_sq_eq_integral_mul (mu := mu) hf]
  have hmono :
      (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu) <=
        ∫ x, (∫ y, K x y * K x y ∂mu) * B ∂mu := by
    refine integral_mono
      ((good_kernelOp_goodK (mu := mu) hK hf).mul
        (good_kernelOp_goodK (mu := mu) hK hf)).integrable
      ((good_kernelSqRow (mu := mu) hK).integrable.mul_const B) ?_
    intro x
    simpa [B] using
      kernelOpGoodK_apply_mul_self_le_rowSq_mul_integral
        (mu := mu) hK hf x
  calc
    (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu)
        <= ∫ x, (∫ y, K x y * K x y ∂mu) * B ∂mu := hmono
    _ = (∫ x, ∫ y, K x y * K x y ∂mu ∂mu) * B := by
          rw [integral_mul_const]
    _ = kernelSqNorm mu K * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
          simp [kernelSqNorm, hBnorm]

/--
@isnad1 id=eq.1h5v.s9.97ad264c45ca from=translated src=- shape=c9e39e6e vocab=af7f94a4
-/
lemma inner_goodK_row_l2_eq_kernelOp
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    (f : Lp Real 2 mu) (x : Omega) :
    inner Real (goodL2 (mu := mu) (goodK_row hK x)) f =
      kernelOp K mu (fun y : Omega => f y) x := by
  rw [MeasureTheory.L2.inner_def]
  have hrowae := goodL2_ae_eq (mu := mu) (goodK_row hK x)
  refine integral_congr_ae ?_
  filter_upwards [hrowae] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

/--
@isnad1 id=integrab.1h3v.s8.aedab7f5e259 from=translated src=- shape=2140798a vocab=4fd40b95
-/
lemma integrable_goodK_row_inner_self
    {K : Omega -> Omega -> Real} (hK : GoodK K) :
    Integrable (fun x : Omega =>
      inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (goodK_row hK x))) mu := by
  refine (good_kernelSqRow (mu := mu) hK).integrable.congr ?_
  exact ae_of_all _ fun x => by
    change (∫ y, K x y * K x y ∂mu) =
      inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (goodK_row hK x))
    rw [inner_goodL2_eq_integral_mul (goodK_row hK x) (goodK_row hK x)]

/--
@isnad1 id=eq.1h3v.s8.d2fe0c2ea5f5 from=translated src=- shape=5e93da47 vocab=66f1d307
-/
lemma integral_goodK_row_inner_self_eq_kernelSqNorm
    {K : Omega -> Omega -> Real} (hK : GoodK K) :
    (∫ x, inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (goodK_row hK x)) ∂mu) =
      kernelSqNorm mu K := by
  unfold kernelSqNorm
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change inner Real (goodL2 (mu := mu) (goodK_row hK x))
      (goodL2 (mu := mu) (goodK_row hK x)) =
    ∫ y, K x y * K x y ∂mu
  rw [inner_goodL2_eq_integral_mul (goodK_row hK x) (goodK_row hK x)]

/--
@isnad1 id=le.2h4v.s8.63621164cf3a from=translated src=- shape=533de1b1 vocab=b0deb2c9
-/
lemma norm_kernelOpL2OfGoodK_le_sqrt_kernelSqNorm_mul_norm_goodL2
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ <=
      Real.sqrt (kernelSqNorm mu K) * ‖goodL2 (mu := mu) hf‖ := by
  have hsq :=
    norm_kernelOpL2OfGoodK_sq_le_kernelSqNorm_mul_norm_goodL2_sq
      (mu := mu) hK hf
  have hsq' :
      ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
        (Real.sqrt (kernelSqNorm mu K) *
          ‖goodL2 (mu := mu) hf‖) ^ 2 := by
    simpa [mul_pow, Real.sq_sqrt (kernelSqNorm_nonneg (mu := mu) (K := K))]
      using hsq
  exact le_of_sq_le_sq hsq'
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/--
@isnad1 id=le.2h4v.s8.2002f5f65ced from=translated src=- shape=c543a698 vocab=3bc4aa99
-/
lemma norm_kernelOpL2OfGood_sq_le_norm_goodL2_sq
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2 <=
      ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  calc
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2
        <= (∫ y, |f y| ∂mu) ^ 2 :=
          norm_kernelOpL2OfGood_sq_le_integral_abs_sq hW hf
    _ <= ∫ y, f y * f y ∂mu :=
          integral_abs_sq_le_integral_mul_self (mu := mu) hf
    _ = ‖goodL2 (mu := mu) hf‖ ^ 2 := by
          rw [norm_goodL2_sq_eq_integral_mul]

/--
@isnad1 id=le.2h4v.s8.e822fe709817 from=translated src=- shape=4fa0857f vocab=12402931
-/
lemma norm_kernelOpL2OfGood_le_norm_goodL2
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ <=
      ‖goodL2 (mu := mu) hf‖ := by
  exact le_of_sq_le_sq
    (norm_kernelOpL2OfGood_sq_le_norm_goodL2_sq hW hf)
    (norm_nonneg _)

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.1h5v.s5.9562198fd691 from=translated src=- shape=68a288b7 vocab=ca5b8956
-/
lemma kernelOp_congr_ae {f g : Omega -> Real}
    (hfg : f =ᵐ[mu] g) :
    kernelOp W mu f = kernelOp W mu g := by
  funext x
  simp only [kernelOp]
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

/--
@isnad1 id=eq.4h5v.s8.bdc32020e380 from=translated src=- shape=c222a495 vocab=31e9a247
-/
lemma kernelOpL2OfGood_congr (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g)
    (hfg : f =ᵐ[mu] g) :
    kernelOpL2OfGood (mu := mu) hW hf =
      kernelOpL2OfGood (mu := mu) hW hg := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (kernelOp_congr_ae (mu := mu) (W := W) hfg) x

/--
@isnad1 id=eq.3h5v.s10.30c99224cb75 from=translated src=- shape=3b315d94 vocab=b9d7523a
-/
lemma kernelOpL2OfGood_add (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    kernelOpL2OfGood (mu := mu) hW (good_add hf hg) =
      kernelOpL2OfGood (mu := mu) hW hf +
        kernelOpL2OfGood (mu := mu) hW hg := by
  calc
    kernelOpL2OfGood (mu := mu) hW (good_add hf hg)
        =
          ((kernelOp_memLp_two hW hf).add (kernelOp_memLp_two hW hg)).toLp
            (kernelOp W mu f + kernelOp W mu g) := by
          exact MemLp.toLp_congr
            (kernelOp_memLp_two hW (good_add hf hg))
            ((kernelOp_memLp_two hW hf).add (kernelOp_memLp_two hW hg))
            (ae_of_all _ fun x => kernelOp_add' hW hf hg x)
    _ =
      kernelOpL2OfGood (mu := mu) hW hf +
        kernelOpL2OfGood (mu := mu) hW hg := by
          exact MemLp.toLp_add
            (kernelOp_memLp_two hW hf) (kernelOp_memLp_two hW hg)

/--
@isnad1 id=eq.2h5v.s11.c22105628be5 from=translated src=- shape=d0930511 vocab=17939292
-/
lemma kernelOpL2OfGood_smul (hW : IsGraphon W mu)
    (c : Real) {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGood (mu := mu) hW (good_smul c hf) =
      c • kernelOpL2OfGood (mu := mu) hW hf := by
  calc
    kernelOpL2OfGood (mu := mu) hW (good_smul c hf)
        =
          ((kernelOp_memLp_two hW hf).const_smul c).toLp
            (c • kernelOp W mu f) := by
          exact MemLp.toLp_congr
            (kernelOp_memLp_two hW (good_smul c hf))
            ((kernelOp_memLp_two hW hf).const_smul c)
            (ae_of_all _ fun x => kernelOp_smul' (U := W) (μ := mu) c f x)
    _ = c • kernelOpL2OfGood (mu := mu) hW hf := by
          exact MemLp.toLp_const_smul c (kernelOp_memLp_two hW hf)

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=good.0h3v.s10.1c19d51c34e5 from=translated src=- shape=7011777f vocab=f84c97e9
-/
lemma simpleFunc_good (s : Lp.simpleFunc Real 2 mu) :
    Good (Lp.simpleFunc.toSimpleFunc s) := by
  obtain ⟨C, hC⟩ :=
    SimpleFunc.exists_forall_norm_le (Lp.simpleFunc.toSimpleFunc s)
  refine ⟨Lp.simpleFunc.stronglyMeasurable s,
    ⟨max C 0, le_max_right _ _, fun x => ?_⟩⟩
  have hx : |Lp.simpleFunc.toSimpleFunc s x| <= C := by
    simpa [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/--
@isnad1 id=eq.0h3v.s11.671f89dc326e from=translated src=- shape=f10025a5 vocab=65f9911c
-/
lemma goodL2_simpleFunc_eq_coe (s : Lp.simpleFunc Real 2 mu) :
    goodL2 (mu := mu) (simpleFunc_good (mu := mu) s) =
      (s : Lp Real 2 mu) := by
  calc
    goodL2 (mu := mu) (simpleFunc_good (mu := mu) s)
        =
          (Lp.simpleFunc.memLp s).toLp (Lp.simpleFunc.toSimpleFunc s) := by
          exact MemLp.toLp_congr
            (good_memLp_two (simpleFunc_good (mu := mu) s))
            (Lp.simpleFunc.memLp s)
            (ae_of_all _ fun _ => rfl)
    _ = (s : Lp Real 2 mu) := by
          have h :=
            congrArg (fun t : Lp.simpleFunc Real 2 mu => (t : Lp Real 2 mu))
              (Lp.simpleFunc.toLp_toSimpleFunc s)
          simpa using h

/--
@isnad1 id=denseran.0h2v.s9.d79306eccbfb from=translated src=- shape=0396d10b vocab=1f3143db
-/
lemma denseRange_goodL2 :
    DenseRange
      (fun f : {f : Omega -> Real // Good f} =>
        goodL2 (mu := mu) f.property) := by
  have hsimple :
      DenseRange
        (fun s : Lp.simpleFunc Real 2 mu => (s : Lp Real 2 mu)) :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  intro x
  refine closure_mono ?_ (hsimple x)
  intro y hy
  rcases hy with ⟨s, rfl⟩
  refine ⟨⟨Lp.simpleFunc.toSimpleFunc s, simpleFunc_good (mu := mu) s⟩, ?_⟩
  change goodL2 (mu := mu) (simpleFunc_good (mu := mu) s) =
    (s : Lp Real 2 mu)
  exact goodL2_simpleFunc_eq_coe (mu := mu) s

def kernelOpSimple (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    Lp Real 2 mu :=
  kernelOpL2OfGood (mu := mu) hW (simpleFunc_good (mu := mu) s)

local instance simpleFuncSMul :
    SMul Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.smul

local instance simpleFuncModule :
    Module Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.module

local instance simpleFuncNormedSpace :
    NormedSpace Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.normedSpace

def kernelOpGoodKSimple {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (s : Lp.simpleFunc Real 2 mu) :
    Lp Real 2 mu :=
  kernelOpL2OfGoodK (mu := mu) hK (simpleFunc_good (mu := mu) s)

/--
@isnad1 id=eq.1h4v.s10.bd8ddfb066b1 from=translated src=- shape=a9099b30 vocab=615659eb
-/
lemma kernelOpSimple_eq_kernelOpGoodKSimple
    (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpSimple (mu := mu) hW s =
      kernelOpGoodKSimple (mu := mu) (goodK_of_isGraphon hW) s := by
  simpa [kernelOpSimple, kernelOpGoodKSimple] using
    kernelOpL2OfGood_eq_kernelOpL2OfGoodK
      (mu := mu) hW (simpleFunc_good (mu := mu) s)

/--
@isnad1 id=eq.1h5v.s13.ef60e38e247b from=translated src=- shape=5b06ce84 vocab=45a6e5f9
-/
lemma kernelOpGoodKSimple_add {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (s t : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKSimple (mu := mu) hK (s + t) =
      kernelOpGoodKSimple (mu := mu) hK s +
        kernelOpGoodKSimple (mu := mu) hK t := by
  calc
    kernelOpGoodKSimple (mu := mu) hK (s + t)
        =
          kernelOpL2OfGoodK (mu := mu) hK
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t)) := by
          exact kernelOpL2OfGoodK_congr (mu := mu) hK
            (simpleFunc_good (mu := mu) (s + t))
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t))
            (Lp.simpleFunc.add_toSimpleFunc s t)
    _ =
      kernelOpGoodKSimple (mu := mu) hK s +
        kernelOpGoodKSimple (mu := mu) hK t := by
          exact kernelOpL2OfGoodK_add (mu := mu) hK
            (simpleFunc_good (mu := mu) s)
            (simpleFunc_good (mu := mu) t)

/--
@isnad1 id=eq.1h5v.s13.c49cabdae7ec from=translated src=- shape=2fe5e63d vocab=85f097c2
-/
lemma kernelOpGoodKSimple_smul {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (c : Real) (s : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKSimple (mu := mu) hK (c • s) =
      c • kernelOpGoodKSimple (mu := mu) hK s := by
  calc
    kernelOpGoodKSimple (mu := mu) hK (c • s)
        =
          kernelOpL2OfGoodK (mu := mu) hK
            (good_smul c (simpleFunc_good (mu := mu) s)) := by
          exact kernelOpL2OfGoodK_congr (mu := mu) hK
            (simpleFunc_good (mu := mu) (c • s))
            (good_smul c (simpleFunc_good (mu := mu) s))
            (Lp.simpleFunc.smul_toSimpleFunc c s)
    _ = c • kernelOpGoodKSimple (mu := mu) hK s := by
          exact kernelOpL2OfGoodK_smul (mu := mu) hK c
            (simpleFunc_good (mu := mu) s)

/--
@isnad1 id=eq.2h5v.s11.b1afa62fa168 from=translated src=- shape=d35fe167 vocab=d13477a0
-/
lemma kernelOpGoodKSimple_sub_kernel {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKSimple (mu := mu) (goodK_sub hK hL) s =
      kernelOpGoodKSimple (mu := mu) hK s -
        kernelOpGoodKSimple (mu := mu) hL s := by
  simpa [kernelOpGoodKSimple] using
    kernelOpL2OfGoodK_sub_kernel (mu := mu) hK hL
      (simpleFunc_good (mu := mu) s)

/--
@isnad1 id=le.3h5v.s11.3e9ba4b2bb5a from=translated src=- shape=c3ff5eb6 vocab=054a9260
-/
lemma norm_kernelOpGoodKSimple_le {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    (s : Lp.simpleFunc Real 2 mu) :
    ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
      C * ‖(s : Lp Real 2 mu)‖ := by
  simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
    norm_kernelOpL2OfGoodK_le_const_mul_norm_goodL2
      (mu := mu) hK hC0 hKC (simpleFunc_good (mu := mu) s)

/--
@isnad1 id=le.1h4v.s11.cb4756092539 from=translated src=- shape=de712ce9 vocab=4faa87c9
-/
lemma norm_kernelOpGoodKSimple_le_sqrt_kernelSqNorm
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    (s : Lp.simpleFunc Real 2 mu) :
    ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
      Real.sqrt (kernelSqNorm mu K) * ‖(s : Lp Real 2 mu)‖ := by
  simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
    norm_kernelOpL2OfGoodK_le_sqrt_kernelSqNorm_mul_norm_goodL2
      (mu := mu) hK (simpleFunc_good (mu := mu) s)

def kernelOpGoodKSimpleLinearMap {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    Lp.simpleFunc Real 2 mu →ₗ[Real] Lp Real 2 mu where
  toFun := kernelOpGoodKSimple (mu := mu) hK
  map_add' := kernelOpGoodKSimple_add (mu := mu) hK
  map_smul' := kernelOpGoodKSimple_smul (mu := mu) hK

def kernelOpGoodKSimpleCLM {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    Lp.simpleFunc Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpGoodKSimpleLinearMap (mu := mu) hK).mkContinuous C
    (fun s => by
      change ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
        C * ‖(s : Lp Real 2 mu)‖
      exact norm_kernelOpGoodKSimple_le (mu := mu) hK hC0 hKC s)

/--
@isnad1 id=le.3h4v.s13.7fe3e2df399c from=translated src=- shape=13d707e8 vocab=67750c38
-/
lemma norm_kernelOpGoodKSimpleCLM_le {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ <= C :=
  LinearMap.mkContinuous_norm_le
    (kernelOpGoodKSimpleLinearMap (mu := mu) hK) hC0 _

/--
@isnad1 id=le.3h4v.s13.a57274a57032 from=translated src=- shape=ed2c8e65 vocab=7d55584c
-/
lemma norm_kernelOpGoodKSimpleCLM_le_sqrt_kernelSqNorm
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ <=
      Real.sqrt (kernelSqNorm mu K) := by
  refine ContinuousLinearMap.opNorm_le_bound
    (kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
    (Real.sqrt_nonneg _) ?_
  intro s
  change ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
    Real.sqrt (kernelSqNorm mu K) * ‖(s : Lp Real 2 mu)‖
  exact norm_kernelOpGoodKSimple_le_sqrt_kernelSqNorm (mu := mu) hK s

/--
@isnad1 id=eq.1h5v.s13.03d1476fbab5 from=translated src=- shape=bb988010 vocab=82243ddd
-/
lemma kernelOpSimple_add (hW : IsGraphon W mu)
    (s t : Lp.simpleFunc Real 2 mu) :
    kernelOpSimple (mu := mu) hW (s + t) =
      kernelOpSimple (mu := mu) hW s +
        kernelOpSimple (mu := mu) hW t := by
  calc
    kernelOpSimple (mu := mu) hW (s + t)
        =
          kernelOpL2OfGood (mu := mu) hW
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t)) := by
          exact kernelOpL2OfGood_congr (mu := mu) hW
            (simpleFunc_good (mu := mu) (s + t))
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t))
            (Lp.simpleFunc.add_toSimpleFunc s t)
    _ =
      kernelOpSimple (mu := mu) hW s +
        kernelOpSimple (mu := mu) hW t := by
          exact kernelOpL2OfGood_add hW
            (simpleFunc_good (mu := mu) s)
            (simpleFunc_good (mu := mu) t)

/--
@isnad1 id=eq.1h5v.s13.fd38844725cb from=translated src=- shape=62bd0270 vocab=9b558444
-/
lemma kernelOpSimple_smul (hW : IsGraphon W mu)
    (c : Real) (s : Lp.simpleFunc Real 2 mu) :
    kernelOpSimple (mu := mu) hW (c • s) =
      c • kernelOpSimple (mu := mu) hW s := by
  calc
    kernelOpSimple (mu := mu) hW (c • s)
        =
          kernelOpL2OfGood (mu := mu) hW
            (good_smul c (simpleFunc_good (mu := mu) s)) := by
          exact kernelOpL2OfGood_congr (mu := mu) hW
            (simpleFunc_good (mu := mu) (c • s))
            (good_smul c (simpleFunc_good (mu := mu) s))
            (Lp.simpleFunc.smul_toSimpleFunc c s)
    _ = c • kernelOpSimple (mu := mu) hW s := by
          exact kernelOpL2OfGood_smul hW c (simpleFunc_good (mu := mu) s)

/--
@isnad1 id=le.1h4v.s11.e05ea251366e from=translated src=- shape=3a073668 vocab=e9bb3f8d
-/
lemma norm_kernelOpSimple_le (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    ‖kernelOpSimple (mu := mu) hW s‖ <= ‖(s : Lp Real 2 mu)‖ := by
  simpa [kernelOpSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
    norm_kernelOpL2OfGood_le_norm_goodL2 hW
      (simpleFunc_good (mu := mu) s)

def kernelOpSimpleLinearMap (hW : IsGraphon W mu) :
    Lp.simpleFunc Real 2 mu →ₗ[Real] Lp Real 2 mu where
  toFun := kernelOpSimple (mu := mu) hW
  map_add' := kernelOpSimple_add (mu := mu) hW
  map_smul' := kernelOpSimple_smul (mu := mu) hW

def kernelOpSimpleCLM (hW : IsGraphon W mu) :
    Lp.simpleFunc Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpSimpleLinearMap (mu := mu) hW).mkContinuous 1
      (fun s => by
        change ‖kernelOpSimple (mu := mu) hW s‖ <= 1 * ‖(s : Lp Real 2 mu)‖
        simpa [one_mul] using norm_kernelOpSimple_le (mu := mu) hW s)

def simpleFuncToL2 :
    Lp.simpleFunc Real 2 mu →L[Real] Lp Real 2 mu :=
  Lp.simpleFunc.coeToLp (α := Omega) (E := Real) (𝕜 := Real)
    (p := (2 : ENNReal)) (μ := mu)

def kernelOpGoodKCLM {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    Lp Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC).extend
    (simpleFuncToL2 (mu := mu))

noncomputable def clmIter
    (T : Lp Real 2 mu →L[Real] Lp Real 2 mu) :
    Nat -> Lp Real 2 mu -> Lp Real 2 mu
  | 0, f => f
  | n + 1, f => T (clmIter T n f)

/--
@isnad1 id=eq.3h5v.s13.d27a923fbfe1 from=translated src=- shape=c8af6acf vocab=8d0df83f
-/
lemma kernelOpGoodKCLM_simpleFunc {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC (s : Lp Real 2 mu) =
      kernelOpGoodKSimple (mu := mu) hK s := by
  change
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC
      ((simpleFuncToL2 (mu := mu)) s) =
      kernelOpGoodKSimple (mu := mu) hK s
  simpa [kernelOpGoodKCLM, simpleFuncToL2, kernelOpGoodKSimpleCLM,
    kernelOpGoodKSimpleLinearMap] using
    ContinuousLinearMap.extend_eq
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      s

/--
@isnad1 id=eq.4h5v.s12.08ed2e18fedb from=translated src=- shape=ff445f0a vocab=74f912f3
-/
lemma kernelOpGoodKCLM_goodL2 {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC
        (goodL2 (mu := mu) hf) =
      kernelOpL2OfGoodK (mu := mu) hK hf := by
  let T : Lp Real 2 mu -> Lp Real 2 mu :=
    fun x => kernelOpGoodKCLM (mu := mu) hK hC0 hKC x
  let y : Lp Real 2 mu := kernelOpL2OfGoodK (mu := mu) hK hf
  let x0 : Lp Real 2 mu := goodL2 (mu := mu) hf
  set p : Lp Real 2 mu -> Prop :=
    fun x => ‖T x - y‖ <= C * ‖x - x0‖
  have hp_x0 : p x0 := by
    apply DenseRange.induction_on (p := p)
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      x0
    · dsimp [p, T, x0, y]
      exact isClosed_le (by fun_prop) (by fun_prop)
    · intro s
      dsimp [p, T, x0, y]
      rw [kernelOpGoodKCLM_simpleFunc (mu := mu) hK hC0 hKC s]
      simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
        norm_kernelOpL2OfGoodK_sub_le_const_mul_norm_goodL2_sub
          (mu := mu) hK hC0 hKC
          (simpleFunc_good (mu := mu) s) hf
  have hnorm :
      ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC
          (goodL2 (mu := mu) hf) -
        kernelOpL2OfGoodK (mu := mu) hK hf‖ <= 0 := by
    simpa [p, T, x0, y] using hp_x0
  have hzero :
      kernelOpGoodKCLM (mu := mu) hK hC0 hKC
          (goodL2 (mu := mu) hf) -
        kernelOpL2OfGoodK (mu := mu) hK hf = 0 := by
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact sub_eq_zero.mp hzero

/--
@isnad1 id=eq.4h6v.s8.f1097e8f3a76 from=translated src=- shape=b3dde155 vocab=84c6198b
-/
lemma kernelOpGoodKCLM_iter_goodL2 {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    forall n,
      clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC) n
          (goodL2 (mu := mu) hf) =
        goodL2 (mu := mu) (good_kernelOpIter_goodK (mu := mu) hK hf n)
  | 0 => rfl
  | n + 1 => by
      calc
        clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
            (n + 1) (goodL2 (mu := mu) hf)
            =
              kernelOpGoodKCLM (mu := mu) hK hC0 hKC
                (goodL2 (mu := mu)
                  (good_kernelOpIter_goodK (mu := mu) hK hf n)) := by
              change
                kernelOpGoodKCLM (mu := mu) hK hC0 hKC
                    (clmIter (mu := mu)
                      (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
                      n (goodL2 (mu := mu) hf)) =
                  kernelOpGoodKCLM (mu := mu) hK hC0 hKC
                    (goodL2 (mu := mu)
                      (good_kernelOpIter_goodK (mu := mu) hK hf n))
              rw [kernelOpGoodKCLM_iter_goodL2 hK hC0 hKC hf n]
        _ =
              kernelOpL2OfGoodK (mu := mu) hK
                (good_kernelOpIter_goodK (mu := mu) hK hf n) := by
              exact kernelOpGoodKCLM_goodL2 (mu := mu) hK hC0 hKC
                (good_kernelOpIter_goodK (mu := mu) hK hf n)
        _ =
              goodL2 (mu := mu)
                (good_kernelOpIter_goodK (mu := mu) hK hf (n + 1)) := rfl

/--
@isnad1 id=le.3h4v.s11.77161f906f3d from=translated src=- shape=33ac2830 vocab=8bcbc91a
-/
lemma norm_kernelOpGoodKCLM_le {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖ <= C := by
  have h_ext :
      ‖(kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC).extend
          (simpleFuncToL2 (mu := mu))‖ <=
        1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
    exact ContinuousLinearMap.opNorm_extend_le
      (N := (1 : NNReal))
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (fun s => by
        change ‖(simpleFuncToL2 (mu := mu)) s‖ <= ((1 : NNReal) : Real) *
          ‖(s : Lp Real 2 mu)‖
        rw [NNReal.coe_one, one_mul]
        exact le_of_eq rfl)
  calc
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖
        <= 1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          simpa [kernelOpGoodKCLM] using h_ext
    _ = ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          exact one_mul _
    _ <= C := by
          exact norm_kernelOpGoodKSimpleCLM_le
            (mu := mu) hK hC0 hKC

/--
@isnad1 id=le.3h4v.s11.9375572e9c90 from=translated src=- shape=e547d526 vocab=eaa961c7
-/
lemma norm_kernelOpGoodKCLM_le_sqrt_kernelSqNorm
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖ <=
      Real.sqrt (kernelSqNorm mu K) := by
  have h_ext :
      ‖(kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC).extend
          (simpleFuncToL2 (mu := mu))‖ <=
        1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
    exact ContinuousLinearMap.opNorm_extend_le
      (N := (1 : NNReal))
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (fun s => by
        change ‖(simpleFuncToL2 (mu := mu)) s‖ <= ((1 : NNReal) : Real) *
          ‖(s : Lp Real 2 mu)‖
        rw [NNReal.coe_one, one_mul]
        exact le_of_eq rfl)
  calc
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖
        <= 1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          simpa [kernelOpGoodKCLM] using h_ext
    _ = ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          exact one_mul _
    _ <= Real.sqrt (kernelSqNorm mu K) := by
          exact norm_kernelOpGoodKSimpleCLM_le_sqrt_kernelSqNorm
            (mu := mu) hK hC0 hKC

/--
@isnad1 id=eq.8h7v.s13.4cb0df8afea0 from=translated src=- shape=16df358f vocab=74b3606b
-/
lemma kernelOpGoodKCLM_sub_kernel {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {CK CL C : Real}
    (hCK0 : 0 <= CK) (hKC : forall x y, |K x y| <= CK)
    (hCL0 : 0 <= CL) (hLC : forall x y, |L x y| <= CL)
    (hC0 : 0 <= C) (hSubC : forall x y, |K x y - L x y| <= C) :
    kernelOpGoodKCLM (mu := mu) (goodK_sub hK hL)
        hC0 hSubC =
      kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC := by
  have hcomp :
      (kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC).comp
          (simpleFuncToL2 (mu := mu)) =
        kernelOpGoodKSimpleCLM (mu := mu)
          (goodK_sub hK hL) hC0 hSubC := by
    apply ContinuousLinearMap.ext
    intro s
    change
      (kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC)
          ((simpleFuncToL2 (mu := mu)) s) =
        kernelOpGoodKSimple (mu := mu) (goodK_sub hK hL) s
    rw [sub_apply]
    calc
      kernelOpGoodKCLM (mu := mu) hK hCK0 hKC
          ((simpleFuncToL2 (mu := mu)) s) -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC
            ((simpleFuncToL2 (mu := mu)) s)
          =
            kernelOpGoodKCLM (mu := mu) hK hCK0 hKC
              (s : Lp Real 2 mu) -
            kernelOpGoodKCLM (mu := mu) hL hCL0 hLC
              (s : Lp Real 2 mu) := by
            rfl
      _
          =
            kernelOpGoodKSimple (mu := mu) hK s -
              kernelOpGoodKSimple (mu := mu) hL s := by
            rw [← kernelOpGoodKCLM_simpleFunc
                (mu := mu) hK hCK0 hKC s,
              ← kernelOpGoodKCLM_simpleFunc
                (mu := mu) hL hCL0 hLC s]
      _ =
          kernelOpGoodKSimple (mu := mu) (goodK_sub hK hL) s := by
            exact (kernelOpGoodKSimple_sub_kernel
              (mu := mu) hK hL s).symm
  have huniq :
      (kernelOpGoodKSimpleCLM (mu := mu)
          (goodK_sub hK hL) hC0 hSubC).extend
          (simpleFuncToL2 (mu := mu)) =
        kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC := by
    exact ContinuousLinearMap.extend_unique
      (f := kernelOpGoodKSimpleCLM (mu := mu)
        (goodK_sub hK hL) hC0 hSubC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      (kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC)
      hcomp
  simpa [kernelOpGoodKCLM] using huniq

/--
@isnad1 id=le.8h7v.s13.7457fd31c0f7 from=translated src=- shape=c9ba2109 vocab=79deab70
-/
lemma norm_kernelOpGoodKCLM_sub_le_sqrt_kernelSqNorm
    {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {CK CL C : Real}
    (hCK0 : 0 <= CK) (hKC : forall x y, |K x y| <= CK)
    (hCL0 : 0 <= CL) (hLC : forall x y, |L x y| <= CL)
    (hC0 : 0 <= C) (hSubC : forall x y, |K x y - L x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC‖ <=
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - L x y)) := by
  rw [← kernelOpGoodKCLM_sub_kernel
    (mu := mu) hK hL hCK0 hKC hCL0 hLC hC0 hSubC]
  exact norm_kernelOpGoodKCLM_le_sqrt_kernelSqNorm
    (mu := mu) (goodK_sub hK hL) hC0 hSubC

def kernelOpCLM (hW : IsGraphon W mu) :
    Lp Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpSimpleCLM (mu := mu) hW).extend (simpleFuncToL2 (mu := mu))

/--
@isnad1 id=eq.1h4v.s13.ba94c692fd82 from=translated src=- shape=2edbb869 vocab=d52d071d
-/
lemma kernelOpCLM_simpleFunc (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpCLM (mu := mu) hW (s : Lp Real 2 mu) =
      kernelOpSimple (mu := mu) hW s := by
  change
    kernelOpCLM (mu := mu) hW ((simpleFuncToL2 (mu := mu)) s) =
      kernelOpSimple (mu := mu) hW s
  simpa [kernelOpCLM, simpleFuncToL2, kernelOpSimpleCLM,
    kernelOpSimpleLinearMap] using
    ContinuousLinearMap.extend_eq
      (f := kernelOpSimpleCLM (mu := mu) hW)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      s

/--
@isnad1 id=eq.1h3v.s11.b0bcf7a0b38a from=translated src=- shape=7df613cb vocab=4ffa9ea9
-/
lemma kernelOpCLM_eq_kernelOpGoodKCLM (hW : IsGraphon W mu) :
    kernelOpCLM (mu := mu) hW =
      kernelOpGoodKCLM (mu := mu) (goodK_of_isGraphon hW)
        zero_le_one (graphon_abs_le_one (mu := mu) hW) := by
  let hK : GoodK W := goodK_of_isGraphon hW
  let hKC : forall x y, |W x y| <= 1 := graphon_abs_le_one (mu := mu) hW
  have hcomp :
      (kernelOpCLM (mu := mu) hW).comp (simpleFuncToL2 (mu := mu)) =
        kernelOpGoodKSimpleCLM (mu := mu) hK zero_le_one hKC := by
    apply ContinuousLinearMap.ext
    intro s
    change kernelOpCLM (mu := mu) hW ((simpleFuncToL2 (mu := mu)) s) =
      kernelOpGoodKSimple (mu := mu) hK s
    calc
      kernelOpCLM (mu := mu) hW ((simpleFuncToL2 (mu := mu)) s)
          = kernelOpCLM (mu := mu) hW (s : Lp Real 2 mu) := by
            rfl
      _ = kernelOpSimple (mu := mu) hW s := by
            exact kernelOpCLM_simpleFunc (mu := mu) hW s
      _ = kernelOpGoodKSimple (mu := mu) hK s := by
            simpa [hK] using
              kernelOpSimple_eq_kernelOpGoodKSimple (mu := mu) hW s
  have huniq :
      (kernelOpGoodKSimpleCLM (mu := mu) hK zero_le_one hKC).extend
          (simpleFuncToL2 (mu := mu)) =
        kernelOpCLM (mu := mu) hW := by
    exact ContinuousLinearMap.extend_unique
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK zero_le_one hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      (kernelOpCLM (mu := mu) hW)
      hcomp
  simpa [kernelOpGoodKCLM, hK, hKC] using huniq.symm

/--
@isnad1 id=eq.2h4v.s12.6435269fac50 from=translated src=- shape=713801ae vocab=1290d529
-/
lemma kernelOpCLM_goodL2 (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf) =
      kernelOpL2OfGood (mu := mu) hW hf := by
  rw [kernelOpCLM_eq_kernelOpGoodKCLM (mu := mu) hW]
  rw [kernelOpL2OfGood_eq_kernelOpL2OfGoodK (mu := mu) hW hf]
  exact kernelOpGoodKCLM_goodL2 (mu := mu)
    (goodK_of_isGraphon hW)
    zero_le_one (graphon_abs_le_one (mu := mu) hW) hf

def oneSimpleL2 :
    Lp.simpleFunc Real 2 mu :=
  SimpleFunc.toLp (SimpleFunc.const Omega (1 : Real))
    ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
      (2 : ENNReal) mu)

/--
@isnad1 id=eq.0h2v.s10.47809008b5f6 from=translated src=- shape=b943bb9e vocab=64204ab1
-/
lemma oneSimpleL2_coe_eq_oneL2 :
    (oneSimpleL2 (Omega := Omega) (mu := mu) : Lp Real 2 mu) =
      oneL2 (Omega := Omega) mu := by
  calc
    (oneSimpleL2 (Omega := Omega) (mu := mu) : Lp Real 2 mu)
        =
          ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
            (2 : ENNReal) mu).toLp
              (SimpleFunc.const Omega (1 : Real)) := rfl
    _ = (memLp_const (1 : Real)).toLp (fun _ : Omega => 1) := by
          exact MemLp.toLp_congr
            ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
              (2 : ENNReal) mu)
            (memLp_const (1 : Real))
            (ae_of_all _ fun _ => rfl)
    _ = oneL2 (Omega := Omega) mu := rfl

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.0h3v.s5.7b4a3b388927 from=translated src=- shape=5ae0fec6 vocab=ea4eabec
-/
lemma kernelOp_one_eq_degree :
    kernelOp W mu (fun _ : Omega => 1) = degree W mu := by
  funext x
  simp [kernelOp, degree]

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.0h3v.s5.a1e48db3d008 from=translated src=- shape=f2a84baa vocab=e7b211be
-/
lemma integral_one_mul_degree_eq_edgeDensity :
    (∫ x, (1 : Real) * degree W mu x ∂mu) = edgeDensity W mu := by
  simp [edgeDensity, mean]

/--
@isnad1 id=eq.1h3v.s7.92ec3ecf1ad2 from=translated src=- shape=aaf8fba6 vocab=f929a810
-/
lemma kernelOpL2OfGood_one_eq_degreeL2 (hW : IsGraphon W mu) :
    kernelOpL2OfGood (mu := mu) hW (good_one (Ω := Omega)) =
      degreeL2 hW := by
  exact MemLp.toLp_congr
    (kernelOp_memLp_two hW (good_one (Ω := Omega)))
    (degree_memLp_two hW)
    (ae_of_all _ fun x => congrFun (kernelOp_one_eq_degree (mu := mu) (W := W)) x)

/--
@isnad1 id=eq.1h3v.s7.0b068a769f59 from=translated src=- shape=b66481dc vocab=fa498bb0
-/
lemma kernelOpSimple_one_eq_degreeL2 (hW : IsGraphon W mu) :
    kernelOpSimple (mu := mu) hW (oneSimpleL2 (Omega := Omega) (mu := mu)) =
      degreeL2 hW := by
  calc
    kernelOpSimple (mu := mu) hW (oneSimpleL2 (Omega := Omega) (mu := mu))
        =
          kernelOpL2OfGood (mu := mu) hW (good_one (Ω := Omega)) := by
          exact kernelOpL2OfGood_congr (mu := mu) hW
            (simpleFunc_good (mu := mu)
              (oneSimpleL2 (Omega := Omega) (mu := mu)))
            (good_one (Ω := Omega))
            (Lp.simpleFunc.toSimpleFunc_toLp
              (SimpleFunc.const Omega (1 : Real))
              ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
                (2 : ENNReal) mu))
    _ = degreeL2 hW := kernelOpL2OfGood_one_eq_degreeL2 hW

/--
@isnad1 id=eq.1h3v.s12.2a32f8088699 from=translated src=- shape=3dc1a7af vocab=e5cb96e4
-/
lemma kernelOpCLM_one_eq_degreeL2 (hW : IsGraphon W mu) :
    kernelOpCLM (mu := mu) hW (oneL2 (Omega := Omega) mu) =
      degreeL2 hW := by
  rw [← oneSimpleL2_coe_eq_oneL2 (Omega := Omega) (mu := mu)]
  rw [kernelOpCLM_simpleFunc hW]
  exact kernelOpSimple_one_eq_degreeL2 hW

/--
@isnad1 id=eq.3h5v.s8.ead11a940d61 from=translated src=- shape=ba578e82 vocab=1dab8130
-/
lemma inner_goodL2_kernelOpL2OfGood_eq_integral
    (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    inner Real (goodL2 (mu := mu) hg)
      (kernelOpL2OfGood (mu := mu) hW hf) =
      ∫ x, g x * kernelOp W mu f x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hgae := goodL2_ae_eq (mu := mu) hg
  have hkfae := kernelOpL2OfGood_ae_eq (mu := mu) hW hf
  refine integral_congr_ae ?_
  filter_upwards [hgae, hkfae] with x hgx hkfx
  rw [hgx, hkfx]
  simp [RCLike.inner_apply, mul_comm]

/--
@isnad1 id=eq.3h5v.s8.2251196aaf50 from=translated src=- shape=9629018e vocab=1dab8130
-/
lemma inner_kernelOpL2OfGood_goodL2_eq_integral
    (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    inner Real (kernelOpL2OfGood (mu := mu) hW hf)
      (goodL2 (mu := mu) hg) =
      ∫ x, kernelOp W mu f x * g x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hkfae := kernelOpL2OfGood_ae_eq (mu := mu) hW hf
  have hgae := goodL2_ae_eq (mu := mu) hg
  refine integral_congr_ae ?_
  filter_upwards [hkfae, hgae] with x hkfx hgx
  rw [hkfx, hgx]
  simp [RCLike.inner_apply, mul_comm]

/--
@isnad1 id=le.2h4v.s8.2f3729826dcb from=translated src=- shape=b00d8f2a vocab=1c5e94d1
-/
lemma abs_inner_goodL2_kernelOpL2OfGood_self_le_abs
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    |inner Real (goodL2 (mu := mu) hf)
        (kernelOpL2OfGood (mu := mu) hW hf)| <=
      inner Real
        (goodL2 (mu := mu) (good_abs hf))
        (kernelOpL2OfGood (mu := mu) hW (good_abs hf)) := by
  rw [inner_goodL2_kernelOpL2OfGood_eq_integral hW hf hf,
    inner_goodL2_kernelOpL2OfGood_eq_integral hW (good_abs hf) (good_abs hf)]
  calc
    |∫ x, f x * kernelOp W mu f x ∂mu|
        <= ∫ x, |f x * kernelOp W mu f x| ∂mu := by
          exact abs_integral_le_integral_abs
    _ <= ∫ x, |f x| * kernelOp W mu (fun y : Omega => |f y|) x ∂mu := by
          refine integral_mono
            ((hf.mul (good_kernelOp hW hf)).integrable).abs
            ((good_abs hf).mul (good_kernelOp hW (good_abs hf))).integrable ?_
          intro x
          change |f x * kernelOp W mu f x| <=
            |f x| * kernelOp W mu (fun y : Omega => |f y|) x
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (abs_kernelOp_le_kernelOp_abs hW hf x) (abs_nonneg (f x))

/--
@isnad1 id=le.2h4v.s13.77389bf49429 from=translated src=- shape=f82ed795 vocab=91de1845
-/
lemma abs_inner_goodL2_kernelOpCLM_self_le_abs
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    |inner Real (goodL2 (mu := mu) hf)
        (kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf))| <=
      inner Real
        |goodL2 (mu := mu) hf|
        (kernelOpCLM (mu := mu) hW |goodL2 (mu := mu) hf|) := by
  rw [kernelOpCLM_goodL2 (mu := mu) hW hf]
  rw [← goodL2_abs (mu := mu) hf]
  rw [kernelOpCLM_goodL2 (mu := mu) hW (good_abs hf)]
  exact abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hW hf

/--
@isnad1 id=eq.3h5v.s8.7734dc99c1d6 from=translated src=- shape=c65edfeb vocab=01e8cb7a
-/
lemma kernelOpL2OfGood_selfadj (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    inner Real (kernelOpL2OfGood (mu := mu) hW hf)
        (goodL2 (mu := mu) hg) =
      inner Real (goodL2 (mu := mu) hf)
        (kernelOpL2OfGood (mu := mu) hW hg) := by
  rw [inner_kernelOpL2OfGood_goodL2_eq_integral hW hf hg,
    inner_goodL2_kernelOpL2OfGood_eq_integral hW hg hf]
  exact kernelOp_symm hW hf hg

/--
@isnad1 id=issymmet.1h3v.s11.171f7a65266f from=translated src=- shape=841eb4ed vocab=df913897
-/
lemma kernelOpCLM_isSymmetric (hW : IsGraphon W mu) :
    (kernelOpCLM (mu := mu) hW :
      Lp Real 2 mu →ₗ[Real] Lp Real 2 mu).IsSymmetric := by
  intro f g
  let e : Lp.simpleFunc Real 2 mu -> Lp Real 2 mu :=
    fun s => (s : Lp Real 2 mu)
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  refine hdense.induction_on₂
    (p := fun f g =>
      inner Real (kernelOpCLM (mu := mu) hW f) g =
        inner Real f (kernelOpCLM (mu := mu) hW g))
    ?closed ?simple f g
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro s t
    dsimp [e]
    rw [kernelOpCLM_simpleFunc hW s, kernelOpCLM_simpleFunc hW t]
    dsimp [kernelOpSimple]
    have h :=
      kernelOpL2OfGood_selfadj (mu := mu) hW
        (simpleFunc_good (mu := mu) s) (simpleFunc_good (mu := mu) t)
    simpa [goodL2_simpleFunc_eq_coe (mu := mu) s,
      goodL2_simpleFunc_eq_coe (mu := mu) t] using h

/--
@isnad1 id=eq.1h3v.s7.e1a27a37123e from=translated src=- shape=eeadec43 vocab=49481d8f
-/
lemma inner_oneL2_degreeL2_eq_edgeDensity
    (hW : IsGraphon W mu) :
    inner Real (oneL2 (Omega := Omega) mu) (degreeL2 hW) =
      edgeDensity W mu := by
  rw [MeasureTheory.L2.inner_def]
  have hone := oneL2_ae_eq_one (Omega := Omega) (mu := mu)
  have hdeg : (degreeL2 hW : Omega -> Real) =ᵐ[mu] degree W mu := by
    change
      ((degree_memLp_two hW).toLp (degree W mu) : Omega -> Real) =ᵐ[mu]
        degree W mu
    exact MemLp.coeFn_toLp (degree_memLp_two hW)
  calc
    (∫ x : Omega,
        inner Real ((oneL2 (Omega := Omega) mu : Lp Real 2 mu) x)
          ((degreeL2 hW : Lp Real 2 mu) x) ∂mu)
        = ∫ x : Omega, (1 : Real) * degree W mu x ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [hone, hdeg] with x hxone hxdeg
          rw [hxone, hxdeg]
          simp
    _ = edgeDensity W mu := integral_one_mul_degree_eq_edgeDensity

/--
@isnad1 id=eq.0h2v.s7.215b0588520f from=translated src=- shape=284e2e93 vocab=944bb727
-/
lemma inner_oneL2_oneL2 :
    inner Real (oneL2 (Omega := Omega) mu) (oneL2 (Omega := Omega) mu) =
      1 := by
  rw [MeasureTheory.L2.inner_def]
  have hone := oneL2_ae_eq_one (Omega := Omega) (mu := mu)
  calc
    (∫ x : Omega,
        inner Real ((oneL2 (Omega := Omega) mu : Lp Real 2 mu) x)
          ((oneL2 (Omega := Omega) mu : Lp Real 2 mu) x) ∂mu)
        = ∫ _x : Omega, (1 : Real) ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [hone] with x hxone
          rw [hxone]
          simp
    _ = 1 := by simp

/--
@isnad1 id=eq.0h2v.s7.8b02b421ab63 from=translated src=- shape=bc306a4d vocab=89973d8e
-/
lemma norm_oneL2_sq :
    ‖oneL2 (Omega := Omega) mu‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_oneL2_oneL2]

end L2Kernel
end Spectral
end OddCycleBound
