import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.FormalShift
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.KernelBlockDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators PowerSeries

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

/--
@isnad1 id=good.1h3v.s4.27230a35db5c from=translated src=- shape=4894df6c vocab=9d55f5b6
-/
lemma good_col_of_goodK {K : Omega → Omega → Real} (hK : GoodK K) (y : Omega) :
    Good (fun x => K x y) := by
  obtain ⟨C, hC0, hKC⟩ := hK.bdd
  refine ⟨(hK.meas.comp
    (measurable_id.prodMk measurable_const)).stronglyMeasurable,
    ⟨C, hC0, fun x => hKC x y⟩⟩

/--
@isnad1 id=eq.2h4v.s5.8cc7fa27fafc from=translated src=- shape=15affd66 vocab=bc129e89
-/
lemma mean_kernelOp_eq_pairing_degree
    (hW : IsGraphon W mu) {f : Omega → Real} (hf : Good f) :
    mean mu (kernelOp W mu f) = pairing mu f (degree W mu) := by
  calc
    mean mu (kernelOp W mu f) =
        ∫ x, kernelOp W mu f x * (1 : Real) ∂mu := by simp [mean]
    _ = ∫ x, f x * kernelOp W mu (fun _ : Omega => (1 : Real)) x ∂mu :=
      kernelOp_selfadj hW hf good_one
    _ = pairing mu f (degree W mu) := by
      rw [kernelOp_one hW]
      rfl

/--
@isnad1 id=eq.3h5v.s6.24090fc681a2 from=translated src=- shape=1321d201 vocab=0ddc5cc3
-/
lemma kernelOp_eq_pairing_degCentered_add_centered
    (hW : IsGraphon W mu) {f : Omega → Real} (hf : Good f)
    (hf0 : mean mu f = 0) (x : Omega) :
    kernelOp W mu f x =
      pairing mu (degCentered W mu) f +
        kernelOp (centeredKernel W mu) mu f x := by
  have hmean : mean mu (kernelOp W mu f) =
      pairing mu (degCentered W mu) f := by
    rw [mean_kernelOp_eq_pairing_degree hW hf]
    unfold pairing
    have hdegree : ∀ z, degree W mu z =
        edgeDensity W mu + degCentered W mu z := degree_eq
    have hintegrand : ∀ z, f z * degree W mu z =
        edgeDensity W mu * f z + degCentered W mu z * f z := by
      intro z
      rw [hdegree z]
      ring
    rw [integral_congr_ae (ae_of_all _ hintegrand)]
    rw [integral_add
      (hf.integrable.const_mul (edgeDensity W mu))
      ((good_degCentered hW).mul hf).integrable,
      integral_const_mul]
    unfold mean at hf0
    rw [hf0]
    ring
  have hcenter :=
    kernelOp_centeredKernel_eq_compress_centeredInput hW hf x
  unfold centeredInput at hcenter
  rw [hf0] at hcenter
  simp only [sub_zero] at hcenter
  unfold compress at hcenter
  rw [hmean] at hcenter
  linarith

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.1h5v.s5.5842554c2538 from=translated src=- shape=4f8e9c4f vocab=a08de1f7
-/
lemma kernelOp_const_eq_mul_degree
    (_hW : IsGraphon W mu) (c : Real) (x : Omega) :
    kernelOp W mu (fun _ : Omega => c) x = c * degree W mu x := by
  unfold kernelOp degree
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

/--
@isnad1 id=eq.4h5v.s7.e71cf35d8f37 from=translated src=- shape=bd8f0ea0 vocab=711ab163
-/
lemma kernelOp_goodK_symm {K : Omega → Omega → Real}
    (hK : GoodK K) (hKsymm : ∀ x y, K x y = K y x)
    {f k : Omega → Real} (hf : Good f) (hk : Good k) :
    ∫ x, kernelOp K mu f x * k x ∂mu =
      ∫ x, f x * kernelOp K mu k x ∂mu := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Ck, hCk0, hCk⟩ := hk.bdd
  have hSM : StronglyMeasurable
      (Function.uncurry fun x y => K x y * f y * k x) := by
    have h1 : StronglyMeasurable (fun p : Omega × Omega => K p.1 p.2) :=
      hK.meas.stronglyMeasurable
    have h2 : StronglyMeasurable (fun p : Omega × Omega => f p.2) :=
      hf.meas.comp_measurable measurable_snd
    have h3 : StronglyMeasurable (fun p : Omega × Omega => k p.1) :=
      hk.meas.comp_measurable measurable_fst
    exact (h1.mul h2).mul h3
  have hInt : Integrable
      (Function.uncurry fun x y => K x y * f y * k x) (mu.prod mu) := by
    refine (integrable_const (CK * Cf * Ck)).mono'
      hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (mul_le_mul (hCK x y) (hCf y) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hCK x y)))
      (hCk x) (abs_nonneg _)
      (mul_nonneg (le_trans (abs_nonneg _) (hCK x y))
        (le_trans (abs_nonneg _) (hCf y)))
  have hL : ∀ x, kernelOp K mu f x * k x =
      ∫ y, K x y * f y * k x ∂mu := fun x => by
    rw [kernelOp, integral_mul_const]
  have hR : ∀ y, f y * kernelOp K mu k y =
      ∫ x, K x y * f y * k x ∂mu := fun y => by
    rw [kernelOp, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by
      change f y * (K y x * k x) = K x y * f y * k x
      rw [hKsymm y x]
      ring)
  calc
    (∫ x, kernelOp K mu f x * k x ∂mu) =
        ∫ x, ∫ y, K x y * f y * k x ∂mu ∂mu := by simp_rw [hL]
    _ = ∫ y, ∫ x, K x y * f y * k x ∂mu ∂mu :=
      integral_integral_swap hInt
    _ = ∫ y, f y * kernelOp K mu k y ∂mu := by simp_rw [hR]

/--
@isnad1 id=eq.3h4v.s6.10b4627a215e from=translated src=- shape=a7c31646 vocab=935ecb58
-/
lemma mean_kernelOp_centeredKernel_eq_zero {K : Omega → Omega → Real}
    (hK : GoodK K) (hKsymm : ∀ x y, K x y = K y x)
    {f : Omega → Real} (hf : Good f) :
    mean mu (kernelOp (centeredKernel K mu) mu f) = 0 := by
  let D := centeredKernel K mu
  have hD : GoodK D := centeredKernel_goodK_of_goodK (mu := mu) hK
  have hDsymm : ∀ x y, D x y = D y x := by
    intro x y
    dsimp [D]
    unfold centeredKernel
    rw [hKsymm x y]
    ring
  have hone : Good (fun _ : Omega => (1 : Real)) := good_one
  calc
    mean mu (kernelOp D mu f) =
        ∫ x, kernelOp D mu f x * (1 : Real) ∂mu := by simp [mean]
    _ = ∫ x, f x * kernelOp D mu (fun _ : Omega => (1 : Real)) x ∂mu :=
      kernelOp_goodK_symm hD hDsymm hf hone
    _ = 0 := by
      apply integral_eq_zero_of_ae
      exact ae_of_all _ fun x => by
        simp only [Pi.zero_apply]
        have hrow : kernelOp D mu (fun _ : Omega => (1 : Real)) x = 0 := by
          unfold kernelOp
          rw [show (fun y => D x y * (1 : Real)) = fun y => D x y by
            funext y
            ring]
          exact integral_centeredKernel_row (mu := mu) hK x
        rw [hrow]
        ring

/--
@isnad1 id=eq.9h7v.s7.d16a7dfda59d from=translated src=- shape=4fe39243 vocab=a7184516
-/
lemma centeredKernel_eq_body_of_block_decomposition
    {M B : Omega → Omega → Real} {a : Real}
    {X Y : Omega → Real}
    (hMsymm : ∀ x y, M x y = M y x)
    (hX : Good X) (hY : Good Y) (hB : GoodK B)
    (hX0 : mean mu X = 0) (hY0 : mean mu Y = 0)
    (hBrow : ∀ x, ∫ y, B x y ∂mu = 0)
    (hBcol : ∀ y, ∫ x, B x y ∂mu = 0)
    (hdecomp : ∀ x y, M x y = a + X x + Y y + B x y) :
    centeredKernel M mu = B := by
  have hdegree : ∀ x, degree M mu x = a + X x := by
    intro x
    unfold degree
    rw [integral_congr_ae (ae_of_all _ fun y => hdecomp x y)]
    have hconst : Integrable (fun _y : Omega => a + X x) mu :=
      integrable_const _
    have hYB : Integrable (fun y => Y y + B x y) mu :=
      hY.integrable.add (hB.integrable_row x)
    rw [show (fun y => a + X x + Y y + B x y) =
        fun y => (a + X x) + (Y y + B x y) by
          funext y
          ring,
      integral_add hconst hYB,
      integral_add hY.integrable (hB.integrable_row x)]
    unfold mean at hY0
    rw [hY0, hBrow x]
    simp
  have hcol : ∀ y, (∫ x, M x y ∂mu) = a + Y y := by
    intro y
    rw [integral_congr_ae (ae_of_all _ fun x => hdecomp x y)]
    have hconst : Integrable (fun _x : Omega => a + Y y) mu :=
      integrable_const _
    have hXB : Integrable (fun x => X x + B x y) mu :=
      hX.integrable.add (hB.integrable_col y)
    rw [show (fun x => a + X x + Y y + B x y) =
        fun x => (a + Y y) + (X x + B x y) by
          funext x
          ring,
      integral_add hconst hXB,
      integral_add hX.integrable (hB.integrable_col y)]
    unfold mean at hX0
    rw [hX0, hBcol y]
    simp
  have hXY : ∀ x, X x = Y x := by
    intro x
    have hsymmIntegral : (∫ y, M x y ∂mu) = ∫ y, M y x ∂mu :=
      integral_congr_ae (ae_of_all _ fun y => hMsymm x y)
    have hxrow := hdegree x
    have hxcol := hcol x
    unfold degree at hxrow
    linarith
  have hedge : edgeDensity M mu = a := by
    unfold edgeDensity
    rw [show degree M mu = fun x => a + X x by
      funext x
      exact hdegree x]
    unfold mean
    rw [integral_add (integrable_const _) hX.integrable]
    unfold mean at hX0
    rw [hX0]
    simp
  funext x y
  unfold centeredKernel
  rw [hdecomp x y, hdegree x, hdegree y, hedge, hXY y]
  ring

/--
@isnad1 id=goodk.2h3v.s5.614420ad1af8 from=translated src=- shape=94710602 vocab=4591a457
-/
lemma goodK_rankOne {f g : Omega → Real} (hf : Good f) (hg : Good g) :
    GoodK (fun x y => f x * g y) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨(hf.meas.measurable.comp measurable_fst).mul
      (hg.meas.measurable.comp measurable_snd),
    ⟨Cf * Cg, mul_nonneg hCf0 hCg0, fun x y => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hCf x) (hCg y) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hCf x))

/--
@isnad1 id=eq.2h5v.s6.e31f10b889a3 from=translated src=- shape=ee34613a vocab=0f1ec7fe
-/
lemma integral_comp_centeredKernel_row_eq_zero
    {K L : Omega → Omega → Real} (hK : GoodK K) (hL : GoodK L)
    (x : Omega) :
    ∫ y, comp mu (centeredKernel K mu) (centeredKernel L mu) x y ∂mu = 0 := by
  let C := centeredKernel K mu
  let D := centeredKernel L mu
  have hC : GoodK C := centeredKernel_goodK_of_goodK (mu := mu) hK
  have hD : GoodK D := centeredKernel_goodK_of_goodK (mu := mu) hL
  have hDone : kernelOp D mu (fun _ : Omega => (1 : Real)) = 0 := by
    funext z
    simp only [Pi.zero_apply]
    unfold kernelOp
    rw [show (fun y => D z y * (1 : Real)) = fun y => D z y by
      funext y
      ring]
    exact integral_centeredKernel_row (mu := mu) hL z
  have hcomp := kernelOp_comp_eq_kernelOp_kernelOp
    (mu := mu) hC hD good_one
  have hx := congrFun hcomp x
  rw [hDone] at hx
  simpa [kernelOp] using hx

/--
@isnad1 id=eq.4h5v.s6.3e74d91a1ff1 from=translated src=- shape=d46198e9 vocab=0f1ec7fe
-/
lemma integral_comp_centeredKernel_col_eq_zero
    {K L : Omega → Omega → Real} (hK : GoodK K) (hL : GoodK L)
    (hKsymm : ∀ x y, K x y = K y x)
    (hLsymm : ∀ x y, L x y = L y x) (y : Omega) :
    ∫ x, comp mu (centeredKernel K mu) (centeredKernel L mu) x y ∂mu = 0 := by
  have hCsymm : ∀ x z, centeredKernel K mu x z = centeredKernel K mu z x := by
    intro x z
    unfold centeredKernel
    rw [hKsymm x z]
    ring
  have hDsymm : ∀ x z, centeredKernel L mu x z = centeredKernel L mu z x := by
    intro x z
    unfold centeredKernel
    rw [hLsymm x z]
    ring
  calc
    (∫ x, comp mu (centeredKernel K mu) (centeredKernel L mu) x y ∂mu) =
        ∫ x, comp mu (centeredKernel L mu) (centeredKernel K mu) y x ∂mu := by
          exact integral_congr_ae (ae_of_all _ fun x =>
            comp_symm_swap hCsymm hDsymm y x)
    _ = 0 := integral_comp_centeredKernel_row_eq_zero hL hK y

/--
@isnad1 id=eq.3h6v.s7.f48f89e6ec79 from=translated src=- shape=dc6f0564 vocab=fe873250
-/
lemma comp_graphon_block_formula
    (hW : IsGraphon W mu) {K : Omega → Omega → Real}
    (hK : GoodK K) (hKsymm : ∀ x y, K x y = K y x)
    (x y : Omega) :
    comp mu W K x y =
      (edgeDensity K mu + degCentered K mu y) * degree W mu x +
        pairing mu (degCentered W mu) (degCentered K mu) +
        kernelOp (centeredKernel W mu) mu (degCentered K mu) x +
        kernelOp (centeredKernel K mu) mu (degCentered W mu) y +
        comp mu (centeredKernel W mu) (centeredKernel K mu) x y := by
  let c : Real := edgeDensity K mu + degCentered K mu y
  let f0 : Omega → Real := fun _ => c
  let f1 : Omega → Real := degCentered K mu
  let f2 : Omega → Real := fun z => centeredKernel K mu z y
  have hf0 : Good f0 := DenseRegion.good_const c
  have hf1 : Good f1 := good_degCentered_of_goodK (mu := mu) hK
  have hD : GoodK (centeredKernel K mu) :=
    centeredKernel_goodK_of_goodK (mu := mu) hK
  have hf2 : Good f2 := good_col_of_goodK hD y
  have hdecomp : (fun z => K z y) = f0 + f1 + f2 := by
    funext z
    dsimp [f0, f1, f2, c]
    rw [kernel_eq_block_decomposition (mu := mu) K z y]
    ring
  have hf1zero : mean mu f1 = 0 :=
    mean_degCentered_of_goodK (mu := mu) hK
  have hf2zero : mean mu f2 = 0 := by
    dsimp [f2]
    exact integral_centeredKernel_col (mu := mu) hK hKsymm y
  have hpair2 : pairing mu (degCentered W mu) f2 =
      kernelOp (centeredKernel K mu) mu (degCentered W mu) y := by
    unfold pairing kernelOp
    exact integral_congr_ae (ae_of_all _ fun z => by
      dsimp [f2]
      unfold centeredKernel
      rw [hKsymm z y]
      ring)
  have hbody : kernelOp (centeredKernel W mu) mu f2 x =
      comp mu (centeredKernel W mu) (centeredKernel K mu) x y := by
    rfl
  change kernelOp W mu (fun z => K z y) x = _
  rw [hdecomp,
    kernelOp_add' hW (good_add hf0 hf1) hf2 x,
    kernelOp_add' hW hf0 hf1 x,
    kernelOp_const_eq_mul_degree hW c x,
    kernelOp_eq_pairing_degCentered_add_centered hW hf1 hf1zero x,
    kernelOp_eq_pairing_degCentered_add_centered hW hf2 hf2zero x,
    hpair2, hbody]
  dsimp [c, f1]
  ring

/--
@isnad1 id=eq.1h4v.s6.fc106bdc0c8a from=translated src=- shape=ec99a3ee vocab=e7183210
-/
theorem centeredKernel_compPow_succ (hW : IsGraphon W mu) (n : Nat) :
    centeredKernel (compPow mu W (n + 1)) mu =
      fun x y =>
        degCentered W mu x * degCentered (compPow mu W n) mu y +
          comp mu (centeredKernel W mu)
            (centeredKernel (compPow mu W n) mu) x y := by
  let K := compPow mu W n
  let M := compPow mu W (n + 1)
  let g := degCentered W mu
  let h := degCentered K mu
  let C := centeredKernel W mu
  let D := centeredKernel K mu
  let a : Real := edgeDensity K mu * edgeDensity W mu + pairing mu g h
  let X : Omega → Real :=
    (edgeDensity K mu) • g + kernelOp C mu h
  let Y : Omega → Real :=
    (edgeDensity W mu) • h + kernelOp D mu g
  let B : Omega → Omega → Real := fun x y =>
    g x * h y + comp mu C D x y
  have hGW : GoodK W := goodK_of_isGraphon hW
  have hK : GoodK K := goodK_compPow (μ := mu) hGW n
  have hKsymm : ∀ x y, K x y = K y x :=
    compPow_symm (μ := mu) hGW hW.symm n
  have hMsymm : ∀ x y, M x y = M y x :=
    compPow_symm (μ := mu) hGW hW.symm (n + 1)
  have hg : Good g := good_degCentered hW
  have hh : Good h := good_degCentered_of_goodK (mu := mu) hK
  have hg0 : mean mu g = 0 := by
    simpa [g] using mean_degCentered_of_goodK (mu := mu) hGW
  have hh0 : mean mu h = 0 := mean_degCentered_of_goodK (mu := mu) hK
  have hC : GoodK C := centeredKernel_goodK_of_goodK (mu := mu) hGW
  have hD : GoodK D := centeredKernel_goodK_of_goodK (mu := mu) hK
  have hX : Good X := by
    dsimp [X]
    exact good_add (good_smul _ hg) (good_kernelOp_goodK (mu := mu) hC hh)
  have hY : Good Y := by
    dsimp [Y]
    exact good_add (good_smul _ hh) (good_kernelOp_goodK (mu := mu) hD hg)
  have hX0 : mean mu X = 0 := by
    dsimp [X]
    rw [mean_add (good_smul _ hg) (good_kernelOp_goodK (mu := mu) hC hh),
      mean_smul, hg0,
      mean_kernelOp_centeredKernel_eq_zero hGW hW.symm hh]
    ring
  have hY0 : mean mu Y = 0 := by
    dsimp [Y]
    rw [mean_add (good_smul _ hh) (good_kernelOp_goodK (mu := mu) hD hg),
      mean_smul, hh0,
      mean_kernelOp_centeredKernel_eq_zero hK hKsymm hg]
    ring
  have hB : GoodK B := by
    dsimp [B]
    exact goodK_add (goodK_rankOne hg hh) (goodK_comp hC hD)
  have hBrow : ∀ x, ∫ y, B x y ∂mu = 0 := by
    intro x
    have hprod : (∫ y, comp mu C D x y ∂mu) = 0 := by
      simpa [C, D, K] using
        (integral_comp_centeredKernel_row_eq_zero
          (mu := mu) hGW hK x)
    dsimp [B]
    rw [integral_add
      ((goodK_rankOne hg hh).integrable_row x)
      ((goodK_comp hC hD).integrable_row x),
      integral_const_mul]
    change g x * mean mu h + (∫ y, comp mu C D x y ∂mu) = 0
    rw [hh0, hprod]
    ring
  have hBcol : ∀ y, ∫ x, B x y ∂mu = 0 := by
    intro y
    have hprod : (∫ x, comp mu C D x y ∂mu) = 0 := by
      simpa [C, D, K] using
        (integral_comp_centeredKernel_col_eq_zero
          (mu := mu) hGW hK hW.symm hKsymm y)
    dsimp [B]
    rw [integral_add
      ((goodK_rankOne hg hh).integrable_col y)
      ((goodK_comp hC hD).integrable_col y),
      integral_mul_const]
    change mean mu g * h y + (∫ x, comp mu C D x y ∂mu) = 0
    rw [hg0, hprod]
    ring
  have hdecomp : ∀ x y, M x y = a + X x + Y y + B x y := by
    intro x y
    dsimp [M, K] at ⊢
    change comp mu W (compPow mu W n) x y = _
    rw [comp_graphon_block_formula hW hK hKsymm x y,
      degree_eq]
    dsimp [a, X, Y, B, g, h, C, D, K]
    ring
  have hcenter := centeredKernel_eq_body_of_block_decomposition
    (mu := mu) hMsymm hX hY hB hX0 hY0 hBrow hBcol hdecomp
  simpa [M, B, g, h, C, D, K] using hcenter

/--
@isnad1 id=eq.2h5v.s6.3084c189d358 from=translated src=- shape=2200e4ef vocab=6e50267c
-/
lemma comp_centeredKernel_rankOne_compressIter
    (hW : IsGraphon W mu) (j : Nat) {f : Omega → Real} (_hf : Good f) :
    comp mu (centeredKernel W mu)
        (fun x y => compressIter W mu j x * f y) =
      fun x y => compressIter W mu (j + 1) x * f y := by
  funext x y
  unfold comp
  rw [show
      (fun z => centeredKernel W mu x z *
        (compressIter W mu j z * f y)) =
        fun z => (centeredKernel W mu x z * compressIter W mu j z) * f y by
      funext z
      ring,
    integral_mul_const]
  change kernelOp (centeredKernel W mu) mu (compressIter W mu j) x * f y = _
  rw [kernelOp_centeredKernel_eq_compress_centeredInput
    hW (good_compressIter hW j) x]
  unfold centeredInput
  rw [mean_compressIter hW j]
  simp only [sub_zero]
  rfl

/--
@isnad1 id=eq.2h6v.s6.922d75c8e2ac from=translated src=- shape=7aa3b8ce vocab=296d41a0
-/
lemma comp_finset_sum_right_goodK {ι : Type*} (s : Finset ι)
    {K : Omega → Omega → Real} (hK : GoodK K)
    (L : ι → Omega → Omega → Real)
    (hL : ∀ i ∈ s, GoodK (L i)) :
    comp mu K (fun x y => ∑ i ∈ s, L i x y) =
      fun x y => ∑ i ∈ s, comp mu K (L i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext x y
      simp [comp]
  | @insert a s ha ih =>
      have hLa : GoodK (L a) := hL a (Finset.mem_insert_self a s)
      have hLs : ∀ i ∈ s, GoodK (L i) := by
        intro i hi
        exact hL i (Finset.mem_insert_of_mem hi)
      have hsum : GoodK (fun x y => ∑ i ∈ s, L i x y) :=
        goodK_finset_sum s L hLs
      rw [show (fun x y => ∑ i ∈ insert a s, L i x y) =
          fun x y => L a x y + ∑ i ∈ s, L i x y by
        funext x y
        rw [Finset.sum_insert ha],
        comp_add_right hK hLa hsum,
        ih hLs]
      funext x y
      rw [Finset.sum_insert ha]

/--
@isnad1 id=eq.1h4v.s6.801090ca1456 from=translated src=- shape=76f3240d vocab=5eb52f33
-/
theorem centeredKernel_compPow_expansion (hW : IsGraphon W mu) (n : Nat) :
    centeredKernel (compPow mu W n) mu = fun x y =>
      compPow mu (centeredKernel W mu) n x y +
        ∑ t ∈ Finset.range n,
          compressIter W mu (n - 1 - t) x *
            degCentered (compPow mu W t) mu y := by
  induction n with
  | zero =>
      simp [compPow]
  | succ n ih =>
      let A := centeredKernel W mu
      let R : Nat → Nat → Omega → Omega → Real := fun r t x y =>
        compressIter W mu (r - 1 - t) x *
          degCentered (compPow mu W t) mu y
      have hGW : GoodK W := goodK_of_isGraphon hW
      have hA : GoodK A := centeredKernel_goodK_of_goodK (mu := mu) hGW
      have hPow : GoodK (compPow mu A n) := goodK_compPow (μ := mu) hA n
      have hR : ∀ t ∈ Finset.range n, GoodK (R n t) := by
        intro t ht
        dsimp [R]
        exact goodK_rankOne (good_compressIter hW (n - 1 - t))
          (good_degCentered_of_goodK (mu := mu)
            (goodK_compPow (μ := mu) hGW t))
      have hSum : GoodK (fun x y => ∑ t ∈ Finset.range n, R n t x y) :=
        goodK_finset_sum (Finset.range n) (R n) hR
      have hcompAtoms :
          comp mu A (fun x y => ∑ t ∈ Finset.range n, R n t x y) =
            fun x y => ∑ t ∈ Finset.range n, R (n + 1) t x y := by
        calc
          comp mu A (fun x y => ∑ t ∈ Finset.range n, R n t x y) =
              (fun x y => ∑ t ∈ Finset.range n,
                comp mu A (R n t) x y) :=
            comp_finset_sum_right_goodK (mu := mu)
              (Finset.range n) hA (R n) hR
          _ = (fun x y => ∑ t ∈ Finset.range n, R (n + 1) t x y) := by
            funext x y
            apply Finset.sum_congr rfl
            intro t ht
            have htlt : t < n := Finset.mem_range.mp ht
            have harith : n - 1 - t + 1 = n + 1 - 1 - t := by omega
            have hadvance := comp_centeredKernel_rankOne_compressIter
              (mu := mu) hW (n - 1 - t)
              (good_degCentered_of_goodK (mu := mu)
                (goodK_compPow (μ := mu) hGW t))
            have hxy := congrFun (congrFun hadvance x) y
            simpa [A, R, harith] using hxy
      have hcomp :
          comp mu A (fun x y =>
            compPow mu A n x y + ∑ t ∈ Finset.range n, R n t x y) =
            fun x y => compPow mu A (n + 1) x y +
              ∑ t ∈ Finset.range n, R (n + 1) t x y := by
        rw [comp_add_right hA hPow hSum, hcompAtoms]
        rfl
      have hlast : R (n + 1) n = fun x y =>
          degCentered W mu x * degCentered (compPow mu W n) mu y := by
        funext x y
        have harith : n + 1 - 1 - n = 0 := by omega
        simp [R, compressIter_zero]
      rw [centeredKernel_compPow_succ hW n, ih]
      change (fun x y =>
        degCentered W mu x * degCentered (compPow mu W n) mu y +
          comp mu A (fun x y =>
            compPow mu A n x y + ∑ t ∈ Finset.range n, R n t x y) x y) = _
      rw [hcomp]
      funext x y
      rw [Finset.sum_range_succ]
      have hlastxy := congrFun (congrFun hlast x) y
      change degCentered W mu x * degCentered (compPow mu W n) mu y +
          (compPow mu A (n + 1) x y +
            ∑ t ∈ Finset.range n, R (n + 1) t x y) =
        compPow mu A (n + 1) x y +
          ((∑ t ∈ Finset.range n, R (n + 1) t x y) +
            R (n + 1) n x y)
      rw [hlastxy]
      ring

/--
@isnad1 id=eq.1h4v.s5.85a30f9c5a1c from=translated src=- shape=69d5a1c2 vocab=fa34478e
-/
lemma edgeDensity_compPow_eq_pathDensity (hW : IsGraphon W mu) (n : Nat) :
    edgeDensity (compPow mu W n) mu = pathDensity W mu (n + 1) := by
  unfold edgeDensity pathDensity
  rw [show degree (compPow mu W n) mu = pathIter W mu (n + 1) by
    exact rowsum_compPow hW n]

/--
@isnad1 id=eq.1h4v.s6.843f677a0536 from=translated src=- shape=80d0b991 vocab=af7193f9
-/
lemma degCentered_compPow_eq_centeredPathIter
    (hW : IsGraphon W mu) (n : Nat) :
    degCentered (compPow mu W n) mu = fun x =>
      pathIter W mu (n + 1) x - pathDensity W mu (n + 1) := by
  funext x
  unfold degCentered degree
  rw [congrFun (rowsum_compPow hW n) x,
    edgeDensity_compPow_eq_pathDensity hW n]

/--
@isnad1 id=eq.1h5v.s7.8bb153ccafe1 from=translated src=- shape=6c9712bb vocab=3e618d32
-/
lemma integral_compressIter_mul_degCentered_compPow
    (hW : IsGraphon W mu) (a t : Nat) :
    (∫ x, compressIter W mu a x *
      degCentered (compPow mu W t) mu x ∂mu) =
      ∑ k ∈ Finset.range (t + 1),
        pathDensity W mu (t - k) * specMoment W mu (a + k) := by
  have hdeg : degCentered (compPow mu W t) mu = fun z =>
      ∑ k ∈ Finset.range (t + 1),
        pathDensity W mu (t - k) * compressIter W mu k z := by
    rw [degCentered_compPow_eq_centeredPathIter hW t]
    funext z
    rw [congrFun (pathIter_expansion hW (t + 1)) z]
    have hsum :
        (∑ k ∈ Finset.range (t + 1),
          pathDensity W mu (t + 1 - 1 - k) * compressIter W mu k z) =
        ∑ k ∈ Finset.range (t + 1),
          pathDensity W mu (t - k) * compressIter W mu k z := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < t + 1 := Finset.mem_range.mp hk
      rw [show t + 1 - 1 - k = t - k by omega]
    rw [hsum]
    ring
  rw [hdeg]
  have hintegrand :
      (fun x => compressIter W mu a x *
        ∑ k ∈ Finset.range (t + 1),
          pathDensity W mu (t - k) * compressIter W mu k x) =
      fun x => ∑ k ∈ Finset.range (t + 1),
        pathDensity W mu (t - k) *
          (compressIter W mu a x * compressIter W mu k x) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hintegrand]
  have hterm : ∀ k ∈ Finset.range (t + 1), Integrable (fun x =>
      pathDensity W mu (t - k) *
        (compressIter W mu a x * compressIter W mu k x)) mu := by
    intro k hk
    exact ((good_compressIter hW a).mul
      (good_compressIter hW k)).integrable.const_mul _
  rw [integral_finsetSum (Finset.range (t + 1)) hterm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, moment hW k a]

/--
@isnad1 id=eq.1h4v.s7.8696063a651f from=translated src=- shape=3c6e0d53 vocab=a4d3aabd
-/
theorem trace_compPow_eq_pathDensity_add_centeredTrace_add_atoms
    (hW : IsGraphon W mu) (n : Nat) :
    trace mu (compPow mu W n) =
      pathDensity W mu (n + 1) +
        trace mu (compPow mu (centeredKernel W mu) n) +
          ∑ t ∈ Finset.range n,
            ∫ x, compressIter W mu (n - 1 - t) x *
              degCentered (compPow mu W t) mu x ∂mu := by
  have hGW : GoodK W := goodK_of_isGraphon hW
  have hK : GoodK (compPow mu W n) := goodK_compPow (μ := mu) hGW n
  have hA : GoodK (centeredKernel W mu) :=
    centeredKernel_goodK_of_goodK (mu := mu) hGW
  have hPowA : GoodK (compPow mu (centeredKernel W mu) n) :=
    goodK_compPow (μ := mu) hA n
  have hterm : ∀ t ∈ Finset.range n, Integrable (fun x =>
      compressIter W mu (n - 1 - t) x *
        degCentered (compPow mu W t) mu x) mu := by
    intro t ht
    exact ((good_compressIter hW (n - 1 - t)).mul
      (good_degCentered_of_goodK (mu := mu)
        (goodK_compPow (μ := mu) hGW t))).integrable
  have hsum : Integrable (fun x => ∑ t ∈ Finset.range n,
      compressIter W mu (n - 1 - t) x *
        degCentered (compPow mu W t) mu x) mu :=
    integrable_finsetSum (Finset.range n) hterm
  have htrace := congrArg (trace mu)
    (centeredKernel_compPow_expansion (mu := mu) hW n)
  unfold trace at htrace
  rw [integral_add hPowA.diag_integrable hsum,
    integral_finsetSum (Finset.range n) hterm] at htrace
  have htrace' : trace mu (centeredKernel (compPow mu W n) mu) =
      trace mu (compPow mu (centeredKernel W mu) n) +
        ∑ t ∈ Finset.range n,
          ∫ x, compressIter W mu (n - 1 - t) x *
            degCentered (compPow mu W t) mu x ∂mu := by
    unfold trace
    exact htrace
  calc
    trace mu (compPow mu W n) =
        edgeDensity (compPow mu W n) mu +
          trace mu (centeredKernel (compPow mu W n) mu) :=
      trace_eq_edgeDensity_add_centeredTrace hK
    _ = pathDensity W mu (n + 1) +
          trace mu (compPow mu (centeredKernel W mu) n) +
            ∑ t ∈ Finset.range n,
              ∫ x, compressIter W mu (n - 1 - t) x *
                degCentered (compPow mu W t) mu x ∂mu := by
      rw [edgeDensity_compPow_eq_pathDensity hW n, htrace']
      ring

/--
@isnad1 id=eq.0h3v.s7.fba3971a68af from=translated src=- shape=7c768059 vocab=7f068e31
-/
lemma coeff_mk_mul_mk (s x : Nat → Real) (n : Nat) :
    PowerSeries.coeff n (PowerSeries.mk s * PowerSeries.mk x) =
      ∑ i ∈ Finset.range (n + 1), s i * x (n - i) := by
  rw [PowerSeries.coeff_mul]
  simp_rw [PowerSeries.coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => s i * x j) n

noncomputable def graphonPrimitiveSeries (_hW : IsGraphon W mu) :
    PowerSeries Real :=
  PowerSeries.C (edgeDensity W mu) * PowerSeries.X +
    PowerSeries.X ^ 2 * PowerSeries.mk (specMoment W mu)

noncomputable def graphonPathDensitySeries (_hW : IsGraphon W mu) :
    PowerSeries Real :=
  PowerSeries.mk (pathDensity W mu)

/--
@isnad1 id=eq.0h2v.s6.b9bb45854ec4 from=translated src=- shape=d6536989 vocab=a9fc3bcc
-/
lemma sum_range_sum_range_sub (F : Nat → Real) (N : Nat) :
    (∑ t ∈ Finset.range N,
        ∑ k ∈ Finset.range (t + 1), F (t - k)) =
      ∑ r ∈ Finset.range N, ((N - r : Nat) : Real) * F r := by
  have hreflect : ∀ t : Nat,
      (∑ k ∈ Finset.range (t + 1), F (t - k)) =
        ∑ r ∈ Finset.range (t + 1), F r := by
    intro t
    simpa [show t + 1 - 1 = t by omega] using
      (Finset.sum_range_reflect F (t + 1))
  simp_rw [hreflect]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hsum :
          (∑ r ∈ Finset.range N, ((N - r : Nat) : Real) * F r) +
              ∑ r ∈ Finset.range N, F r =
            ∑ r ∈ Finset.range N,
              ((N + 1 - r : Nat) : Real) * F r := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        have hrle : r ≤ N := Nat.le_of_lt (Finset.mem_range.mp hr)
        rw [show N + 1 - r = (N - r) + 1 by omega]
        push_cast
        ring
      calc
        (∑ r ∈ Finset.range N, ((N - r : Nat) : Real) * F r) +
              ((∑ r ∈ Finset.range N, F r) + F N) =
            ((∑ r ∈ Finset.range N, ((N - r : Nat) : Real) * F r) +
              ∑ r ∈ Finset.range N, F r) + F N := by ring
        _ =
            (∑ r ∈ Finset.range N,
              ((N + 1 - r : Nat) : Real) * F r) + F N := by rw [hsum]
        _ = (∑ r ∈ Finset.range N,
              ((N + 1 - r : Nat) : Real) * F r) +
            ((N + 1 - N : Nat) : Real) * F N := by norm_num

/--
@isnad1 id=eq.1h4v.s7.7f3fa9d4e331 from=translated src=- shape=420b6167 vocab=783af36f
-/
theorem trace_atoms_eq_weighted_moments
    (hW : IsGraphon W mu) (n : Nat) :
    (∑ t ∈ Finset.range n,
        ∫ x, compressIter W mu (n - 1 - t) x *
          degCentered (compPow mu W t) mu x ∂mu) =
      ∑ j ∈ Finset.range n,
        ((j + 1 : Nat) : Real) * specMoment W mu j *
          pathDensity W mu (n - 1 - j) := by
  simp_rw [integral_compressIter_mul_degCentered_compPow hW]
  let F : Nat → Real := fun r =>
    pathDensity W mu r * specMoment W mu (n - 1 - r)
  have hreindex :
      (∑ t ∈ Finset.range n,
          ∑ k ∈ Finset.range (t + 1),
            pathDensity W mu (t - k) *
              specMoment W mu (n - 1 - t + k)) =
        ∑ t ∈ Finset.range n,
          ∑ k ∈ Finset.range (t + 1), F (t - k) := by
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro k hk
    have htlt : t < n := Finset.mem_range.mp ht
    have hkle : k ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hindex : n - 1 - t + k = n - 1 - (t - k) := by omega
    rw [hindex]
  rw [hreindex, sum_range_sum_range_sub F n]
  let G : Nat → Real := fun j =>
    ((j + 1 : Nat) : Real) * specMoment W mu j *
      pathDensity W mu (n - 1 - j)
  calc
    (∑ r ∈ Finset.range n, ((n - r : Nat) : Real) * F r) =
        ∑ r ∈ Finset.range n, G (n - 1 - r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrlt : r < n := Finset.mem_range.mp hr
          have hleft : n - 1 - r + 1 = n - r := by omega
          have hright : n - 1 - (n - 1 - r) = r := by omega
          dsimp [F, G]
          rw [hleft, hright]
          ring
    _ = ∑ j ∈ Finset.range n, G j := Finset.sum_range_reflect G n
    _ = _ := rfl

end OddCycleBound.IntermediateRegion
