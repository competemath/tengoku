import Tengoku.OddcyclegoodmanLean.OddCycleBound.Cycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

noncomputable def pairing (μ : Measure Ω) (f g : Ω → ℝ) : ℝ := ∫ x, f x * g x ∂μ

/--
@isnad1 id=good.1h4v.s5.4c51dbcc983d from=translated src=- shape=c680d783 vocab=f8c8caa4
-/
lemma good_pathIter (hU : IsGraphon U μ) : ∀ n, Good (pathIter U μ n)
  | 0 => good_one
  | (n + 1) => good_kernelOp hU (good_pathIter hU n)

def compl (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - U x y

omit [MeasurableSpace Ω] in
/--
@isnad1 id=eq.0h4v.s5.e848c2d20311 from=translated src=- shape=772f1d93 vocab=d68bed68
-/
lemma compl_eq_onesKernel_sub (x y : Ω) : compl U x y = onesKernel x y - U x y := by simp [compl, onesKernel]

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=goodk.1h3v.s4.3e10e9db8a55 from=translated src=- shape=d99ec10f vocab=4df90e4b
-/
lemma goodK_compl (hU : IsGraphon U μ) : GoodK (compl U) := by
  refine ⟨measurable_const.sub hU.meas, ⟨1, zero_le_one, fun x y => ?_⟩⟩
  rw [compl, abs_le]; constructor <;> nlinarith [hU.nonneg x y, hU.le_one x y]

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.1h5v.s5.3ac4f67171af from=translated src=- shape=12df1379 vocab=5e3d6a89
-/
lemma compl_symm (hU : IsGraphon U μ) (x y : Ω) : compl U x y = compl U y x := by
  simp only [compl, hU.symm x y]

/--
@isnad1 id=eq.1h4v.s5.88f13a82ab12 from=translated src=- shape=aad96ba7 vocab=654fe6d7
-/
lemma compPow_comm_U (hU : IsGraphon U μ) : ∀ n,
    comp μ (compPow μ U n) U = comp μ U (compPow μ U n) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show comp μ (comp μ U (compPow μ U k)) U = comp μ U (comp μ U (compPow μ U k))
      rw [comp_assoc hGU (goodK_compPow hGU k) hGU, ih]

/--
@isnad1 id=eq.1h4v.s5.6710fa7fce1d from=translated src=- shape=242eb57a vocab=fb6b93c8
-/
lemma comp_compPow_U (hU : IsGraphon U μ) (n : ℕ) :
    comp μ (compPow μ U n) U = compPow μ U (n + 1) := by
  rw [compPow_comm_U hU]; rfl

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.0h4v.s6.09b23fdd628b from=translated src=- shape=5acdc18b vocab=f5f0b608
-/
lemma trace_comp_rowBroadcast (f : Ω → ℝ) (R : Ω → Ω → ℝ) :
    trace μ (comp μ (fun x _ => f x) R) = ∫ x, f x * (∫ z, R z x ∂μ) ∂μ := by
  show ∫ x, comp μ (fun x _ => f x) R x x ∂μ = ∫ x, f x * (∫ z, R z x ∂μ) ∂μ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, f x * R z x ∂μ) = f x * ∫ z, R z x ∂μ
  rw [integral_const_mul]

private lemma abs_sub_le'' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans (le_of_eq (by rw [abs_neg]))

noncomputable def complIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (n + 1) => fun x => mean μ (complIter U μ n) - kernelOp U μ (complIter U μ n) x

/--
@isnad1 id=good.1h4v.s5.6673c32f1de9 from=translated src=- shape=c680d783 vocab=59cfa37f
-/
lemma good_complIter (hU : IsGraphon U μ) : ∀ n, Good (complIter U μ n)
  | 0 => good_one
  | (n + 1) => by
      obtain ⟨C, hC0, hC⟩ := (good_kernelOp hU (good_complIter hU n)).bdd
      refine ⟨stronglyMeasurable_const.sub (good_kernelOp hU (good_complIter hU n)).meas,
        ⟨|mean μ (complIter U μ n)| + C, by positivity, fun x => ?_⟩⟩
      show |mean μ (complIter U μ n) - kernelOp U μ (complIter U μ n) x| ≤ |mean μ (complIter U μ n)| + C
      exact (abs_sub_le'' _ _).trans (by linarith [hC x])

omit [IsProbabilityMeasure μ] in
private lemma abs_compl_le_one (hU : IsGraphon U μ) (x z : Ω) : |compl U x z| ≤ 1 := by
  rw [compl, abs_le]; constructor <;> nlinarith [hU.nonneg x z, hU.le_one x z]

/--
@isnad1 id=eq.1h4v.s6.f043cc561623 from=translated src=- shape=18ab1b31 vocab=362bd257
-/
lemma rowsum_complPow (hU : IsGraphon U μ) : ∀ n,
    (fun x => ∫ y, compPow μ (compl U) n x y ∂μ) = complIter U μ (n + 1) := by
  have hGW : GoodK (compl U) := goodK_compl hU
  intro n
  induction n with
  | zero =>
      funext x
      show ∫ y, compl U x y ∂μ = mean μ (complIter U μ 0) - kernelOp U μ (complIter U μ 0) x
      rw [show complIter U μ 0 = (fun _ => (1:ℝ)) from rfl, mean_const, kernelOp_one hU]
      simp only [compl]
      rw [integral_sub (integrable_const 1) ((goodK_of_isGraphon hU).integrable_row x)]
      have h2 : ∫ y, U x y ∂μ = degree U μ x := rfl
      rw [h2]; simp
  | succ k ih =>
      funext x
      show ∫ y, comp μ (compl U) (compPow μ (compl U) k) x y ∂μ
          = mean μ (complIter U μ (k + 1)) - kernelOp U μ (complIter U μ (k + 1)) x
      obtain ⟨Ck, _, hCk⟩ := (goodK_compPow (μ := μ) hGW k).bdd
      have hint : Integrable (Function.uncurry fun y z => compl U x z * compPow μ (compl U) k z y) (μ.prod μ) := by
        have hSM : StronglyMeasurable (Function.uncurry fun y z => compl U x z * compPow μ (compl U) k z y) := by
          have h1 : Measurable (fun p : Ω × Ω => compl U x p.2) :=
            hGW.meas.comp (measurable_const.prodMk measurable_snd)
          have h2 : Measurable (fun p : Ω × Ω => compPow μ (compl U) k p.2 p.1) :=
            (goodK_compPow (μ := μ) hGW k).meas.comp (measurable_snd.prodMk measurable_fst)
          exact (h1.mul h2).stronglyMeasurable
        refine (integrable_const (1 * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
        rintro ⟨y, z⟩
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_compl_le_one hU x z) (hCk z y) (abs_nonneg _) (by norm_num)
      calc ∫ y, comp μ (compl U) (compPow μ (compl U) k) x y ∂μ
          = ∫ y, ∫ z, compl U x z * compPow μ (compl U) k z y ∂μ ∂μ := by simp only [comp]
        _ = ∫ z, ∫ y, compl U x z * compPow μ (compl U) k z y ∂μ ∂μ := integral_integral_swap hint
        _ = ∫ z, compl U x z * (∫ y, compPow μ (compl U) k z y ∂μ) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              show ∫ y, compl U x z * compPow μ (compl U) k z y ∂μ = compl U x z * ∫ y, compPow μ (compl U) k z y ∂μ
              rw [integral_const_mul]
        _ = ∫ z, compl U x z * complIter U μ (k + 1) z ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              have ihz : ∫ y, compPow μ (compl U) k z y ∂μ = complIter U μ (k + 1) z := congrFun ih z
              show compl U x z * (∫ y, compPow μ (compl U) k z y ∂μ) = compl U x z * complIter U μ (k + 1) z
              rw [ihz]
        _ = mean μ (complIter U μ (k + 1)) - kernelOp U μ (complIter U μ (k + 1)) x := by
              simp only [compl, sub_mul, one_mul]
              rw [integral_sub (good_complIter hU (k + 1)).integrable
                (integrable_Uf hU (good_complIter hU (k + 1)) x)]
              rfl

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.2h6v.s6.f66ddecf0815 from=translated src=- shape=db6817ea vocab=a8fc2c79
-/
lemma comp_symm_swap {K L : Ω → Ω → ℝ} (hsK : ∀ x y, K x y = K y x)
    (hsL : ∀ x y, L x y = L y x) (x y : Ω) : comp μ K L y x = comp μ L K x y := by
  simp only [comp]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show K y z * L z x = L x z * K z y
  rw [hsK y z, hsL z x]; ring

/--
@isnad1 id=eq.1h4v.s5.5fa2e1a9c56f from=translated src=- shape=ae2d05d5 vocab=eb01fbc8
-/
lemma compPow_comm {K : Ω → Ω → ℝ} (hK : GoodK K) : ∀ n,
    comp μ (compPow μ K n) K = comp μ K (compPow μ K n)
  | 0 => rfl
  | (n + 1) => by
      show comp μ (comp μ K (compPow μ K n)) K = comp μ K (comp μ K (compPow μ K n))
      rw [comp_assoc hK (goodK_compPow hK n) hK, compPow_comm hK n]

/--
@isnad1 id=eq.2h6v.s6.9359236a1ca4 from=translated src=- shape=520d0a58 vocab=9c61555c
-/
lemma compPow_symm {K : Ω → Ω → ℝ} (hK : GoodK K) (hsymm : ∀ x y, K x y = K y x) :
    ∀ (n) (x y : Ω), compPow μ K n x y = compPow μ K n y x
  | 0, x, y => hsymm x y
  | (n + 1), x, y => by
      have ih : ∀ a b, compPow μ K n a b = compPow μ K n b a := fun a b => compPow_symm hK hsymm n a b
      show comp μ K (compPow μ K n) x y = comp μ K (compPow μ K n) y x
      rw [comp_symm_swap hsymm ih x y, compPow_comm hK n]

/--
@isnad1 id=eq.1h4v.s6.dcd229bc46b5 from=translated src=- shape=88d2f907 vocab=70fc3d22
-/
lemma comp_compPow_compl (hU : IsGraphon U μ) (a : ℕ) :
    comp μ (compPow μ U a) (compl U) = fun x y => pathIter U μ (a + 1) x - compPow μ U (a + 1) x y := by
  have hGU := goodK_of_isGraphon hU
  have e : comp μ (compPow μ U a) (compl U)
      = fun x y => comp μ (compPow μ U a) onesKernel x y - comp μ (compPow μ U a) U x y := by
    rw [show (compl U) = (fun x y => onesKernel x y - U x y) from by funext x y; rw [compl_eq_onesKernel_sub]]
    exact comp_sub_right (goodK_compPow hGU a) goodK_onesKernel hGU
  rw [e, comp_compPow_U hU, comp_onesKernel_right]
  funext x y
  show (∫ z, compPow μ U a x z ∂μ) - compPow μ U (a + 1) x y
      = pathIter U μ (a + 1) x - compPow μ U (a + 1) x y
  rw [congrFun (rowsum_compPow hU a) x]

/--
@isnad1 id=eq.1h4v.s6.b8276a1c5268 from=translated src=- shape=25e25db0 vocab=362bd257
-/
lemma colsum_compPow_compl (hU : IsGraphon U μ) (b : ℕ) :
    (fun x => ∫ z, compPow μ (compl U) b z x ∂μ) = complIter U μ (b + 1) := by
  have h : (fun x => ∫ z, compPow μ (compl U) b z x ∂μ)
      = (fun x => ∫ z, compPow μ (compl U) b x z ∂μ) := by
    funext x
    exact integral_congr_ae (ae_of_all _ fun z =>
      compPow_symm (goodK_compl hU) (compl_symm hU) b z x)
  rw [h, rowsum_complPow hU b]

noncomputable def mixedTrace (U : Ω → Ω → ℝ) (μ : Measure Ω) (a b : ℕ) : ℝ :=
  trace μ (comp μ (compPow μ U a) (compPow μ (compl U) b))

/--
@isnad1 id=eq.1h5v.s6.549d196d692f from=translated src=- shape=a41c5af9 vocab=963fe440
-/
lemma mixedTrace_succ (hU : IsGraphon U μ) (a b : ℕ) :
    mixedTrace U μ a (b + 1)
      = pairing μ (pathIter U μ (a + 1)) (complIter U μ (b + 1)) - mixedTrace U μ (a + 1) b := by
  have hGU := goodK_of_isGraphon hU
  have hGW := goodK_compl hU
  have hrow : GoodK (fun _x _y => pathIter U μ (a + 1) _x) :=
    goodK_rowBroadcast (good_pathIter hU (a + 1))
  show trace μ (comp μ (compPow μ U a) (compPow μ (compl U) (b + 1))) = _
  rw [show compPow μ (compl U) (b + 1) = comp μ (compl U) (compPow μ (compl U) b) from rfl,
    ← comp_assoc (goodK_compPow hGU a) hGW (goodK_compPow hGW b), comp_compPow_compl hU a,
    comp_sub_left hrow (goodK_compPow hGU (a + 1)) (goodK_compPow hGW b),
    trace_sub (goodK_comp hrow (goodK_compPow hGW b)) (goodK_comp (goodK_compPow hGU (a + 1)) (goodK_compPow hGW b)),
    trace_comp_rowBroadcast]
  show (∫ x, pathIter U μ (a + 1) x * (∫ z, compPow μ (compl U) b z x ∂μ) ∂μ) - mixedTrace U μ (a + 1) b
      = pairing μ (pathIter U μ (a + 1)) (complIter U μ (b + 1)) - mixedTrace U μ (a + 1) b
  congr 1
  show (∫ x, pathIter U μ (a + 1) x * (∫ z, compPow μ (compl U) b z x ∂μ) ∂μ)
      = ∫ x, pathIter U μ (a + 1) x * complIter U μ (b + 1) x ∂μ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show pathIter U μ (a + 1) x * (∫ z, compPow μ (compl U) b z x ∂μ)
      = pathIter U μ (a + 1) x * complIter U μ (b + 1) x
  rw [congrFun (colsum_compPow_compl hU b) x]

/--
@isnad1 id=eq.1h4v.s6.bb42827deea2 from=translated src=- shape=6f24e425 vocab=c4b26196
-/
lemma mixedTrace_zero (hU : IsGraphon U μ) (a : ℕ) :
    mixedTrace U μ a 0 = pathDensity U μ (a + 1) - trace μ (compPow μ U (a + 1)) := by
  have hGU := goodK_of_isGraphon hU
  show trace μ (comp μ (compPow μ U a) (compl U)) = _
  rw [show (compl U) = (fun x y => onesKernel x y - U x y) from by funext x y; rw [compl_eq_onesKernel_sub],
    comp_sub_right (goodK_compPow hGU a) goodK_onesKernel hGU,
    trace_sub (goodK_comp (goodK_compPow hGU a) goodK_onesKernel) (goodK_comp (goodK_compPow hGU a) hGU),
    trace_comp_onesKernel_right, doubleMean_compPow hU a, comp_compPow_U hU]

/--
@isnad1 id=eq.2h4v.s6.8638a4d24f7d from=translated src=- shape=78469f59 vocab=c62d1b5c
-/
lemma comp_compl_left (hU : IsGraphon U μ) {L : Ω → Ω → ℝ} (hL : GoodK L) :
    comp μ (compl U) L = fun x y => comp μ onesKernel L x y - comp μ U L x y := by
  have hWeq : compl U = fun x y => onesKernel x y - U x y := by funext x y; rw [compl_eq_onesKernel_sub]
  rw [hWeq]; exact comp_sub_left goodK_onesKernel (goodK_of_isGraphon hU) hL

/--
@isnad1 id=eq.1h4v.s6.ac4f6892901c from=translated src=- shape=f0e0a0a8 vocab=5b508911
-/
lemma complTrace_peel (hU : IsGraphon U μ) (m : ℕ) :
    trace μ (compPow μ (compl U) (m + 1)) = doubleMean μ (compPow μ (compl U) m) - mixedTrace U μ 0 m := by
  have hGU := goodK_of_isGraphon hU
  have hGW := goodK_compl hU
  show trace μ (comp μ (compl U) (compPow μ (compl U) m)) = _
  rw [comp_compl_left hU (goodK_compPow hGW m),
    trace_sub (goodK_comp goodK_onesKernel (goodK_compPow hGW m)) (goodK_comp hGU (goodK_compPow hGW m)),
    trace_comp_onesKernel (goodK_compPow hGW m)]
  rfl

/--
@isnad1 id=eq.1h4v.s6.7c22898544bd from=translated src=- shape=c3125c28 vocab=42a6d1af
-/
lemma doubleMean_complPow (hU : IsGraphon U μ) (n : ℕ) :
    doubleMean μ (compPow μ (compl U) n) = mean μ (complIter U μ (n + 1)) := by
  rw [doubleMean, show (fun x => ∫ y, compPow μ (compl U) n x y ∂μ) = complIter U μ (n + 1) from rowsum_complPow hU n]
  rfl

/--
@isnad1 id=eq.3h5v.s6.319bd536bed1 from=translated src=- shape=cbbd279c vocab=dc508665
-/
lemma kernelOp_selfadj (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    ∫ x, kernelOp U μ f x * g x ∂μ = ∫ x, f x * kernelOp U μ g x ∂μ := by
  have hGU := goodK_of_isGraphon hU
  obtain ⟨Cf, _, hCf⟩ := hf.bdd
  obtain ⟨Cg, _, hCg⟩ := hg.bdd
  have hint : Integrable (Function.uncurry fun x y => U x y * f y * g x) (μ.prod μ) := by
    have hSM : StronglyMeasurable (Function.uncurry fun x y => U x y * f y * g x) :=
      ((hGU.meas).mul (hf.meas.measurable.comp measurable_snd)).mul
        (hg.meas.measurable.comp measurable_fst) |>.stronglyMeasurable
    refine (integrable_const (1 * Cf * Cg)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (mul_le_mul ?_ (hCf y) (abs_nonneg _) (by norm_num)) (hCg x) (abs_nonneg _)
      (by positivity)
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y
  calc ∫ x, kernelOp U μ f x * g x ∂μ
      = ∫ x, ∫ y, U x y * f y * g x ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show kernelOp U μ f x * g x = ∫ y, U x y * f y * g x ∂μ
        rw [kernelOp, integral_mul_const]
    _ = ∫ y, ∫ x, U x y * f y * g x ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, f y * kernelOp U μ g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show (∫ x, U x y * f y * g x ∂μ) = f y * kernelOp U μ g y
        rw [kernelOp, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show U x y * f y * g x = f y * (U y x * g x)
        rw [hU.symm x y]; ring

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.1h3v.s5.2e6f417b29b8 from=translated src=- shape=754afb8c vocab=e6e74668
-/
lemma pathIter_one (hU : IsGraphon U μ) : pathIter U μ 1 = degree U μ := by
  show kernelOp U μ (fun _ => 1) = degree U μ; exact kernelOp_one hU

/--
@isnad1 id=eq.2h4v.s5.db12fc48c71f from=translated src=- shape=505c35ac vocab=61388b0f
-/
lemma mean_kernelOp_eq (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) :
    mean μ (kernelOp U μ f) = pairing μ (pathIter U μ 1) f := by
  have h1 : mean μ (kernelOp U μ f) = ∫ x, kernelOp U μ f x * 1 ∂μ := by simp [mean]
  rw [h1, kernelOp_selfadj hU hf good_one]
  simp only [pairing, pathIter_one hU]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show f x * kernelOp U μ (fun _ => 1) x = degree U μ x * f x
  rw [kernelOp_one hU]; ring

omit [IsProbabilityMeasure μ] in

/--
@isnad1 id=eq.0h4v.s5.444b52e7b213 from=translated src=- shape=684f7e9e vocab=12e14a5c
-/
lemma pairing_pathIter_zero (v : Ω → ℝ) : pairing μ (pathIter U μ 0) v = mean μ v := by
  simp only [pairing, pathIter, one_mul, mean]

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=le.1h3v.s5.9e74f8a8ad83 from=translated src=- shape=2791fd9e vocab=c84c66b6
-/
lemma edgeDensity_nonneg (hU : IsGraphon U μ) : 0 ≤ edgeDensity U μ :=
  integral_nonneg fun x => integral_nonneg fun y => hU.nonneg x y

/--
@isnad1 id=le.1h3v.s5.8c92ae0b507d from=translated src=- shape=d79d2092 vocab=30f73d90
-/
lemma edgeDensity_le_one (hU : IsGraphon U μ) : edgeDensity U μ ≤ 1 := by
  rw [edgeDensity, mean]
  calc ∫ x, degree U μ x ∂μ ≤ ∫ _x, (1:ℝ) ∂μ := by
        refine integral_mono ((goodK_of_isGraphon hU).colsum_integrable.congr
          (ae_of_all _ fun x => by rw [degree]; exact integral_congr_ae (ae_of_all _ fun y => hU.symm y x)))
          (integrable_const 1) (fun x => ?_)
        rw [degree]
        calc ∫ y, U x y ∂μ ≤ ∫ _y, (1:ℝ) ∂μ :=
              integral_mono ((goodK_of_isGraphon hU).integrable_row x) (integrable_const 1)
                (fun y => hU.le_one x y)
          _ = 1 := by simp
    _ = 1 := by simp

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=isgrapho.1h3v.s4.e89429a5c769 from=translated src=- shape=e5e0f354 vocab=5e3d6a89
-/
lemma isGraphon_compl (hU : IsGraphon U μ) : IsGraphon (compl U) μ where
  meas := by
    have h : Function.uncurry (compl U) = fun p : Ω × Ω => 1 - U p.1 p.2 := rfl
    rw [h]; exact measurable_const.sub hU.meas
  nonneg := fun x y => by rw [compl]; linarith [hU.le_one x y]
  le_one := fun x y => by rw [compl]; linarith [hU.nonneg x y]
  symm := fun x y => by rw [compl, compl, hU.symm x y]

end OddCycleBound
