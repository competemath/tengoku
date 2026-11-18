import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp

set_option autoImplicit false

open MeasureTheory TopologicalSpace Set Filter Topology Complex

noncomputable section

namespace PoissonPiSol

variable {d : Type*} [Fintype d]

def ιZ (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

/--
@isnad1 id=eq.0h3v.s4.01df2b4062d7 from=translated src=- shape=b084d0d7 vocab=ff3cee3d
-/
@[scoped simp] lemma ιZ_apply (n : d → ℤ) (i : d) : ιZ n i = (n i : ℝ) := rfl

/--
@isnad1 id=eq.0h3v.s6.b4a595573e70 from=translated src=- shape=488f121e vocab=532114cb
-/
lemma ιZ_add (m n : d → ℤ) : ιZ (m + n) = ιZ m + ιZ n := by
  funext i; simp [ιZ]

def proj (y : d → ℝ) : UnitAddTorus d := fun i => ((y i : ℝ) : UnitAddCircle)

/--
@isnad1 id=eq.0h1v.s5.1205f44cf96a from=translated src=- shape=dfc4e370 vocab=89500304
-/
lemma proj_eq_piMap : (proj : (d → ℝ) → UnitAddTorus d) =
    Pi.map (fun _ : d => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) := rfl

/--
@isnad1 id=isquotie.0h1v.s5.ebf0248d2263 from=translated src=- shape=ea26f425 vocab=d4b05a7f
-/
lemma isQuotientMap_proj : IsQuotientMap (proj : (d → ℝ) → UnitAddTorus d) := by
  rw [proj_eq_piMap]
  exact (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

def ech (m : d → ℤ) (y : d → ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * y i : ℝ) : ℂ))

def echN (m : d → ℤ) (y : d → ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * y i : ℝ) : ℂ)))

/--
@isnad1 id=eq.0h3v.s4.587ce56cac53 from=translated src=- shape=0bf20fa7 vocab=392f3c39
-/
lemma norm_echN (m : d → ℤ) (y : d → ℝ) : ‖echN m y‖ = 1 := by
  unfold echN
  have : -(2 * Real.pi * Complex.I * (((∑ i, (m i : ℝ) * y i : ℝ)) : ℂ)) =
      ((-(2 * Real.pi * (∑ i, (m i : ℝ) * y i)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/--
@isnad1 id=continuo.0h2v.s5.667175d922e0 from=translated src=- shape=09c6cce6 vocab=63bb93e0
-/
lemma continuous_echN (m : d → ℤ) : Continuous (echN m : (d → ℝ) → ℂ) := by
  unfold echN; fun_prop

/--
@isnad1 id=eq.0h4v.s5.dba487cb05ac from=translated src=- shape=8249715a vocab=7642e978
-/
lemma echN_add_ιZ (m n : d → ℤ) (y : d → ℝ) : echN m (y + ιZ n) = echN m y := by
  unfold echN
  have hsum : (∑ i, (m i : ℝ) * (y + ιZ n) i) = (∑ i, (m i : ℝ) * y i) + ((∑ i, m i * n i : ℤ) : ℝ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ιZ, mul_add]
  rw [hsum]
  have h2 : -(2 * (Real.pi : ℂ) * Complex.I * (((∑ i, (m i : ℝ) * y i) + ((∑ i, m i * n i : ℤ) : ℝ) : ℝ) : ℂ)) =
      -(2 * (Real.pi : ℂ) * Complex.I * (((∑ i, (m i : ℝ) * y i : ℝ)) : ℂ)) +
        ((-(∑ i, m i * n i) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/--
@isnad1 id=eq.0h3v.s6.43624eb256fb from=translated src=- shape=6a58ac66 vocab=27b47fe3
-/
lemma mFourier_proj (m : d → ℤ) (y : d → ℝ) : UnitAddTorus.mFourier m (proj y) = ech m y := by
  simp only [UnitAddTorus.mFourier, proj, ContinuousMap.coe_mk, fourier_coe_apply, ech]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/--
@isnad1 id=eq.0h3v.s7.df884ec0ea0d from=translated src=- shape=9ade19ff vocab=65c89acc
-/
lemma mFourier_neg_proj (m : d → ℤ) (y : d → ℝ) : UnitAddTorus.mFourier (-m) (proj y) = echN m y := by
  rw [mFourier_proj]
  unfold ech echN
  congr 1
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

def cubeI (n : d → ℤ) : Set (d → ℝ) := {y | ∀ i, y i ∈ Ioc (n i : ℝ) (n i + 1)}

/--
@isnad1 id=eq.0h2v.s5.3449f057dfa5 from=translated src=- shape=6d95f9d2 vocab=15f9e846
-/
lemma cubeI_eq_pi (n : d → ℤ) : cubeI n = Set.pi Set.univ (fun i => Ioc (n i : ℝ) (n i + 1)) := by
  ext y; simp [cubeI]

/--
@isnad1 id=iff.0h3v.s5.98fd180f8a5b from=translated src=- shape=95e0daba vocab=79179560
-/
lemma mem_cubeI_iff (n : d → ℤ) (y : d → ℝ) : y ∈ cubeI n ↔ ∀ i, ⌈y i⌉ = n i + 1 := by
  simp only [cubeI, mem_ofPred_eq, mem_Ioc, Int.ceil_eq_iff]
  refine forall_congr' fun i => ?_
  push_cast
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/--
@isnad1 id=measurab.0h2v.s4.8a1a064e7f1c from=translated src=- shape=e6b9a5b7 vocab=61289b84
-/
lemma measurableSet_cubeI (n : d → ℤ) : MeasurableSet (cubeI n) := by
  rw [cubeI_eq_pi]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/--
@isnad1 id=pairwise.0h1v.s6.f6410bf0dbef from=translated src=- shape=75ef16c1 vocab=955aa022
-/
lemma pairwise_disjoint_cubeI : Pairwise (Function.onFun Disjoint (cubeI (d := d))) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro w hw hw'
  apply hkk'
  funext i
  have h1 := (mem_cubeI_iff k w).1 hw i
  have h2 := (mem_cubeI_iff k' w).1 hw' i
  omega

/--
@isnad1 id=eq.0h1v.s4.e32aa60bd76a from=translated src=- shape=87a0a88c vocab=3cff5d1d
-/
lemma iUnion_cubeI : (⋃ n : d → ℤ, cubeI n) = Set.univ := by
  refine Set.eq_univ_of_forall fun w => Set.mem_iUnion.2 ⟨fun i => ⌈w i⌉ - 1, ?_⟩
  rw [mem_cubeI_iff]; intro i; ring

/--
@isnad1 id=eq.0h2v.s6.659232e08946 from=translated src=- shape=83f60e71 vocab=f12d2781
-/
lemma volume_cubeI (n : d → ℤ) : volume (cubeI n) = 1 := by
  rw [cubeI_eq_pi, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioc]

/--
@isnad1 id=eq.0h2v.s6.4237de62c546 from=translated src=- shape=1b8ce8d7 vocab=76adeedd
-/
lemma preimage_cubeI (n : d → ℤ) : (fun y : d → ℝ => y + ιZ n) ⁻¹' cubeI n = cubeI 0 := by
  ext y
  simp only [mem_preimage, cubeI, mem_ofPred_eq, Pi.add_apply, ιZ_apply, mem_Ioc, Pi.zero_apply, Int.cast_zero,
    zero_add]
  refine forall_congr' fun i => ?_
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/--
@isnad1 id=eq.2h3v.s9.a4afad907f17 from=translated src=- shape=ea49578c vocab=ffeb8e79
-/
theorem main (f : C(d → ℝ, ℂ))
    (h_norm : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖)
    (h_sum : Summable fun n : d → ℤ => ∫ y : d → ℝ, echN n y * f y)
    (x : d → ℝ) :
    ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) = ∑' n : d → ℤ, (∫ y : d → ℝ, echN n y * f y) * ech n x := by
  classical

  set T : (d → ℤ) → C(d → ℝ, ℂ) := fun n => f.comp (ContinuousMap.addRight (ιZ n)) with hT
  have hTs : Summable T := ContinuousMap.summable_of_locally_summable_norm h_norm
  set F₀ : C(d → ℝ, ℂ) := ∑' n, T n with hF₀
  have hF₀_apply : ∀ y, F₀ y = ∑' n, f (y + ιZ n) := fun y => by
    rw [hF₀, ← ContinuousMap.tsum_apply hTs]; rfl
  have hF₀_per : ∀ (y : d → ℝ) (n : d → ℤ), F₀ (y + ιZ n) = F₀ y := by
    intro y n
    rw [hF₀_apply, hF₀_apply]
    conv_rhs => rw [← Equiv.tsum_eq (Equiv.addRight n)]
    refine tsum_congr fun c => ?_
    simp only [Equiv.coe_addRight, ιZ_add]
    rw [add_assoc, add_comm (ιZ n)]

  set sec : UnitAddTorus d → (d → ℝ) := fun t i => ((AddCircle.equivIoc 1 0 (t i)) : ℝ) with hsecdef
  have hsec : ∀ t, proj (sec t) = t := fun t => funext fun i => AddCircle.coe_equivIoc
  have hsecπ : ∀ y : d → ℝ, ∃ n : d → ℤ, sec (proj y) = y + ιZ n := by
    intro y
    have hex : ∀ i, ∃ k : ℤ, sec (proj y) i = y i + k := fun i => by
      have hi := congr_fun (hsec (proj y)) i
      simp only [proj] at hi
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at hi
      obtain ⟨k, hk⟩ := hi
      refine ⟨k, ?_⟩
      have : (k : ℝ) = sec (proj y) i - y i := by simpa using hk
      linarith
    choose n hn using hex
    exact ⟨n, funext fun i => by simp [hn]⟩
  set G : UnitAddTorus d → ℂ := fun t => F₀ (sec t) with hGdef
  have hGπ : ∀ y, G (proj y) = F₀ y := fun y => by
    obtain ⟨n, hn⟩ := hsecπ y
    show F₀ (sec (proj y)) = F₀ y
    rw [hn, hF₀_per]
  have hGcont : Continuous G := by
    refine isQuotientMap_proj.continuous_iff.2 ?_
    have : G ∘ proj = (F₀ : (d → ℝ) → ℂ) := funext hGπ
    rw [this]; exact F₀.continuous
  set Gc : C(UnitAddTorus d, ℂ) := ⟨G, hGcont⟩ with hGc

  set K : Compacts (d → ℝ) := ⟨Set.pi Set.univ (fun _ : d => Icc (0 : ℝ) 1), isCompact_univ_pi fun _ => isCompact_Icc⟩
    with hK
  have hC0K : cubeI (0 : d → ℤ) ⊆ (K : Set (d → ℝ)) := by
    intro y hy
    simp only [hK, Compacts.coe_mk, mem_univ_pi, mem_Icc]
    intro i
    have := hy i
    simp only [Pi.zero_apply, Int.cast_zero, zero_add, mem_Ioc] at this
    exact ⟨this.1.le, this.2⟩
  have hT_apply : ∀ (n : d → ℤ) (z : d → ℝ), T n z = f (z + ιZ n) := fun n z => rfl

  have hbound0 : ∀ (m n : d → ℤ) (y : d → ℝ), y ∈ cubeI 0 → ‖echN m y * f (y + ιZ n)‖ ≤ ‖(T n).restrict K‖ := by
    intro m n y hy
    rw [norm_mul, norm_echN, one_mul]
    have : f (y + ιZ n) = (T n).restrict K ⟨y, hC0K hy⟩ := rfl
    rw [this]; exact ContinuousMap.norm_coe_le_norm _ _
  have hboundn : ∀ (m n : d → ℤ) (y : d → ℝ), y ∈ cubeI n → ‖echN m y * f y‖ ≤ ‖(T n).restrict K‖ := by
    intro m n y hy
    have hy0 : y - ιZ n ∈ cubeI 0 := by
      rw [← preimage_cubeI n, mem_preimage, sub_add_cancel]; exact hy
    have := hbound0 m n (y - ιZ n) hy0
    rwa [sub_add_cancel, norm_mul, norm_echN, one_mul, ← one_mul ‖f y‖, ← norm_echN m y, ← norm_mul] at this
  have hvol : ∀ n : d → ℤ, volume (cubeI n) < ⊤ := fun n => by rw [volume_cubeI]; exact ENNReal.one_lt_top
  have hcont0 : ∀ m n : d → ℤ, Continuous (fun y : d → ℝ => echN m y * f (y + ιZ n)) := fun m n =>
    (continuous_echN m).mul (f.continuous.comp (continuous_id.add continuous_const))
  have hcontn : ∀ m : d → ℤ, Continuous (fun y : d → ℝ => echN m y * f y) := fun m =>
    (continuous_echN m).mul f.continuous
  have hint0 : ∀ m n : d → ℤ, IntegrableOn (fun y => echN m y * f (y + ιZ n)) (cubeI 0) := fun m n =>
    Measure.integrableOn_of_bounded (hvol 0).ne (hcont0 m n).aestronglyMeasurable
      ((ae_restrict_iff' (measurableSet_cubeI 0)).2 (Filter.Eventually.of_forall (hbound0 m n)))
  have hintn : ∀ m n : d → ℤ, IntegrableOn (fun y => echN m y * f y) (cubeI n) := fun m n =>
    Measure.integrableOn_of_bounded (hvol n).ne (hcontn m).aestronglyMeasurable
      ((ae_restrict_iff' (measurableSet_cubeI n)).2 (Filter.Eventually.of_forall (hboundn m n)))
  have hnorm0 : ∀ m n : d → ℤ, ∫ y in cubeI 0, ‖echN m y * f (y + ιZ n)‖ ≤ ‖(T n).restrict K‖ := by
    intro m n
    calc ∫ y in cubeI 0, ‖echN m y * f (y + ιZ n)‖ ≤ ∫ y in cubeI (0 : d → ℤ), ‖(T n).restrict K‖ :=
          setIntegral_mono_on (hint0 m n).norm (integrableOn_const (hvol 0).ne) (measurableSet_cubeI 0)
            (hbound0 m n)
      _ = ‖(T n).restrict K‖ := by rw [setIntegral_const]; simp [measureReal_def, volume_cubeI]
  have hnormn : ∀ m n : d → ℤ, ∫ y in cubeI n, ‖echN m y * f y‖ ≤ ‖(T n).restrict K‖ := by
    intro m n
    calc ∫ y in cubeI n, ‖echN m y * f y‖ ≤ ∫ y in cubeI n, ‖(T n).restrict K‖ :=
          setIntegral_mono_on (hintn m n).norm (integrableOn_const (hvol n).ne) (measurableSet_cubeI n)
            (hboundn m n)
      _ = ‖(T n).restrict K‖ := by rw [setIntegral_const]; simp [measureReal_def, volume_cubeI]
  have hKsum : Summable fun n : d → ℤ => ‖(T n).restrict K‖ := h_norm K
  have hsum0 : ∀ m : d → ℤ, Summable fun n : d → ℤ => ∫ y in cubeI 0, ‖echN m y * f (y + ιZ n)‖ := fun m =>
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (hnorm0 m) hKsum
  have hsumn : ∀ m : d → ℤ, Summable fun n : d → ℤ => ∫ y in cubeI n, ‖echN m y * f y‖ := fun m =>
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (hnormn m) hKsum

  have hshift : ∀ m n : d → ℤ, ∫ y in cubeI 0, echN m y * f (y + ιZ n) = ∫ y in cubeI n, echN m y * f y := by
    intro m n
    have h := (measurePreserving_add_right (volume : Measure (d → ℝ)) (ιZ n)).setIntegral_preimage_emb
      (measurableEmbedding_addRight (ιZ n)) (fun y => echN m y * f y) (cubeI n)
    rw [preimage_cubeI] at h
    rw [← h]
    refine setIntegral_congr_fun (measurableSet_cubeI 0) fun y _ => ?_
    rw [echN_add_ιZ]

  have hcoef_int : ∀ m : d → ℤ, Integrable (fun y : d → ℝ => echN m y * f y) := by
    intro m
    have h := integrableOn_iUnion_of_summable_integral_norm (hintn m) (hsumn m)
    rw [iUnion_cubeI] at h
    exact integrableOn_univ.1 h
  have hdecomp : ∀ m : d → ℤ, HasSum (fun n : d → ℤ => ∫ y in cubeI n, echN m y * f y) (∫ y, echN m y * f y) := by
    intro m
    have hIU : IntegrableOn (fun y : d → ℝ => echN m y * f y) (⋃ n : d → ℤ, cubeI n) := by
      rw [iUnion_cubeI]; exact (hcoef_int m).integrableOn
    have := hasSum_integral_iUnion measurableSet_cubeI pairwise_disjoint_cubeI hIU
    rwa [iUnion_cubeI, setIntegral_univ] at this

  have hset : {y : d → ℝ | ∀ i, y i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} = cubeI 0 := by
    ext y; simp [cubeI]
  have hcoef : ∀ m : d → ℤ, UnitAddTorus.mFourierCoeff Gc m = ∫ y : d → ℝ, echN m y * f y := by
    intro m
    calc UnitAddTorus.mFourierCoeff Gc m
        = ∫ y in cubeI 0, UnitAddTorus.mFourier (-m) (proj y) • Gc (proj y) := by
          rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0, hset]
          rfl
      _ = ∫ y in cubeI 0, ∑' n : d → ℤ, echN m y * f (y + ιZ n) := by
          refine setIntegral_congr_fun (measurableSet_cubeI 0) fun y _ => ?_
          rw [mFourier_neg_proj, smul_eq_mul]
          show echN m y * G (proj y) = _
          rw [hGπ, hF₀_apply, ← tsum_mul_left]
      _ = ∑' n : d → ℤ, ∫ y in cubeI 0, echN m y * f (y + ιZ n) :=
          (integral_tsum_of_summable_integral_norm (hint0 m) (hsum0 m)).symm
      _ = ∑' n : d → ℤ, ∫ y in cubeI n, echN m y * f y := tsum_congr (hshift m)
      _ = ∫ y, echN m y * f y := (hdecomp m).tsum_eq

  have hsumm : Summable (UnitAddTorus.mFourierCoeff Gc) := by
    rw [show UnitAddTorus.mFourierCoeff Gc = fun n => ∫ y : d → ℝ, echN n y * f y from funext hcoef]
    exact h_sum
  have hS := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumm (proj x)
  have hGx : Gc (proj x) = ∑' n : d → ℤ, f (x + ιZ n) := by
    show G (proj x) = _
    rw [hGπ, hF₀_apply]
  rw [hGx] at hS
  simp only [hcoef, mFourier_proj, smul_eq_mul] at hS
  exact hS.tsum_eq.symm

end PoissonPiSol
open scoped _root_.P2MW.S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp.PoissonPiSol

end
open scoped _root_.P2MW.S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp.PoissonPiSol

open PoissonPiSol in
/--
@isnad1 id=eq.2h3v.s10.efaac8a1c780 from=translated src=- shape=51aa7c0f vocab=21261e72
-/
theorem solution
    {d : Type*} [Fintype d] (f : C(d → ℝ, ℂ))
    (h_norm : ∀ K : TopologicalSpace.Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖)
    (h_sum : Summable fun n : d → ℤ =>
      ∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y)
    (x : d → ℝ) :
    ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) =
      ∑' n : d → ℤ, (∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ)) :=
  PoissonPiSol.main f h_norm h_sum x
