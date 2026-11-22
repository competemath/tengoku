import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.Seed.Algebra.Module.ZLattice.Summable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms summable_translate_of_mem_schwartzBruhat_impl` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat

set_option autoImplicit false

open _root_.NumberField open _root_.IsDedekindDomain open _root_.NumberField.AdelicFourier open _root_.NumberField.InfiniteAdeleRing open _root_.Filter
open scoped SchwartzMap

noncomputable section

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing place RingOfIntegers mixedEmbedding mixedEmbedding.mixedSpace AdeleRing mixedEmbedding_injective mixedEmbedding.integerLattice RingOfIntegers.ext AdelicBox.integralFiniteAdeles AdelicBox.isOpen_integralFiniteAdeles)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (schwartzBruhat schwartzBruhat_induction)
open _root_.NumberField.AdelicFourier open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

private theorem exists_ringOfIntegers_of_mem_integralFiniteAdeles (k : F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F) :
    ∃ o : 𝓞 F, (o : F) = k := by
  have hk : k ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => ?_
    have hv := h v
    have heval : (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = ((k : F) : v.adicCompletion F) := rfl
    rw [heval, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  obtain ⟨o, ho⟩ := hk
  exact ⟨o, ho⟩

section LatticeSum

open scoped Classical in

/--
@isnad1 id=ex.0h3v.s10.9db811047d5b from=translated src=- shape=4fc07add vocab=74770d1c
-/
theorem exists_one_add_norm_pow_mul_norm_le (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ℕ) :
    ∃ C : ℝ, ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖g y‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl g y
  rwa [norm_iteratedFDeriv_zero] at h

open scoped Classical in

/--
@isnad1 id=summable.0h3v.s12.b8e51b620852 from=translated src=- shape=b6d2061a vocab=a44de595
-/
theorem summable_norm_apply_add_integerLattice (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (z : mixedEmbedding.mixedSpace F) :
    Summable fun l : mixedEmbedding.integerLattice F => ‖g (z + (l : mixedEmbedding.mixedSpace F))‖ := by
  set L := mixedEmbedding.integerLattice F
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_le F g (Module.finrank ℤ L + 1)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hsum : Summable fun l : L =>
      C * ‖(l : mixedEmbedding.mixedSpace F) - (-z)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _) (-z)).mul_left C
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hfin : {l : L | (l : mixedEmbedding.mixedSpace F) = -z}.Finite :=
    Set.Subsingleton.finite fun a ha b hb => Subtype.val_injective (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with l hl
  have hl' : (l : mixedEmbedding.mixedSpace F) - (-z) ≠ 0 := fun h => hl (sub_eq_zero.mp h)
  have hzl : z + (l : mixedEmbedding.mixedSpace F) = (l : mixedEmbedding.mixedSpace F) - (-z) := by
    rw [sub_neg_eq_add, add_comm]
  have hpos : 0 < ‖z + (l : mixedEmbedding.mixedSpace F)‖ := by
    rw [hzl]; exact norm_pos_iff.mpr hl'
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have h1 := hC (z + (l : mixedEmbedding.mixedSpace F))
  have h2 : 0 < (1 + ‖z + (l : mixedEmbedding.mixedSpace F)‖) ^ (Module.finrank ℤ L + 1) := by
    positivity
  calc ‖g (z + (l : mixedEmbedding.mixedSpace F))‖
        ≤ C / (1 + ‖z + (l : mixedEmbedding.mixedSpace F)‖) ^ (Module.finrank ℤ L + 1) := by
          rw [le_div_iff₀ h2, mul_comm]; exact h1
    _ ≤ C / ‖z + (l : mixedEmbedding.mixedSpace F)‖ ^ (Module.finrank ℤ L + 1) :=
          div_le_div_of_nonneg_left hC0 (pow_pos hpos _)
            (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _)
    _ = C * ‖(l : mixedEmbedding.mixedSpace F) - (-z)‖⁻¹ ^ (Module.finrank ℤ L + 1) := by
          rw [hzl, div_eq_mul_inv, inv_pow]

def toIntegerLattice (o : 𝓞 F) : mixedEmbedding.integerLattice F :=
  ⟨mixedEmbedding F (o : F), LinearMap.mem_range.mpr ⟨o, rfl⟩⟩

omit [NumberField F] in
/--
@isnad1 id=eq.0h2v.s9.fd8b58ee7149 from=translated src=- shape=0912eb97 vocab=4babccf5
-/
theorem coe_toIntegerLattice (o : 𝓞 F) :
    (toIntegerLattice F o : mixedEmbedding.mixedSpace F) = mixedEmbedding F (o : F) := rfl

/--
@isnad1 id=injectiv.0h1v.s9.db36e7c34a0c from=translated src=- shape=313b0f7a vocab=e36b1b1a
-/
theorem toIntegerLattice_injective : Function.Injective (toIntegerLattice F) := by
  intro a b h
  have h' : mixedEmbedding F (a : F) = mixedEmbedding F (b : F) := congrArg Subtype.val h
  exact RingOfIntegers.ext ((mixedEmbedding_injective F) h')

open scoped Classical in

/--
@isnad1 id=summable.0h3v.s11.7c0bf6619b5b from=translated src=- shape=4683e823 vocab=27ec9667
-/
theorem summable_norm_apply_add_mixedEmbedding (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (z : mixedEmbedding.mixedSpace F) :
    Summable fun o : 𝓞 F => ‖g (z + mixedEmbedding F (o : F))‖ := by
  have h : Summable ((fun l : mixedEmbedding.integerLattice F =>
      ‖g (z + (l : mixedEmbedding.mixedSpace F))‖) ∘ toIntegerLattice F) :=
    (summable_norm_apply_add_integerLattice F g z).comp_injective (toIntegerLattice_injective F)
  simpa only [Function.comp_def, coe_toIntegerLattice] using h

end LatticeSum

section PureTensor

variable {F}

/--
@isnad1 id=mem.0h1v.s7.139e47b6fa83 from=translated src=- shape=62dc9b7e vocab=9b03104f
-/
theorem zero_mem_integralFiniteAdeles' :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F :=
  fun v => (v.adicCompletionIntegers F).zero_mem

/--
@isnad1 id=mem.2h3v.s8.052a193a4c55 from=translated src=- shape=e4d16b89 vocab=523a7a7c
-/
theorem sub_mem_integralFiniteAdeles {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F) (hb : b ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F) :
    a - b ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F :=
  fun v => by have h__af := (v.adicCompletionIntegers F).sub_mem (ha v) (hb v); simp at h__af; exact h__af

variable (F)

open scoped Classical in

/--
@isnad1 id=summable.2h4v.s11.01e16ff63672 from=translated src=- shape=b028a730 vocab=21ba8ba2
-/
theorem summable_translate_pureTensor (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) (x : 𝔸) :
    Summable fun ξ : F => g (ringEquiv_mixedSpace F (x + ι ξ).1) * h (x + ι ξ).2 := by
  set U := AdelicBox.integralFiniteAdeles (𝓞 F) F with hUdef
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hlc.continuous

  have h1 : ∀ ξ : F, ringEquiv_mixedSpace F (x + ι ξ).1
      = ringEquiv_mixedSpace F x.1 + mixedEmbedding F ξ := fun ξ => by
    rw [mixedEmbedding_eq_algebraMap_comp, ← map_add]; rfl
  have h2 : ∀ ξ : F, (x + ι ξ).2 = x.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := fun ξ => rfl
  simp_rw [h1, h2]
  set c := ringEquiv_mixedSpace F x.1 with hcdef
  set ιf := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hιfdef

  have hTo : ∀ y : FiniteAdeleRing (𝓞 F) F, IsOpen {w : FiniteAdeleRing (𝓞 F) F | w - y ∈ U} :=
    fun y => (AdelicBox.isOpen_integralFiniteAdeles F).preimage (continuous_sub_right y)
  obtain ⟨t, ht⟩ := (hcs : IsCompact (tsupport h)).elim_finite_subcover
    (fun y => {w : FiniteAdeleRing (𝓞 F) F | w - y ∈ U}) hTo
    (fun w _ => Set.mem_iUnion.mpr ⟨w, by
      show w - w ∈ U
      rw [sub_self]; exact zero_mem_integralFiniteAdeles'⟩)

  let S : FiniteAdeleRing (𝓞 F) F → Set F := fun y => {ξ | x.2 + ιf ξ - y ∈ U}
  let ξ0 : FiniteAdeleRing (𝓞 F) F → F := fun y => if hy : (S y).Nonempty then hy.some else 0
  have hcoset : ∀ y, ∀ ξ ∈ S y, ∃ o : 𝓞 F, ξ = ξ0 y + o := by
    intro y ξ hξ
    have hne : (S y).Nonempty := ⟨ξ, hξ⟩
    have hξ0 : ξ0 y ∈ S y := by
      show (if hy : (S y).Nonempty then hy.some else 0) ∈ S y
      rw [dite_eq_left hne]; exact hne.some_mem
    have hdiff : ιf (ξ - ξ0 y) ∈ U := by
      have hsub := sub_mem_integralFiniteAdeles hξ hξ0
      have heq : x.2 + ιf ξ - y - (x.2 + ιf (ξ0 y) - y) = ιf (ξ - ξ0 y) := by
        rw [map_sub]; abel
      rwa [heq] at hsub
    obtain ⟨o, ho⟩ := exists_ringOfIntegers_of_mem_integralFiniteAdeles F (ξ - ξ0 y) hdiff
    refine ⟨o, ?_⟩
    rw [ho]; abel

  let G : F → ℝ := fun ξ => ‖g (c + mixedEmbedding F ξ)‖
  have hGsum : ∀ y, Summable ((S y).indicator G) := by
    intro y
    have hφ : Function.Injective fun o : 𝓞 F => ξ0 y + (o : F) := fun a b hab =>
      RingOfIntegers.ext (add_left_cancel hab)
    refine (hφ.summable_iff ?_).mp ?_
    · intro ξ hξ
      apply Set.indicator_of_notMem
      intro hS
      obtain ⟨o, rfl⟩ := hcoset y ξ hS
      exact hξ ⟨o, rfl⟩
    · have hS' := summable_norm_apply_add_mixedEmbedding F g (c + mixedEmbedding F (ξ0 y))
      refine Summable.of_nonneg_of_le (fun o => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
        (fun o => ?_) hS'
      refine (Set.indicator_le_self' (fun _ _ => norm_nonneg _) _).trans (le_of_eq ?_)
      show ‖g (c + mixedEmbedding F (ξ0 y + (o : F)))‖ = ‖g (c + mixedEmbedding F (ξ0 y) + mixedEmbedding F (o : F))‖
      rw [map_add (mixedEmbedding F), add_assoc]

  have hdom : ∀ ξ : F, ‖g (c + mixedEmbedding F ξ) * h (x.2 + ιf ξ)‖
      ≤ max B 0 * ∑ y ∈ t, (S y).indicator G ξ := by
    intro ξ
    by_cases hz : h (x.2 + ιf ξ) = 0
    · rw [hz, mul_zero, norm_zero]
      exact mul_nonneg (le_max_right _ _)
        (Finset.sum_nonneg fun y _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
    · have hmem : x.2 + ιf ξ ∈ tsupport h := subset_tsupport _ hz
      obtain ⟨y, hy, hyU⟩ : ∃ y ∈ t, x.2 + ιf ξ - y ∈ U := by
        have := ht hmem
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at this
        obtain ⟨y, hy, hyU⟩ := this
        exact ⟨y, hy, hyU⟩
      have hξS : ξ ∈ S y := hyU
      calc ‖g (c + mixedEmbedding F ξ) * h (x.2 + ιf ξ)‖
            = ‖g (c + mixedEmbedding F ξ)‖ * ‖h (x.2 + ιf ξ)‖ := norm_mul _ _
        _ ≤ G ξ * max B 0 :=
              mul_le_mul_of_nonneg_left ((hB _).trans (le_max_left _ _)) (norm_nonneg _)
        _ = max B 0 * (S y).indicator G ξ := by rw [mul_comm, Set.indicator_of_mem hξS]
        _ ≤ max B 0 * ∑ y' ∈ t, (S y').indicator G ξ :=
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (f := fun y' => (S y').indicator G ξ)
                  (fun y' _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _) hy)
                (le_max_right _ _)
  exact Summable.of_norm_bounded_eventually
    ((summable_sum fun y _ => hGsum y).mul_left (max B 0)) (Eventually.of_forall hdom)

end PureTensor

/--
@isnad1 id=summable.1h3v.s9.89efccb59000 from=translated src=- shape=163671b5 vocab=0cd31b5b
-/
theorem summable_translate_of_mem_schwartzBruhat_impl {f : 𝔸 → ℂ} (hf : f ∈ schwartzBruhat F) (x : 𝔸) :
    Summable fun ξ : F => f (x + ι ξ) := by
  revert x
  refine schwartzBruhat_induction (p := fun f _ => ∀ x : 𝔸, Summable fun ξ : F => f (x + ι ξ))
    ?_ ?_ ?_ ?_ hf
  · rintro f ⟨g, h, hlc, hcs, rfl⟩ x
    exact summable_translate_pureTensor F g h hlc hcs x
  · intro x
    exact summable_zero
  · intro f g _ _ hf hg x
    simpa [Pi.add_apply] using (hf x).add (hg x)
  · intro c f _ hf x
    simpa [Pi.smul_apply, smul_eq_mul] using (hf x).mul_left c

end NumberField.AdelicFourier

end

open _root_.NumberField open _root_.P2MW.S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat.NumberField open _root_.NumberField.AdelicFourier open _root_.P2MW.S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat.NumberField.AdelicFourier

/--
@isnad1 id=summable.1h3v.s9.89efccb59000 from=translated src=- shape=163671b5 vocab=0cd31b5b
-/
theorem solution (F : Type) [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    Summable fun ξ : F => f (x + algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  exact NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat_impl F hf x
