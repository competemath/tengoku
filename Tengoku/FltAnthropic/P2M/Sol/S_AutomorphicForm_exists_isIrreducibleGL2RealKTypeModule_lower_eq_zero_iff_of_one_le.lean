import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2RealKTypeModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le

set_option autoImplicit false

open _root_.AutomorphicForm

namespace AutomorphicForm
export _root_.AutomorphicForm (IsGL2RealKTypeModule IsIrreducibleGL2RealKTypeModule)
namespace GL2RealDiscreteSeriesModel
open _root_.AutomorphicForm

variable (k : ℤ)

abbrev J := ℕ ⊕ ℕ

noncomputable def b (i : J) : J →₀ ℂ := Finsupp.single i 1

/--
@isnad1 id=eq.0h2v.s6.f08259d7df84 from=translated src=- shape=b9da20e4 vocab=304ee062
-/
theorem single_eq_smul_b (i : J) (c : ℂ) : Finsupp.single i c = c • b i := by
  rw [b, Finsupp.smul_single', mul_one]

/--
@isnad1 id=ne.0h1v.s4.42f5cd730f10 from=translated src=- shape=4f1d8603 vocab=e8bd7719
-/
theorem b_ne_zero (i : J) : b i ≠ 0 :=
  Finsupp.single_ne_zero.mpr one_ne_zero

/--
@isnad1 id=eq.0h2v.s5.ec446afc58f4 from=translated src=- shape=24fcae48 vocab=f24eb1d1
-/
theorem b_apply (i i' : J) : b i i' = if i = i' then 1 else 0 := by
  rw [b, Finsupp.single_apply]

noncomputable def Efun : J → (J →₀ ℂ)
  | Sum.inl j => ((k : ℂ) + j) • b (Sum.inl (j + 1))
  | Sum.inr 0 => 0
  | Sum.inr (j + 1) => (-((j + 1 : ℕ) : ℂ)) • b (Sum.inr j)

noncomputable def Lfun : J → (J →₀ ℂ)
  | Sum.inl 0 => 0
  | Sum.inl (j + 1) => (-((j + 1 : ℕ) : ℂ)) • b (Sum.inl j)
  | Sum.inr j => ((k : ℂ) + j) • b (Sum.inr (j + 1))

noncomputable def εfun : J → (J →₀ ℂ)
  | Sum.inl j => b (Sum.inr j)
  | Sum.inr j => b (Sum.inl j)

noncomputable def E : (J →₀ ℂ) →ₗ[ℂ] (J →₀ ℂ) :=
  Finsupp.lsum ℂ fun i : J => LinearMap.toSpanSingleton ℂ _ (Efun k i)

noncomputable def L : (J →₀ ℂ) →ₗ[ℂ] (J →₀ ℂ) :=
  Finsupp.lsum ℂ fun i : J => LinearMap.toSpanSingleton ℂ _ (Lfun k i)

noncomputable def ε : (J →₀ ℂ) →ₗ[ℂ] (J →₀ ℂ) :=
  Finsupp.lsum ℂ fun i : J => LinearMap.toSpanSingleton ℂ _ (εfun i)

/--
@isnad1 id=eq.0h2v.s6.03afc8278de7 from=translated src=- shape=b7f4fec4 vocab=1ae10411
-/
theorem E_b (i : J) : E k (b i) = Efun k i := by
  rw [E, b, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul]

/--
@isnad1 id=eq.0h2v.s6.cefb1a8f6d7b from=translated src=- shape=b7f4fec4 vocab=6b45db25
-/
theorem L_b (i : J) : L k (b i) = Lfun k i := by
  rw [L, b, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul]

/--
@isnad1 id=eq.0h1v.s6.89db6fdd8cc7 from=translated src=- shape=2588ca47 vocab=ef4ab820
-/
theorem ε_b (i : J) : ε (b i) = εfun i := by
  rw [ε, b, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul]

def weightOf : J → ℤ
  | Sum.inl j => k + 2 * j
  | Sum.inr j => -(k + 2 * j)

noncomputable def wt (n : ℤ) : Submodule ℂ (J →₀ ℂ) :=
  if 0 ≤ n - k ∧ Even (n - k) then ℂ ∙ b (Sum.inl ((n - k) / 2).toNat)
  else if 0 ≤ -n - k ∧ Even (-n - k) then ℂ ∙ b (Sum.inr ((-n - k) / 2).toNat)
  else ⊥

variable {k}

/--
@isnad1 id=eq.0h2v.s6.4aee7d308c59 from=translated src=- shape=b03f4d11 vocab=d062e133
-/
theorem wt_inl (j : ℕ) : wt k (k + 2 * j) = ℂ ∙ b (Sum.inl j) := by
  have h : 0 ≤ k + 2 * (j : ℤ) - k ∧ Even (k + 2 * (j : ℤ) - k) := ⟨by omega, ⟨j, by ring⟩⟩
  simp only [wt, ite_eq_left h]
  have : (k + 2 * (j : ℤ) - k) / 2 = j := by omega
  rw [this, Int.toNat_natCast]

/--
@isnad1 id=or.0h2v.s7.c8a7d28d0159 from=translated src=- shape=5c7a7ef4 vocab=c9d2315e
-/
theorem weight_cases (n : ℤ) :
    (∃ j : ℕ, n = k + 2 * j) ∨ (∃ j : ℕ, n = -(k + 2 * j)) ∨ wt k n = ⊥ := by
  by_cases h1 : 0 ≤ n - k ∧ Even (n - k)
  · left
    refine ⟨((n - k) / 2).toNat, ?_⟩
    have := Int.two_mul_ediv_two_of_even h1.2
    have h0 : 0 ≤ (n - k) / 2 := by omega
    rw [Int.toNat_of_nonneg h0]; omega
  · by_cases h2 : 0 ≤ -n - k ∧ Even (-n - k)
    · right; left
      refine ⟨((-n - k) / 2).toNat, ?_⟩
      have := Int.two_mul_ediv_two_of_even h2.2
      have h0 : 0 ≤ (-n - k) / 2 := by omega
      rw [Int.toNat_of_nonneg h0]; omega
    · right; right
      simp only [wt, ite_eq_right h1, ite_eq_right h2]

variable (hk : 1 ≤ k)
include hk

/--
@isnad1 id=eq.1h2v.s6.e34c0becb2a5 from=translated src=- shape=df11413a vocab=8e3124bf
-/
theorem wt_inr (j : ℕ) : wt k (-(k + 2 * j)) = ℂ ∙ b (Sum.inr j) := by
  have h1 : ¬ (0 ≤ -(k + 2 * (j : ℤ)) - k ∧ Even (-(k + 2 * (j : ℤ)) - k)) := by
    rintro ⟨h, -⟩; omega
  have h2 : 0 ≤ -(-(k + 2 * (j : ℤ))) - k ∧ Even (-(-(k + 2 * (j : ℤ))) - k) :=
    ⟨by omega, ⟨j, by ring⟩⟩
  simp only [wt, ite_eq_right h1, ite_eq_left h2]
  have : (-(-(k + 2 * (j : ℤ))) - k) / 2 = j := by omega
  rw [this, Int.toNat_natCast]

/--
@isnad1 id=eq.1h2v.s6.0c64e78582f5 from=translated src=- shape=7d0b8df2 vocab=17d465be
-/
theorem wt_weightOf (i : J) : wt k (weightOf k i) = ℂ ∙ b i := by
  cases i with
  | inl j => exact wt_inl j
  | inr j => exact wt_inr hk j

/--
@isnad1 id=mem.1h2v.s6.e706d2fa117a from=translated src=- shape=893be0e1 vocab=812ea073
-/
theorem b_mem_wt (i : J) : b i ∈ wt k (weightOf k i) := by
  rw [wt_weightOf hk]; exact Submodule.mem_span_singleton_self _

/--
@isnad1 id=or.2h3v.s7.f8afb76d7962 from=translated src=- shape=e4475f05 vocab=f8fd1f20
-/
theorem mem_wt_iff {n : ℤ} {v : J →₀ ℂ} (hv : v ∈ wt k n) :
    (∃ i : J, weightOf k i = n ∧ ∃ a : ℂ, a • b i = v) ∨ v = 0 := by
  rcases weight_cases (k := k) n with ⟨j, rfl⟩ | ⟨j, rfl⟩ | h
  · rw [wt_inl, Submodule.mem_span_singleton] at hv
    exact Or.inl ⟨Sum.inl j, rfl, hv⟩
  · rw [wt_inr hk, Submodule.mem_span_singleton] at hv
    exact Or.inl ⟨Sum.inr j, rfl, hv⟩
  · rw [h, Submodule.mem_bot] at hv
    exact Or.inr hv

/--
@isnad1 id=mem.1h2v.s7.3bb667839d28 from=translated src=- shape=6700d0ba vocab=a208da80
-/
theorem E_b_mem (i : J) : E k (b i) ∈ wt k (weightOf k i + 2) := by
  rw [E_b]
  cases i with
  | inl j =>
    simp only [Efun, weightOf]
    have : k + 2 * (j : ℤ) + 2 = weightOf k (Sum.inl (j + 1)) := by
      simp only [weightOf]; push_cast; ring
    rw [this]
    exact Submodule.smul_mem _ _ (b_mem_wt hk _)
  | inr j =>
    cases j with
    | zero => simp [Efun]
    | succ j =>
      simp only [Efun, weightOf]
      have : -(k + 2 * ((j + 1 : ℕ) : ℤ)) + 2 = weightOf k (Sum.inr j) := by
        simp only [weightOf]; push_cast; ring
      rw [this]
      exact Submodule.smul_mem _ _ (b_mem_wt hk _)

/--
@isnad1 id=mem.1h2v.s7.500124d23288 from=translated src=- shape=6700d0ba vocab=a1fa6469
-/
theorem L_b_mem (i : J) : L k (b i) ∈ wt k (weightOf k i - 2) := by
  rw [L_b]
  cases i with
  | inl j =>
    cases j with
    | zero => simp [Lfun]
    | succ j =>
      simp only [Lfun, weightOf]
      have : k + 2 * ((j + 1 : ℕ) : ℤ) - 2 = weightOf k (Sum.inl j) := by
        simp only [weightOf]; push_cast; ring
      rw [this]
      exact Submodule.smul_mem _ _ (b_mem_wt hk _)
  | inr j =>
    simp only [Lfun, weightOf]
    have : -(k + 2 * (j : ℤ)) - 2 = weightOf k (Sum.inr (j + 1)) := by
      simp only [weightOf]; push_cast; ring
    rw [this]
    exact Submodule.smul_mem _ _ (b_mem_wt hk _)

/--
@isnad1 id=mem.1h2v.s7.d4ee35094ec2 from=translated src=- shape=95b0d7b3 vocab=63126097
-/
theorem ε_b_mem (i : J) : ε (b i) ∈ wt k (-weightOf k i) := by
  rw [ε_b]
  cases i with
  | inl j =>
    simp only [εfun, weightOf]
    have : -(k + 2 * (j : ℤ)) = weightOf k (Sum.inr j) := rfl
    rw [this]; exact b_mem_wt hk _
  | inr j =>
    simp only [εfun, weightOf, neg_neg]
    have : k + 2 * (j : ℤ) = weightOf k (Sum.inl j) := rfl
    rw [this]; exact b_mem_wt hk _

/--
@isnad1 id=le.2h4v.s8.b735e3fce6fa from=translated src=- shape=72b781d4 vocab=e54838a7
-/
theorem map_le_of_b {T : (J →₀ ℂ) →ₗ[ℂ] (J →₀ ℂ)} {f : ℤ → ℤ}
    (hT : ∀ i : J, T (b i) ∈ wt k (f (weightOf k i))) (n : ℤ) :
    (wt k n).map T ≤ wt k (f n) := by
  rcases weight_cases (k := k) n with ⟨j, rfl⟩ | ⟨j, rfl⟩ | h
  · rw [wt_inl, Submodule.map_span, Set.image_singleton, Submodule.span_le,
      Set.singleton_subset_iff]
    exact hT (Sum.inl j)
  · rw [wt_inr hk, Submodule.map_span, Set.image_singleton, Submodule.span_le,
      Set.singleton_subset_iff]
    exact hT (Sum.inr j)
  · rw [h, Submodule.map_bot]; exact bot_le

/--
@isnad1 id=le.1h2v.s7.2eb569efdb1e from=translated src=- shape=1a43354b vocab=79d0c093
-/
theorem map_raise_le (n : ℤ) : (wt k n).map (E k) ≤ wt k (n + 2) :=
  map_le_of_b hk (f := fun n => n + 2) (E_b_mem hk) n

/--
@isnad1 id=le.1h2v.s7.90ac8e1c4548 from=translated src=- shape=1a43354b vocab=8ffcb1cb
-/
theorem map_lower_le (n : ℤ) : (wt k n).map (L k) ≤ wt k (n - 2) :=
  map_le_of_b hk (f := fun n => n - 2) (L_b_mem hk) n

/--
@isnad1 id=le.1h2v.s7.1cd615914334 from=translated src=- shape=56a34557 vocab=65eb86b3
-/
theorem map_refl_le (n : ℤ) : (wt k n).map ε ≤ wt k (-n) :=
  map_le_of_b hk (f := fun n => -n) (ε_b_mem hk) n

omit hk in

/--
@isnad1 id=eq.0h2v.s9.354b044cc340 from=translated src=- shape=bd573cca vocab=3c115d37
-/
theorem raise_lower_sub_b (i : J) :
    E k (L k (b i)) - L k (E k (b i)) = (weightOf k i : ℂ) • b i := by
  cases i with
  | inl j =>
    cases j with
    | zero =>
      rw [L_b, E_b]
      simp only [Lfun, Efun, map_zero, map_smul, L_b, zero_sub, smul_smul, weightOf,
        Nat.cast_zero, ← neg_smul]
      congr 1
      push_cast; ring
    | succ j =>
      rw [L_b, E_b]
      simp only [Lfun, Efun, map_smul, E_b, L_b, smul_smul, weightOf, ← sub_smul]
      congr 1
      push_cast; ring
  | inr j =>
    cases j with
    | zero =>
      rw [L_b, E_b]
      simp only [Lfun, Efun, map_zero, map_smul, E_b, sub_zero, smul_smul, weightOf,
        Nat.cast_zero]
      congr 1
      push_cast; ring
    | succ j =>
      rw [L_b, E_b]
      simp only [Lfun, Efun, map_smul, E_b, L_b, smul_smul, weightOf, ← sub_smul]
      congr 1
      push_cast; ring

/--
@isnad1 id=eq.2h3v.s9.0f3f558be23a from=translated src=- shape=54a22ed2 vocab=ad5118cb
-/
theorem raise_lower_sub (n : ℤ) (v : J →₀ ℂ) (hv : v ∈ wt k n) :
    E k (L k v) - L k (E k v) = (n : ℂ) • v := by
  rcases mem_wt_iff hk hv with ⟨i, rfl, a, rfl⟩ | rfl
  · simp only [map_smul, ← smul_sub, raise_lower_sub_b, smul_smul, mul_comm a]
  · simp

omit hk in
/--
@isnad1 id=eq.0h0v.s7.1d6ff740908c from=translated src=- shape=f30035b4 vocab=d298edb9
-/
theorem refl_comp_refl : (ε : (J →₀ ℂ) →ₗ[ℂ] _) ∘ₗ ε = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i c
  simp only [LinearMap.comp_apply, LinearMap.id_apply, single_eq_smul_b, map_smul, ε_b]
  congr 1
  rcases i with j | j <;> simp only [εfun, ε_b]

omit hk in
/--
@isnad1 id=eq.0h1v.s7.d41e4d2a7907 from=translated src=- shape=1b3fc43e vocab=78f05e4b
-/
theorem refl_comp_raise : (ε : (J →₀ ℂ) →ₗ[ℂ] _) ∘ₗ E k = L k ∘ₗ ε := by
  apply Finsupp.lhom_ext
  intro i c
  simp only [LinearMap.comp_apply, single_eq_smul_b, map_smul, ε_b, E_b]
  congr 1
  rcases i with j | _ | j <;> simp only [Efun, εfun, map_smul, map_zero, ε_b, L_b, Lfun]

/--
@isnad1 id=le.2h3v.s7.febadde38166 from=translated src=- shape=2b8b9d90 vocab=88d30cc4
-/
theorem wt_le_ker_lapply {m : ℤ} {i : J} (hm : m ≠ weightOf k i) :
    wt k m ≤ LinearMap.ker (Finsupp.lapply (M := ℂ) (R := ℂ) i) := by
  rcases weight_cases (k := k) m with ⟨j, rfl⟩ | ⟨j, rfl⟩ | h
  · rw [wt_inl, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LinearMap.mem_ker, Finsupp.lapply_apply, b_apply, ite_eq_right]
    rintro rfl; exact hm rfl
  · rw [wt_inr hk, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LinearMap.mem_ker, Finsupp.lapply_apply, b_apply, ite_eq_right]
    rintro rfl; exact hm rfl
  · rw [h]; exact bot_le

/--
@isnad1 id=isupinde.1h1v.s5.4459933363ec from=translated src=- shape=f58e0756 vocab=4f010f12
-/
theorem iSupIndep_wt : iSupIndep (wt k) := by
  rw [iSupIndep_def]
  intro n
  rcases weight_cases (k := k) n with ⟨j, rfl⟩ | ⟨j, rfl⟩ | h
  · have hle : (⨆ (m : ℤ) (_ : m ≠ k + 2 * (j : ℤ)), wt k m) ≤
        LinearMap.ker (Finsupp.lapply (M := ℂ) (R := ℂ) (Sum.inl j : J)) :=
      iSup₂_le fun m hm => wt_le_ker_lapply hk hm
    refine Disjoint.mono_right hle ?_
    rw [wt_inl]
    refine Disjoint.symm ((Submodule.disjoint_span_singleton' (b_ne_zero _)).mpr ?_)
    simp [b_apply]
  · have hle : (⨆ (m : ℤ) (_ : m ≠ -(k + 2 * (j : ℤ))), wt k m) ≤
        LinearMap.ker (Finsupp.lapply (M := ℂ) (R := ℂ) (Sum.inr j : J)) :=
      iSup₂_le fun m hm => wt_le_ker_lapply hk hm
    refine Disjoint.mono_right hle ?_
    rw [wt_inr hk]
    refine Disjoint.symm ((Submodule.disjoint_span_singleton' (b_ne_zero _)).mpr ?_)
    simp [b_apply]
  · rw [h]; exact disjoint_bot_left

/--
@isnad1 id=eq.1h1v.s7.bb87f5591244 from=translated src=- shape=e83b994e vocab=a09179c5
-/
theorem iSup_wt : (⨆ n : ℤ, wt k n) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  induction v using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add i c f _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    rw [single_eq_smul_b]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem (weightOf k i) (b_mem_wt hk i))

/--
@isnad1 id=isgl2rea.1h1v.s5.8307f7244c22 from=translated src=- shape=3804618e vocab=089f5bc9
-/
theorem isGL2RealKTypeModule : IsGL2RealKTypeModule (wt k) (E k) (L k) ε where
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_wt hk) (iSup_wt hk)
  map_raise_le := map_raise_le hk
  map_lower_le := map_lower_le hk
  raise_lower_sub := raise_lower_sub hk
  map_refl_le := map_refl_le hk
  refl_comp_refl := refl_comp_refl
  refl_comp_raise := refl_comp_raise

/--
@isnad1 id=finitedi.1h2v.s7.b4f00e1e7837 from=translated src=- shape=93da0078 vocab=3b242710
-/
theorem finiteDimensional_wt (n : ℤ) : FiniteDimensional ℂ (wt k n) := by
  rcases weight_cases (k := k) n with ⟨j, rfl⟩ | ⟨j, rfl⟩ | h
  · rw [wt_inl]; infer_instance
  · rw [wt_inr hk]; infer_instance
  · rw [h]; infer_instance

/--
@isnad1 id=iff.1h2v.s6.ae8e7bceaaaf from=translated src=- shape=51ee94a4 vocab=3dba56c2
-/
theorem wt_ne_bot_iff (n : ℤ) : wt k n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)) := by
  rcases weight_cases (k := k) n with ⟨j, rfl⟩ | ⟨j, rfl⟩ | h
  · rw [wt_inl]
    simp only [ne_eq, Submodule.span_singleton_eq_bot, b_ne_zero, not_false_eq_true, true_iff]
    refine ⟨?_, ⟨j, by ring⟩⟩
    rw [abs_of_nonneg (by omega)]; omega
  · rw [wt_inr hk]
    simp only [ne_eq, Submodule.span_singleton_eq_bot, b_ne_zero, not_false_eq_true, true_iff]
    refine ⟨?_, ⟨-(k : ℤ) - j, by ring⟩⟩
    rw [abs_of_nonpos (by omega)]; omega
  · simp only [h, ne_eq, not_true_eq_false, false_iff, not_and]
    intro habs heven
    rcases le_or_gt 0 n with hn | hn
    · rw [abs_of_nonneg hn] at habs
      have hj : n = k + 2 * ((((n - k) / 2).toNat : ℕ) : ℤ) := by
        have := Int.two_mul_ediv_two_of_even heven
        rw [Int.toNat_of_nonneg (by omega)]; omega
      rw [hj, wt_inl] at h
      exact b_ne_zero _ (Submodule.span_singleton_eq_bot.mp h)
    · rw [abs_of_neg hn] at habs
      have heven' : Even (-n - k) := by
        obtain ⟨r, hr⟩ := heven
        exact ⟨-r - k, by omega⟩
      have hj : n = -(k + 2 * ((((-n - k) / 2).toNat : ℕ) : ℤ)) := by
        have := Int.two_mul_ediv_two_of_even heven'
        rw [Int.toNat_of_nonneg (by omega)]; omega
      rw [hj, wt_inr hk] at h
      exact b_ne_zero _ (Submodule.span_singleton_eq_bot.mp h)

omit hk in
/--
@isnad1 id=infinite.0h1v.s6.6618aebeeea9 from=translated src=- shape=8161d38a vocab=796c045f
-/
theorem infinite_support : {n : ℤ | wt k n ≠ ⊥}.Infinite := by
  have hinj : Function.Injective fun j : ℕ => k + 2 * (j : ℤ) := by
    intro a b hab; simp only at hab; omega
  refine Set.infinite_of_injective_forall_mem hinj fun j => ?_
  simp only [Set.mem_ofPred_eq]
  rw [wt_inl]
  simp [b_ne_zero]

/--
@isnad1 id=iff.1h2v.s7.673fed43e6a6 from=translated src=- shape=8ed88244 vocab=32c60888
-/
theorem lowestWeight_iff (k' : ℤ) : (∃ v ∈ wt k k', v ≠ 0 ∧ L k v = 0) ↔ k' = k := by
  constructor
  · rintro ⟨v, hv, hv0, hL⟩
    rcases mem_wt_iff hk hv with ⟨i, rfl, a, rfl⟩ | rfl
    · have ha : a ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
      rw [map_smul, L_b] at hL
      cases i with
      | inl j =>
        cases j with
        | zero => simp [weightOf]
        | succ j =>
          exfalso
          simp only [Lfun, smul_smul] at hL
          have hcoef : a * -((j + 1 : ℕ) : ℂ) = 0 := by
            have := congrArg (fun f : J →₀ ℂ => f (Sum.inl j)) hL
            simpa [b_apply] using this
          rcases mul_eq_zero.mp hcoef with h | h
          · exact ha h
          · rw [neg_eq_zero] at h
            exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) h
      | inr j =>
        exfalso
        simp only [Lfun, smul_smul] at hL
        have hcoef : a * ((k : ℂ) + j) = 0 := by
          have := congrArg (fun f : J →₀ ℂ => f (Sum.inr (j + 1))) hL
          simpa [b_apply] using this
        rcases mul_eq_zero.mp hcoef with h | h
        · exact ha h
        · have : ((k + j : ℤ) : ℂ) = 0 := by push_cast; exact h
          have : (k + j : ℤ) = 0 := by exact_mod_cast this
          omega
    · exact absurd rfl hv0
  · rintro rfl
    refine ⟨b (Sum.inl 0), ?_, b_ne_zero _, ?_⟩
    · have := b_mem_wt hk (Sum.inl 0)
      simpa [weightOf] using this
    · rw [L_b]; rfl

/--
@isnad1 id=ex.3h2v.s8.b1c48d8e2382 from=translated src=- shape=5ab99347 vocab=2f161584
-/
theorem exists_b_mem {W : Submodule ℂ (J →₀ ℂ)} (hW : W ≤ ⨆ n : ℤ, W ⊓ wt k n) (hW0 : W ≠ ⊥) :
    ∃ i : J, b i ∈ W := by
  by_contra hcon
  push Not at hcon
  apply hW0
  have hall : ∀ n : ℤ, W ⊓ wt k n = ⊥ := by
    intro n
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvW, hvwt⟩
    rcases mem_wt_iff hk hvwt with ⟨i, -, a, rfl⟩ | rfl
    · by_contra hne
      have ha : a ≠ 0 := by rintro rfl; exact hne (zero_smul _ _)
      apply hcon i
      have := Submodule.smul_mem W a⁻¹ hvW
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    · rfl
  rw [eq_bot_iff]
  refine hW.trans ?_
  simp [hall]

omit hk in
/--
@isnad1 id=mem.3h3v.s8.50f05b7f3217 from=translated src=- shape=5185578c vocab=e7dfae09
-/
theorem b_inl_zero_mem {W : Submodule ℂ (J →₀ ℂ)} (hL : W.map (L k) ≤ W) (hε : W.map ε ≤ W)
    {i : J} (hi : b i ∈ W) : b (Sum.inl 0) ∈ W := by

  have hpos : ∃ j : ℕ, b (Sum.inl j) ∈ W := by
    cases i with
    | inl j => exact ⟨j, hi⟩
    | inr j =>
      refine ⟨j, ?_⟩
      have := hε (Submodule.mem_map_of_mem hi)
      rwa [ε_b] at this
  obtain ⟨j, hj⟩ := hpos

  induction j with
  | zero => exact hj
  | succ j ih =>
    apply ih
    have h1 : L k (b (Sum.inl (j + 1))) ∈ W := hL (Submodule.mem_map_of_mem hj)
    rw [L_b] at h1
    simp only [Lfun] at h1
    have hne : (-((j + 1 : ℕ) : ℂ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))
    have := Submodule.smul_mem W (-((j + 1 : ℕ) : ℂ))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/--
@isnad1 id=mem.4h3v.s8.795cc00eef35 from=translated src=- shape=71ae3598 vocab=854243e9
-/
theorem b_mem_all {W : Submodule ℂ (J →₀ ℂ)} (hE : W.map (E k) ≤ W) (hε : W.map ε ≤ W)
    (h0 : b (Sum.inl 0) ∈ W) (i : J) : b i ∈ W := by
  have hpos : ∀ j : ℕ, b (Sum.inl j) ∈ W := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih =>
      have h1 : E k (b (Sum.inl j)) ∈ W := hE (Submodule.mem_map_of_mem ih)
      rw [E_b] at h1
      simp only [Efun] at h1
      have hne : ((k : ℂ) + j) ≠ 0 := by
        intro h
        have : ((k + j : ℤ) : ℂ) = 0 := by push_cast; exact h
        have : (k + j : ℤ) = 0 := by exact_mod_cast this
        omega
      have := Submodule.smul_mem W ((k : ℂ) + j)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  cases i with
  | inl j => exact hpos j
  | inr j =>
    have := hε (Submodule.mem_map_of_mem (hpos j))
    rwa [ε_b] at this

/--
@isnad1 id=isirredu.1h1v.s5.de7ca94ee969 from=translated src=- shape=3804618e vocab=f7a1503f
-/
theorem isIrreducible : IsIrreducibleGL2RealKTypeModule (wt k) (E k) (L k) ε := by
  refine ⟨⟨b (Sum.inl 0), b_ne_zero _⟩, fun W hW => ?_⟩
  obtain ⟨hgr, hE, hL, hε⟩ := hW
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨i, hi⟩ := exists_b_mem hk hgr hW0
  have h0 := b_inl_zero_mem hL hε hi
  rw [Submodule.eq_top_iff']
  intro v
  induction v using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add i c f _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    rw [single_eq_smul_b]
    exact Submodule.smul_mem _ _ (b_mem_all hk hE hε h0 i)

end AutomorphicForm.GL2RealDiscreteSeriesModel

open AutomorphicForm.GL2RealDiscreteSeriesModel in
/--
@isnad1 id=ex.1h1v.s8.4fabba59dcea from=translated src=- shape=aa4612dd vocab=fdf35af5
-/
theorem solution (k : ℤ) (hk : 1 ≤ k) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k))) ∧
      (∀ k' : ℤ, (∃ v ∈ wt k', v ≠ 0 ∧ L v = 0) ↔ k' = k) :=
  ⟨(ℕ ⊕ ℕ) →₀ ℂ, inferInstance, inferInstance, wt k, E k, L k, ε, isGL2RealKTypeModule hk,
    finiteDimensional_wt hk, isIrreducible hk, infinite_support, wt_ne_bot_iff hk,
    lowestWeight_iff hk⟩
