/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.SardMoreira.ContDiff
import Tengoku.LeanPool.LeanPool.SardMoreira.ContinuousMultilinearMap
import Tengoku.LeanPool.LeanPool.SardMoreira.ToMathlib.ContinuousLinearMap

/-!
# LeanPool.SardMoreira.ContDiffMoreiraHolder
-/

@[expose] public section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A map `f` is `C^{k+(α)}` at a point `a`, meaning it is `C^k` at `a` and its
`k`-th derivative satisfies a pointwise Hölder estimate of exponent `α` at `a`. -/
@[mk_iff]
structure ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  /-- A `C^{k+(α)}` map is in particular `C^k` at the point. -/
  contDiffAt : ContDiffAt ℝ k f a
  /-- A `C^{k+(α)}` map satisfies `D^k f x - D^k f a = O(‖x - a‖^α)` as `x → a`. -/
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

/--
@isnad1 id=contdiff.2h7v.s6.914f51137364 from=translated src=- shape=8fe50665 vocab=8643dfa8
-/
theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt ℝ n f a) (hk : k < n) (α : I) : ContDiffMoreiraHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffMoreiraHolderAt

/--
@isnad1 id=continuo.1h6v.s6.81e117d70d9b from=translated src=- shape=2232b642 vocab=2bd43d05
-/
theorem continuousAt {k : ℕ} {α : I} {f : E → F} {a : E} (h : ContDiffMoreiraHolderAt k α f a) :
    ContinuousAt f a :=
  h.contDiffAt.continuousAt

/--
@isnad1 id=differen.2h6v.s6.5bc7d3aaeb27 from=translated src=- shape=83a4355c vocab=4558988c
-/
theorem differentiableAt {k : ℕ} {α : I} {f : E → F} {a : E} (h : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : DifferentiableAt ℝ f a :=
  h.contDiffAt.differentiableAt <| mod_cast hk

/--
@isnad1 id=iff.0h5v.s6.4ec9b8262460 from=translated src=- shape=3b306d69 vocab=a05e87d9
-/
@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

/--
@isnad1 id=iff.0h5v.s7.99febb5975d0 from=translated src=- shape=9aaa5952 vocab=2fc2dd34
-/
theorem zero_left_iff {α : I} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt 0 α f a ↔
      ContDiffAt ℝ 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) := by
  simp only [contDiffMoreiraHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

/--
@isnad1 id=contdiff.2h7v.s6.f516ca2ad217 from=translated src=- shape=2ab0af64 vocab=a14e9b9a
-/
theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hle : β ≤ α) : ContDiffMoreiraHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

/--
@isnad1 id=contdiff.2h8v.s6.a1b87deb1b3b from=translated src=- shape=fe47b47b vocab=7adc9ffc
-/
theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hlt : l < k) : ContDiffMoreiraHolderAt l β f a :=
  hf.contDiffAt.contDiffMoreiraHolderAt (mod_cast hlt) _

/--
@isnad1 id=contdiff.2h8v.s7.4c736263e22b from=translated src=- shape=50d61fe5 vocab=9ba9ab49
-/
theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hle : toLex (l, β) ≤ toLex (k, α)) : ContDiffMoreiraHolderAt l β f a :=
  (Prod.Lex.le_iff.mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

/--
@isnad1 id=contdiff.2h7v.s6.a532279d97c0 from=translated src=- shape=4a6a0958 vocab=8ae72507
-/
theorem of_le {k l : ℕ} {f : E → F} {a : E} {α : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hl : l ≤ k) : ContDiffMoreiraHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

/--
@isnad1 id=contdiff.3h8v.s8.97c09b96d3a5 from=translated src=- shape=967cbb7e vocab=a6aa680c
-/
theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffMoreiraHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    have hdist' :
        dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f a) ≤
          (C : ℝ) * dist x a ^ (α : ℝ) := by
      convert hd.dist_le hx (mem_of_mem_nhds hs) using 2
      rfl
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg] using hdist'

/--
@isnad1 id=contdiff.0h5v.s6.4dec8b7e3a77 from=translated src=- shape=47e0ad4f vocab=3670ec67
-/
theorem fst {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

/--
@isnad1 id=contdiff.0h5v.s6.fe4343183db6 from=translated src=- shape=ec666c05 vocab=05491f72
-/
theorem snd {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.snd a :=
  contDiffAt_snd.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

/--
@isnad1 id=contdiff.2h8v.s6.895e40cca5c2 from=translated src=- shape=a740c2be vocab=1141bcb1
-/
theorem prodMk {k : ℕ} {α : I} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffMoreiraHolderAt k α f a) (hg : ContDiffMoreiraHolderAt k α g a) :
    ContDiffMoreiraHolderAt k α (fun x ↦ (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x ↦ (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f a).prod
                (iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.eventually (by simp)] with x hfx hgx
      apply DFunLike.ext
      rw [iteratedFDeriv_prodMk _ _ le_rfl, iteratedFDeriv_prodMk _ _ le_rfl] <;>
        simp [hfx, hgx, hf.contDiffAt, hg.contDiffAt]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      refine .of_norm_left ?_
      simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
      exact (hf.isBigO.prod_left hg.isBigO).norm_left

/--
@isnad1 id=contdiff.3h8v.s7.88e966610b8c from=translated src=- shape=74ec9323 vocab=7531516e
-/
theorem comp' {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a where
  contDiffAt := hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv ℝ k (g ∘ f) · - iteratedFDeriv ℝ k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x ↦ (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) k -
        (ftaylorSeries ℝ g (f a)).taylorComp (ftaylorSeries ℝ f a) k := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hf.continuousAt.eventually (hg.contDiffAt.eventually (by simp))] with x hfx hgx
      rw [iteratedFDeriv_comp hgx hfx le_rfl,
        iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt le_rfl]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
      · intro i hi
        exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
          |>.norm.isBoundedUnder_le
      · intro i hi
        by_cases hfd : DifferentiableAt ℝ f a
        · refine ((hg.of_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
          exact .rpow α.2.1 (.of_forall fun _ ↦ norm_nonneg _) <| .norm_norm hfd.isBigO_sub
        · obtain rfl : k = 0 := by
            contrapose! hfd
            exact hf.differentiableAt hfd
          obtain rfl : i = 0 := by rwa [nonpos_iff_eq_zero] at hi
          refine .of_norm_left ?_
          simp only [ftaylorSeries, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          refine ((hd.resolve_right hfd).isBigO_sub.comp_tendsto hf.continuousAt).trans ?_
          refine .trans (.of_norm_right ?_) hf.isBigO
          simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, LinearIsometryEquiv.norm_map,
            ← map_sub]
          exact isBigO_norm_right.mpr (isBigO_refl _ _)
      · intro i hi
        exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact fun _ _ ↦ isBoundedUnder_const
      · exact fun i hi ↦ (hf.of_le hi).isBigO

/--
@isnad1 id=contdiff.3h8v.s6.9dc8bed15543 from=translated src=- shape=87fc5853 vocab=dfa80749
-/
theorem comp {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  hg.comp' hf (.inl <| hg.differentiableAt hk)

theorem _root_.ContinuousLinearMap.contDiffMoreiraHolderAt
    (f : E →L[ℝ] F) {a : E} {k : ℕ} {α : I} :
    ContDiffMoreiraHolderAt k α f a :=
  f.contDiff.contDiffAt.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) _

theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt
    (f : E ≃L[ℝ] F) {a : E} {k : ℕ} {α : I} :
    ContDiffMoreiraHolderAt k α f a :=
  f.toContinuousLinearMap.contDiffMoreiraHolderAt

/--
@isnad1 id=contdiff.1h8v.s7.8e2754bda737 from=translated src=- shape=70cee642 vocab=482bb718
-/
theorem continuousLinearMap_comp {f : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  g.contDiffMoreiraHolderAt.comp' hf <| .inl g.differentiableAt

@[simp]
theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G →L[ℝ] F),
    fun h ↦ h.continuousLinearMap_comp (g : F →L[ℝ] G)⟩

@[simp]
theorem _root_.LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp

/--
@isnad1 id=contdiff.0h4v.s5.7d6b1e27b7d0 from=translated src=- shape=35240470 vocab=1588de8b
-/
protected theorem id {k : ℕ} {α : I} {a : E} : ContDiffMoreiraHolderAt k α id a :=
  ContinuousLinearMap.id ℝ E |>.contDiffMoreiraHolderAt

/--
@isnad1 id=contdiff.0h6v.s5.000be77bb7c4 from=translated src=- shape=44826440 vocab=654e9489
-/
protected theorem const {k : ℕ} {α : I} {a : E} {b : F} :
    ContDiffMoreiraHolderAt k α (Function.const E b) a :=
  contDiffAt_const.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

/--
@isnad1 id=contdiff.2h7v.s8.bb6c1543d2a3 from=translated src=- shape=c91d8eb8 vocab=8f3c2f92
-/
protected theorem fderiv {f : E → F} {a : E} {k l : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + 1 ≤ k) :
    ContDiffMoreiraHolderAt l α (fderiv ℝ f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
  isBigO := .of_norm_left <| by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
      using hf.of_le hl |>.isBigO |>.norm_left

/--
@isnad1 id=contdiff.2h8v.s7.1fdfbac2cda2 from=translated src=- shape=6c24ef13 vocab=44034346
-/
protected theorem iteratedFDeriv {f : E → F} {a : E} {k l m : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffMoreiraHolderAt l α (iteratedFDeriv ℝ m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_le hl
  | succ m ihm =>
    rw [← add_assoc, add_right_comm] at hl
    -- TODO: why `simp` fails to apply the lemma? Does it fail to unify some instances?
    -- Does it happen on the latest Mathlib?
    simp +unfoldPartialApp only [iteratedFDeriv_succ_eq_comp_left]
    exact (LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun x ↦ E) F).symm).mpr ((ihm hl).fderiv le_rfl)

/--
@isnad1 id=contdiff.2h7v.s6.83eec8e63597 from=translated src=- shape=14176ce2 vocab=a36ff12f
-/
theorem congr_eventuallyEq {f g : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffMoreiraHolderAt k α g a where
  contDiffAt := hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv ℝ _
    · rw [hfg.symm.iteratedFDeriv ℝ _ |>.self_of_nhds]

end ContDiffMoreiraHolderAt
