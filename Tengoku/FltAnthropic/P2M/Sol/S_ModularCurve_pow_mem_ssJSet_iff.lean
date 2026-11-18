import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SupersingularModuli
import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_RatPointHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_pow_mem_ssJSet_iff.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_pow_mem_ssJSet_iff

open _root_.ModularCurve

set_option autoImplicit false

namespace ModularCurve export _root_.ModularCurve (ssJSet mem_ssJSet_iff) end ModularCurve
open scoped _root_.ModularCurve in

theorem ModularCurve.solution_aux_ringEquiv_mem {K : Type} [Field K] [DecidableEq K] (p : ℕ)
    (σ : K ≃+* K) {a : K} (ha : a ∈ ssJSet p K) : σ a ∈ ssJSet p K := by
  rw [mem_ssJSet_iff] at ha ⊢
  intro W _ hj P hP
  have hj₀ : (W.map (σ.symm : K →+* K)).j = a := by
    rw [W.map_j, hj]; simp
  have h0 : WeierstrassCurve.ratPointHom (σ.symm : K →+* K) P = 0 :=
    ha _ hj₀ _ (by rw [← map_nsmul, hP, map_zero])
  rw [WeierstrassCurve.ratPointHom_apply] at h0
  exact WeierstrassCurve.ratPointMap_injective (σ.symm : K →+* K)
    (h0.trans (WeierstrassCurve.ratPointMap_zero _).symm)

theorem solution {K : Type} [Field K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K] (a : K) :
    a ^ q ∈ ModularCurve.ssJSet q K ↔ a ∈ ModularCurve.ssJSet q K := by
  rw [← frobeniusEquiv_def K q a]
  exact ⟨fun h => by simpa using ModularCurve.solution_aux_ringEquiv_mem q (frobeniusEquiv K q).symm h,
    ModularCurve.solution_aux_ringEquiv_mem q (frobeniusEquiv K q)⟩
