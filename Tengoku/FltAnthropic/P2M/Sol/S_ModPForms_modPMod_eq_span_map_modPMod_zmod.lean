import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_modPMod_eq_span_map_modPMod_zmod.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_modPMod_eq_span_map_modPMod_zmod
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModPForms
export _root_.ModPForms (modPCusp modPMod)
namespace BaseChange
open _root_.ModPForms

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]

noncomputable abbrev ι : PowerSeries (ZMod p) →+* PowerSeries F :=
  PowerSeries.map (ZMod.castHom (dvd_refl p) F)

theorem ι_mk_intCast (a : ℕ → ℤ) :
    ι p F (PowerSeries.mk fun n => ((a n : ℤ) : ZMod p)) = PowerSeries.mk fun n => ((a n : ℤ) : F) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_intCast]

theorem span_image_span (S : Set (PowerSeries (ZMod p))) :
    Submodule.span F (ι p F '' (Submodule.span (ZMod p) S : Set (PowerSeries (ZMod p)))) =
      Submodule.span F (ι p F '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      have : ι p F (c • y) = (ZMod.castHom (dvd_refl p) F c) • ι p F y := by
        rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul]
      rw [this]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem genSet_modPMod_eq_image (N : ℕ) (k : ℤ) :
    {φ : PowerSeries F | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)} =
    ι p F '' {φ : PowerSeries (ZMod p) | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : ZMod p)} := by
  ext φ
  constructor
  · rintro ⟨f, a, ha, rfl⟩
    exact ⟨_, ⟨f, a, ha, rfl⟩, ι_mk_intCast p F a⟩
  · rintro ⟨_, ⟨f, a, ha, rfl⟩, rfl⟩
    exact ⟨f, a, ha, ι_mk_intCast p F a⟩

theorem modPMod_eq_span_image (N : ℕ) (k : ℤ) :
    ModPForms.modPMod N k F =
      Submodule.span F (ι p F '' (ModPForms.modPMod N k (ZMod p) : Set (PowerSeries (ZMod p)))) := by
  rw [ModPForms.modPMod, ModPForms.modPMod, span_image_span, genSet_modPMod_eq_image]

end ModPForms.BaseChange

theorem solution (p : ℕ) [Fact p.Prime] (N : ℕ) (k : ℤ) (F : Type) [Field F] [CharP F p] :
    ModPForms.modPMod N k F =
      Submodule.span F (PowerSeries.map (ZMod.castHom (dvd_refl p) F) ''
        (ModPForms.modPMod N k (ZMod p) : Set (PowerSeries (ZMod p)))) :=
  ModPForms.BaseChange.modPMod_eq_span_image p F N k
