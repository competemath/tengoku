import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem

set_option autoImplicit false

namespace HeckeIntegralSeam
export _root_.HeckeIntegralSeam (IsHeckeCosetSystem)
open _root_.HeckeIntegralSeam
namespace IsHeckeCosetSystem
export _root_.HeckeIntegralSeam.IsHeckeCosetSystem (mk_injective covers mk mem_doubleCoset)
open _root_.HeckeIntegralSeam.IsHeckeCosetSystem
namespace KcPermR1

variable {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} {reps : ι₀ → G}

theorem exists_mk_mul_eq_mk (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) (i : ι₀) :
    ∃ j, (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (reps j) :=
  hsys.covers _ (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu)

noncomputable def leftPerm (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) : ι₀ → ι₀ :=
  fun i => Classical.choose (exists_mk_mul_eq_mk hsys hu i)

theorem mk_mul_eq_mk_leftPerm (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) (i : ι₀) :
    (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (reps (leftPerm hsys hu i)) :=
  Classical.choose_spec (exists_mk_mul_eq_mk hsys hu i)

theorem exists_mul_reps_eq (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) (i : ι₀) :
    ∃ u' ∈ U, u * reps i = reps (leftPerm hsys hu i) * u' := by
  have h := mk_mul_eq_mk_leftPerm hsys hu i
  rw [QuotientGroup.eq] at h
  refine ⟨(reps (leftPerm hsys hu i))⁻¹ * (u * reps i), ?_, by group⟩
  have := U.inv_mem h
  simpa [mul_inv_rev] using this

theorem leftPerm_injective (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) :
    Function.Injective (leftPerm hsys hu) := by
  intro i j hij
  have hi := mk_mul_eq_mk_leftPerm hsys hu i
  have hj := mk_mul_eq_mk_leftPerm hsys hu j
  rw [hij] at hi
  have hmk : (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (u * reps j) :=
    hi.trans hj.symm
  apply hsys.mk_injective
  change (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
  rw [QuotientGroup.eq] at hmk ⊢
  simpa [mul_inv_rev, mul_assoc] using hmk

theorem leftPerm_surjective (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) :
    Function.Surjective (leftPerm hsys hu) := by
  intro j
  obtain ⟨i, hi⟩ := exists_mk_mul_eq_mk hsys (U.inv_mem hu) j
  refine ⟨i, ?_⟩
  apply hsys.mk_injective
  change (QuotientGroup.mk (reps (leftPerm hsys hu i)) : G ⧸ U) = QuotientGroup.mk (reps j)
  rw [← mk_mul_eq_mk_leftPerm hsys hu i]
  rw [QuotientGroup.eq] at hi ⊢
  have := U.inv_mem hi
  simpa [mul_inv_rev, mul_assoc] using this

end KcPermR1
end IsHeckeCosetSystem
end HeckeIntegralSeam

open _root_.HeckeIntegralSeam _root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.HeckeIntegralSeam _root_.HeckeIntegralSeam.IsHeckeCosetSystem _root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.HeckeIntegralSeam.IsHeckeCosetSystem _root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.HeckeIntegralSeam.IsHeckeCosetSystem.KcPermR1 in
theorem solution
    {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} {reps : ι₀ → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (u : G) (hu : u ∈ U) :
    ∃ π : ι₀ → ι₀, Function.Bijective π ∧
      ∀ i : ι₀, ∃ u' ∈ U, u * reps i = reps (π i) * u' :=
  ⟨leftPerm hsys hu, ⟨leftPerm_injective hsys hu, leftPerm_surjective hsys hu⟩,
    fun i => exists_mul_reps_eq hsys hu i⟩
