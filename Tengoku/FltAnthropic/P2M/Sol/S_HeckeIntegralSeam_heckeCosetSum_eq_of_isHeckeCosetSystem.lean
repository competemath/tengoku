import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem

set_option autoImplicit false

/--
@isnad1 id=eq.3h8v.s7.2774bf009939 from=translated src=- shape=8708ce77 vocab=46acc293
-/
theorem P1RepIndep.heckeCosetSum_eq_of_isHeckeCosetSystem_impl
    {G : Type*} [Group G] {n : ℕ} {U : Subgroup G} {gv : G}
    {reps reps' : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps)
    (hsys' : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps')
    {φ : G → ℂ} (hinv : ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g) (g : G) :
    ∑ i, φ (g * reps' i) = ∑ i, φ (g * reps i) := by
  have hchoice : ∀ i : Fin n, ∃ j : Fin n,
      (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps' j) :=
    fun i => hsys'.covers (reps i) (hsys.mem_doubleCoset i)
  choose e he using hchoice
  have hinj : Function.Injective e := fun i₁ i₂ h => hsys.mk_injective (by
    show (QuotientGroup.mk (reps i₁) : G ⧸ U) = QuotientGroup.mk (reps i₂)
    rw [he i₁, he i₂, h])
  have hbij : Function.Bijective e := Finite.injective_iff_bijective.mp hinj
  have hpt : ∀ i : Fin n, φ (g * reps' (e i)) = φ (g * reps i) := by
    intro i
    have hu : (reps i)⁻¹ * reps' (e i) ∈ U := QuotientGroup.eq.mp (he i)
    have harg : g * reps' (e i) = g * reps i * ((reps i)⁻¹ * reps' (e i)) := by
      rw [mul_assoc, mul_inv_cancel_left]
    rw [harg]
    exact hinv (g * reps i) _ hu
  exact (Fintype.sum_bijective e hbij (fun i => φ (g * reps i))
    (fun j => φ (g * reps' j)) (fun i => (hpt i).symm)).symm

/--
@isnad1 id=eq.3h8v.s7.2774bf009939 from=translated src=- shape=8708ce77 vocab=46acc293
-/
theorem solution
    {G : Type*} [Group G] {n : ℕ} {U : Subgroup G} {gv : G}
    {reps reps' : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps)
    (hsys' : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps')
    {φ : G → ℂ} (hinv : ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g) (g : G) :
    ∑ i, φ (g * reps' i) = ∑ i, φ (g * reps i) := by
  exact P1RepIndep.heckeCosetSum_eq_of_isHeckeCosetSystem_impl hsys hsys' hinv g
