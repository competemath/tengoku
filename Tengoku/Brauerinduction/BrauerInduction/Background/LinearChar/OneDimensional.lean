import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

variable {G : Type v} [Group G]
variable {k : Type u} [Field k]

namespace FDRep

/--
Construct a linear character from a one-dimensional representation of a group.

If `σ` is one-dimensional, choose a linear equivalence `σ ≃ₗ[k] k` and a
nonzero vector `v₀` mapping to `1`.  Each group element acts on the line spanned
by `v₀` by a nonzero scalar; these scalars form the desired linear character.-/
noncomputable def linearCharOfOneDim
    (σ : FDRep k G)
    (h_dim : Module.finrank k σ = 1) :
    G →* kˣ := by
  let e : σ ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq σ k (by rw [h_dim, Module.finrank_self])
  let v0 : σ := e.symm 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have : e v0 = 0 := by rw [h, map_zero]
    simp [v0] at this
  let χ : G → k := fun g => e (σ.ρ g v0)
  have h_scale : ∀ g : G, σ.ρ g v0 = (χ g) • v0 := by
    intro g
    apply e.injective
    simp only [v0, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, χ]
  have hχ_ne0 : ∀ g : G, χ g ≠ 0 := by
    intro g hg
    have h_im := h_scale g
    rw [hg, zero_smul] at h_im
    have h_inj : Function.Injective (σ.ρ g) :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot_of_inverse
        (g := σ.ρ g⁻¹)
        (by ext; simp)
      )
    apply hv0
    apply h_inj
    rw [map_zero, h_im]
  refine {
    toFun := fun g => Units.mk0 (χ g) (hχ_ne0 g),
    map_one' := by
      ext
      simp only [Units.val_mk0, χ]
      simp only [Units.val_one]
      simp only [map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply e 1, v0]
    map_mul' := by
      intro x y
      ext
      simp only [Units.val_mk0, Units.val_mul]
      dsimp [χ]
      simp only [map_mul, Module.End.mul_apply]
      rw [h_scale y, map_smul, h_scale x]
      rw [smul_smul, map_smul, mul_comm]
      have he : e v0 = 1 := by simp [v0]
      simp only [smul_eq_mul, mul_one, map_smul, he]
  }

end FDRep
