import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card

set_option autoImplicit false

/--
@isnad1 id=and.3h5v.s9.006e5fb8fe0e from=translated src=- shape=2a135f6c vocab=0e39494a
-/
theorem solution
    {K : Type} [Field K] {D : Type} [Ring D] [Algebra K D]
    (hdiv : ∀ d : D, d ≠ 0 → IsUnit d)
    {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (hdim : Module.finrank K D = Fintype.card N)
    (ι : D →ₐ[K] Matrix N N K) (e₀ : N → K) (he₀ : e₀ ≠ 0) :
    Function.Bijective (fun d : D => (ι d).mulVec e₀) ∧
      ∀ T : Matrix N N K, (∀ d : D, T * ι d = ι d * T) →
        ∃ ξ : D, ∀ d : D, T.mulVec ((ι d).mulVec e₀) = (ι (d * ξ)).mulVec e₀ := by
  classical

  let f : D →ₗ[K] (N → K) :=
    { toFun := fun d => (ι d).mulVec e₀
      map_add' := fun x y => by
        simp only [map_add, Matrix.add_mulVec]
      map_smul' := fun c x => by
        simp only [map_smul, Matrix.smul_mulVec, RingHom.id_apply] }
  have hf : ∀ d : D, f d = (ι d).mulVec e₀ := fun _ => rfl

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    by_contra hne
    obtain ⟨u, rfl⟩ := hdiv d hne
    have h0 : (ι ((↑u⁻¹ : D) * (↑u : D))).mulVec e₀ = 0 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← hf (↑u : D), hd, Matrix.mulVec_zero]
    rw [Units.inv_mul, map_one, Matrix.one_mulVec] at h0
    exact he₀ h0

  have hpos : 0 < Module.finrank K D := by
    rw [hdim]; exact Fintype.card_pos
  haveI : Module.Finite K D := Module.finite_of_finrank_pos hpos
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdim, Module.finrank_fintype_fun_eq_card])).1 hinj
  refine ⟨⟨hinj, hsurj⟩, ?_⟩

  intro T hT
  obtain ⟨ξ, hξ⟩ := hsurj (T.mulVec e₀)
  refine ⟨ξ, fun d => ?_⟩
  rw [Matrix.mulVec_mulVec, hT d, ← Matrix.mulVec_mulVec, map_mul, ← Matrix.mulVec_mulVec,
    ← hf ξ, hξ]
