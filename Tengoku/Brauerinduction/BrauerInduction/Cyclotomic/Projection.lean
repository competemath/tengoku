import Tengoku.Brauerinduction.BrauerInduction.Cyclotomic.IntegralCharacterRing
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Ring
import Tengoku.Brauerinduction.BrauerInduction.Background.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projection from cyclotomic to integral character coefficients

This file constructs Bernstein's additive coefficient projection and packages
its action on class functions.

First, `exists_projection_of_primitive` proves that a primitive element of a
finite free `ℤ`-module admits a `ℤ`-linear projection to `ℤ` sending that
element to `1`. Applied to `ClassFun.Lambda k G`, this yields a chosen additive
map `nu : Lambda k G →+ ℤ` with `nu 1 = 1`.

The auxiliary function `nu_ext` extends this projection to all of `k` by zero
outside `Lambda k G`. It is used only on arguments known to lie in the
cyclotomic coefficient ring, where it is additive and compatible with integer
scalars.

Finally, `nuStar` applies `nu_ext` to coordinates in an irreducible-character
basis. On functions with cyclotomic coordinates it is additive, `ℤ`-linear,
and fixes representation characters. The map `nuStarLinear` restricts this
construction to a linear map from
`ClassFun.IntegralCyclotomicCharacterRing k G` to
`ClassFun.CharacterRing k G`.
-/

namespace BrauerInduction.Cyclotomic

/--
In a finitely generated free `ℤ`-module, every primitive element admits a
linear projection to `ℤ` sending it to `1`.

Here “primitive” means that if `v = m • x`, then `m` is a unit of `ℤ`.
@isnad1 id=ex.1h2v.s7.0195cdb1fee8 from=translated src=- shape=4fa6de28 vocab=48f6d65f
-/
lemma exists_projection_of_primitive {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (v : M) (h_prim : ∀ (m : ℤ) (x : M), m • x = v → IsUnit m) :
    ∃ ν : M →ₗ[ℤ] ℤ, ν v = 1 := by
  let eval_v : (M →ₗ[ℤ] ℤ) →ₗ[ℤ] ℤ := {
    toFun := fun f => f v
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl
  }
  let I := LinearMap.range eval_v
  haveI : Submodule.IsPrincipal I := inferInstance
  obtain ⟨d, hd⟩ : ∃ d, Submodule.span ℤ {d} = I :=
    ⟨Submodule.IsPrincipal.generator I, Submodule.IsPrincipal.span_singleton_generator I⟩
  let ι := Module.Free.ChooseBasisIndex ℤ M
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ M
  let b := Module.Free.chooseBasis ℤ M
  have h_coord_in : ∀ i, b.coord i v ∈ I := by
    intro i
    exact LinearMap.mem_range.mpr ⟨b.coord i, rfl⟩
  have h_w : ∀ i, ∃ w_i : ℤ, b.coord i v = d * w_i := by
    intro i
    have h1 := h_coord_in i
    rw [← hd] at h1
    have h2 := Submodule.mem_span_singleton.mp h1
    obtain ⟨y, hy⟩ := h2
    use y
    rw [← hy, smul_eq_mul, mul_comm]
  choose w hw using h_w
  let W_repr : ι →₀ ℤ := ∑ i, Finsupp.single i (w i)
  let W := b.repr.symm W_repr
  have h_W_repr_i : ∀ i, W_repr i = w i := by
    intro i
    have h_eval : W_repr i = ∑ j, (Finsupp.single j (w j)) i := by
      exact Finsupp.finsetSum_apply Finset.univ (fun j => Finsupp.single j (w j)) i
    rw [h_eval]
    rw [Finset.sum_eq_single i]
    · exact Finsupp.single_eq_same
    · intro j _ hj
      exact Finsupp.single_eq_of_ne hj.symm
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have h_dW : d • W = v := by
    apply b.repr.injective
    ext i
    have h_lhs : b.repr (d • W) i = d * w i := by
      simp only [map_zsmul, Finsupp.coe_smul, Pi.smul_apply,
        Int.zsmul_eq_mul, mul_eq_mul_left_iff]
      rw [LinearEquiv.apply_symm_apply]
      rw [h_W_repr_i i]
      simp only [true_or]
    rw [h_lhs]
    have h_cw := hw i
    exact h_cw.symm
  have hd_unit : IsUnit d := h_prim d W h_dW
  have h_1_in : (1 : ℤ) ∈ I := by
    rw [← hd, Submodule.mem_span_singleton]
    obtain ⟨u, hu⟩ := hd_unit
    use ↑(u⁻¹)
    rw [← hu, smul_eq_mul]
    exact Units.inv_mul u
  obtain ⟨nu_lin, h_nu_one⟩ := LinearMap.mem_range.mp h_1_in
  use nu_lin
  exact h_nu_one

section LambdaProjection
/-!
## Projection on cyclotomic coefficients

This section constructs the additive projection `nu : Lambda k G →+ ℤ` and
its auxiliary extension `nu_ext : k → k`.
-/

variable {G : Type v} [Group G] [Finite G]
variable {k : Type u} [Field k] [CharZero k]

end LambdaProjection

section CharacterCoefficientProjection

/-!
## Projection on class-function coefficients

This section fixes an irreducible-character basis and applies `nu_ext` to the
coordinates of a class function. The resulting map `nuStar` fixes characters
of finite-dimensional representations. On the integral cyclotomic character
ring, it is packaged as the `ℤ`-linear map `nuStarLinear` with codomain
`ClassFun.CharacterRing k G`.
-/

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G]

end CharacterCoefficientProjection

end BrauerInduction.Cyclotomic
