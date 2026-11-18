import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKerHopf
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfTower
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open Function

universe u v

namespace HopfAlgebra
export _root_.HopfAlgebra (faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem)
namespace OrderMultiplicativity
open _root_.HopfAlgebra

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
variable (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
variable (S : Subalgebra k H)

/--
@isnad1 id=eq.0h3v.s9.57c4e2db9d56 from=translated src=- shape=9e6ea946 vocab=2feb42fa
-/
theorem counit_algebraMap (c : k) : Coalgebra.counit (R := k) (algebraMap k H c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one]

include k in
/--
@isnad1 id=nontrivi.0h2v.s6.d4881d839cea from=translated src=- shape=18f8e485 vocab=2d07fd81
-/
theorem nontrivial_H : Nontrivial H :=
  ⟨⟨0, 1, fun h => zero_ne_one (by
    have := congrArg (Coalgebra.counit (R := k) (A := H)) h
    rwa [map_zero, Bialgebra.counit_one] at this)⟩⟩

def εS : ↥S →ₐ[k] k := (Bialgebra.counitAlgHom k H).comp S.val

/--
@isnad1 id=eq.0h4v.s10.ef24435a657d from=translated src=- shape=7c340b9d vocab=d9bf26cd
-/
theorem εS_apply (x : ↥S) : εS S x = Coalgebra.counit (R := k) (x : H) := rfl

def mS : Ideal ↥S := RingHom.ker (εS S)

/--
@isnad1 id=iff.0h4v.s11.4e2254f6f7e8 from=translated src=- shape=37210751 vocab=e8125fcb
-/
theorem mem_mS {x : ↥S} : x ∈ mS S ↔ Coalgebra.counit (R := k) (x : H) = 0 := RingHom.mem_ker

/--
@isnad1 id=eq.0h3v.s11.aae55988c699 from=translated src=- shape=b7e3e258 vocab=2fc74d18
-/
theorem map_mS_eq :
    (mS S).map (algebraMap (↥S) H) =
      Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0} := by
  change Ideal.span _ = Ideal.span _
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_mS S).1 hy⟩
  · rintro ⟨hxS, hx⟩
    exact ⟨⟨x, hxS⟩, (mem_mS S).2 hx, rfl⟩

include hH in

/--
@isnad1 id=islocalr.1h3v.s9.e91db2b9855f from=translated src=- shape=aa2aa910 vocab=8ad21b60
-/
theorem isLocalRing_S : IsLocalRing ↥S := by
  haveI : Nontrivial H := nontrivial_H (k := k)
  haveI : Nontrivial ↥S := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h : ((0 : ↥S) : H) = 1)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hnil : ∀ y : ↥S, Coalgebra.counit (R := k) (y : H) = 0 → IsNilpotent y := fun y hy => by
    obtain ⟨N, hN⟩ := hH (y : H) hy
    exact ⟨N, Subtype.ext (by rw [SubmonoidClass.coe_pow, hN]; rfl)⟩
  by_cases hx : Coalgebra.counit (R := k) (x : H) = 0
  · exact Or.inr (hnil x hx).isUnit_one_sub
  · left
    have hn : IsNilpotent (x - algebraMap k (↥S) (Coalgebra.counit (R := k) (x : H))) := hnil _ (by
      rw [AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, map_sub, counit_algebraMap, sub_self])
    have hu : IsUnit (algebraMap k (↥S) (Coalgebra.counit (R := k) (x : H))) :=
      (isUnit_iff_ne_zero.2 hx).map _
    have := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    rwa [add_sub_cancel] at this

/--
@isnad1 id=eq.0h5v.s11.02c559a94422 from=translated src=- shape=6a8c4fc4 vocab=9e7a94ae
-/
theorem finrank_quotient_eq_card {ι : Type*} [Fintype ι] (b : Module.Basis ι (↥S) H) :
    Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) =
      Fintype.card ι := by
  classical
  set J : Ideal H := Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0} with hJdef

  let T : H →ₗ[k] (ι → k) :=
    { toFun := fun h i => εS S (b.repr h i)
      map_add' := fun u v => by
        funext i
        simp only [map_add, Finsupp.coe_add, Pi.add_apply]
      map_smul' := fun c u => by
        funext i
        rw [RingHom.id_apply, Pi.smul_apply, ← IsScalarTower.algebraMap_smul (↥S) c u, map_smul,
          Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, AlgHom.commutes, smul_eq_mul,
          Algebra.algebraMap_self_apply] }
  have hT : ∀ h i, T h i = εS S (b.repr h i) := fun h i => rfl

  have hTsurj : Function.Surjective T := fun c => by
    refine ⟨∑ i, algebraMap k (↥S) (c i) • b i, funext fun i => ?_⟩
    rw [hT, map_sum, Finset.sum_apply']
    simp_rw [map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i), AlgHom.commutes, Algebra.algebraMap_self_apply]

  have hJS : (mS S • (⊤ : Submodule (↥S) H)) = J.restrictScalars (↥S) := by
    rw [Ideal.smul_top_eq_map, map_mS_eq]
  have hker : LinearMap.ker T = J.restrictScalars k := by
    have hJk : J.restrictScalars k = (mS S • (⊤ : Submodule (↥S) H)).restrictScalars k := by
      rw [hJS, Submodule.restrictScalars_restrictScalars]
    rw [hJk]
    ext h
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    constructor
    · intro hh
      rw [← b.sum_repr h]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      exact (mem_mS S).2 (by have := congrFun hh i; rwa [hT, εS_apply] at this)
    · intro hh
      funext i
      rw [hT, Pi.zero_apply]
      refine Submodule.smul_induction_on hh (fun m hm u _ => ?_) (fun u v hu hv => ?_)
      · rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul,
          show εS S m = 0 from hm, zero_mul]
      · rw [map_add, Finsupp.coe_add, Pi.add_apply, map_add, hu, hv, add_zero]
  have e : (H ⧸ J) ≃ₗ[k] (ι → k) :=
    (Submodule.Quotient.restrictScalarsEquiv k J).symm ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hker.symm) ≪≫ₗ T.quotKerEquivOfSurjective hTsurj
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]

include hH in

/--
@isnad1 id=eq.3h3v.s12.4e2853bc92e7 from=translated src=- shape=54fc6e8c vocab=e07427c8
-/
theorem main
    (hΔ : ∀ x ∈ S, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ S, ∃ b ∈ S, t = a ⊗ₜ[k] b})
    (hSant : ∀ x ∈ S, antipode k x ∈ S) :
    Module.finrank k H =
      Module.finrank k S *
        Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) := by
  haveI : IsLocalRing ↥S := isLocalRing_S hH S
  haveI : Module.FaithfullyFlat (↥S) H :=
    HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem S hΔ hSant
  haveI : Module.Finite (↥S) H := Module.Finite.of_restrictScalars_finite k (↥S) H
  haveI : Module.Free (↥S) H := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis (↥S) H
  haveI : Fintype (Module.Free.ChooseBasisIndex (↥S) H) := Fintype.ofFinite _
  rw [finrank_quotient_eq_card S b, ← Module.finrank_eq_card_basis b,
    Module.finrank_mul_finrank k (↥S) H]

end HopfAlgebra.OrderMultiplicativity

/--
@isnad1 id=eq.3h3v.s12.4e2853bc92e7 from=translated src=- shape=54fc6e8c vocab=e07427c8
-/
theorem solution
    (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
    (S : Subalgebra k H)
    (hΔ : ∀ x ∈ S, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H | ∃ a ∈ S, ∃ b ∈ S, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ S, HopfAlgebra.antipode k x ∈ S) :
    Module.finrank k H =
      Module.finrank k S *
        Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) :=
  HopfAlgebra.OrderMultiplicativity.main hH S hΔ hS
