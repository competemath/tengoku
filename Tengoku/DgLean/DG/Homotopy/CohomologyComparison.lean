import Tengoku.Seed.Algebra.Homology.ConcreteCategory
import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
import Tengoku.DgLean.DG.Homotopy.Forget
import Tengoku.DgLean.DG.Module.Cohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohomology of a dg module and homology of its underlying cochain complex

For a dg `R`-algebra `A` and a dg `A`-module `M`, the cohomology `DG.cohomology M n` (defined
as `Zⁿ(M) ⧸ Bⁿ(M)`) is identified with Mathlib's homology of the underlying cochain complex
`(DG.DGModuleCat.forget R A).obj M` of `R`-modules:

* `DG.DGModuleCat.cohomologyAddEquiv R M n : cohomology M n ≃+ ((forget R A).obj M).homology n`,
  sending the class of a cocycle `z` to the homology class of the cycle `z`
  (`DG.DGModuleCat.cohomologyAddEquiv_mk`);
* naturality: `DG.DGModuleCat.cohomologyAddEquiv_naturality`, relating `DG.cohomology.map` and
  `HomologicalComplex.homologyMap`.

The isomorphism is obtained from Mathlib's explicit description of the homology of a short
complex of modules (`CategoryTheory.ShortComplex.moduleCatHomologyIso`).
-/

open scoped DG

open CategoryTheory

universe v u w

noncomputable section

namespace DG

namespace DGModuleCat

open DGModuleCat.Algebra

variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

section Object

variable (M : DGModuleCat.{v} A)

/-- The differential `(toComplex R M).d i j` is `d` for `j = i + 1`.
@isnad1 id=eq.1h6v.s10.b0696ec58b19 from=translated src=- shape=b4e13faa vocab=3b756b8e
-/
theorem toComplex_d_apply {i j : ℤ} (h : i + 1 = j) (x : DGModule.gradingSubmodule R A M i) :
    (Subtype.val ((toComplex R M).d i j x) : M) = d (x : M) := by
  subst h
  rw [toComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cocycles of degree `n` of `M` are the kernel of the differential of the short complex
`(toComplex R M).sc n`.-/
def cocyclesAddEquiv (n : ℤ) :
    cocycles M n ≃+ LinearMap.ker ((toComplex R M).sc n).g.hom where
  toFun z := ⟨⟨z, (cocycles.mem_grading z : _)⟩, Subtype.ext (by
    rw [ZeroMemClass.coe_zero]
    exact (toComplex_d_apply R M (CochainComplex.next ℤ n).symm _).trans (cocycles.d_eq_zero z))⟩
  invFun y := ⟨y.1.1, y.1.2,
    (toComplex_d_apply R M (CochainComplex.next ℤ n).symm y.1).symm.trans
      (congrArg Subtype.val y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem prev_add_one (n : ℤ) : (ComplexShape.up ℤ).prev n + 1 = n := by
  rw [CochainComplex.prev]; omega

/-- Under `DG.DGModuleCat.cocyclesAddEquiv`, the coboundaries correspond to the image of the
map `X (n - 1) → ker (d : X n → X (n + 1))`.
@isnad1 id=iff.0h5v.s16.83bb5c346f85 from=translated src=- shape=f0d99f38 vocab=9c711e77
-/
theorem mem_map_cocyclesAddEquiv_iff (n : ℤ) (y : LinearMap.ker ((toComplex R M).sc n).g.hom) :
    y ∈ ((coboundaries M n).addSubgroupOf (cocycles M n)).map
      (cocyclesAddEquiv R M n).toAddMonoidHom ↔
      y ∈ LinearMap.range ((toComplex R M).sc n).moduleCatToCycles := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨m, hm, hmz⟩ := AddSubgroup.mem_addSubgroupOf.mp hz
    refine ⟨⟨m, ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
    · change m ∈ grading _
      rwa [CochainComplex.prev]
    · exact (toComplex_d_apply R M (prev_add_one n) _).trans hmz
  · rintro ⟨⟨x, hx⟩, rfl⟩
    refine ⟨(cocyclesAddEquiv R M n).symm (((toComplex R M).sc n).moduleCatToCycles ⟨x, hx⟩),
      AddSubgroup.mem_addSubgroupOf.mpr ⟨x, ?_, ?_⟩, (cocyclesAddEquiv R M n).apply_symm_apply _⟩
    · change x ∈ grading _ at hx
      rwa [CochainComplex.prev] at hx
    · exact (toComplex_d_apply R M (prev_add_one n) ⟨x, hx⟩).symm

/-- The comparison `Hⁿ(M) ≃+ Hⁿ(toComplex R M)` between the cohomology of a dg module and the
homology of its underlying cochain complex of `R`-modules.-/
def cohomologyAddEquiv (n : ℤ) : cohomology M n ≃+ ((forget R A).obj M).homology n :=
  (QuotientAddGroup.congr _ _ (cocyclesAddEquiv R M n) (AddSubgroup.ext fun y =>
      (mem_map_cocyclesAddEquiv_iff R M n y).trans Iff.rfl)).trans
    (((toComplex R M).sc n).moduleCatHomologyIso.symm.toLinearEquiv.toAddEquiv)

set_option backward.isDefEq.respectTransparency false in
/-- `DG.DGModuleCat.cohomologyAddEquiv` sends the class of a cocycle to the homology class of
the corresponding cycle of the underlying cochain complex.
@isnad1 id=eq.0h5v.s13.c14cc6cdebd1 from=translated src=- shape=53a2bfde vocab=eed5cc71
-/
theorem cohomologyAddEquiv_mk (n : ℤ) (z : cocycles M n) :
    cohomologyAddEquiv R M n (cohomology.mk M n z) =
      (forget₂ (ModuleCat R) Ab).map (((forget R A).obj M).homologyπ n)
        (((forget R A).obj M).cyclesMk
          (⟨z, cocycles.mem_grading z⟩ : DGModule.gradingSubmodule R A M n) (n + 1)
          (CochainComplex.next ℤ n)
          (Subtype.ext ((toComplex_d_apply R M rfl _).trans (cocycles.d_eq_zero z)))) := by
  change ((toComplex R M).sc n).moduleCatHomologyIso.inv
    (((toComplex R M).sc n).moduleCatLeftHomologyData.π (cocyclesAddEquiv R M n z)) = _
  rw [← ShortComplex.moduleCatCyclesIso_inv_π_apply]
  change ((toComplex R M).sc n).homologyπ _ = ((toComplex R M).sc n).homologyπ _
  congr 1
  apply (ModuleCat.mono_iff_injective ((toComplex R M).iCycles n)).1 inferInstance
  change ((toComplex R M).sc n).iCycles _ = _
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
  exact (HomologicalComplex.i_cyclesMk (toComplex R M) _ _ _ _).symm

end Object

section Naturality

variable {M N : DGModuleCat.{v} A} (f : M ⟶ N)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `Hⁿ(M) ≃+ Hⁿ(toComplex R M)` is natural in `M`.
@isnad1 id=eq.0h7v.s13.0a1bda5570a1 from=translated src=- shape=5d34c77d vocab=197e9cc4
-/
theorem cohomologyAddEquiv_naturality (n : ℤ) (x : cohomology M n) :
    cohomologyAddEquiv R N n (cohomology.map f.hom n x) =
      HomologicalComplex.homologyMap ((forget R A).map f) n (cohomologyAddEquiv R M n x) := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [cohomology.map_mk, cohomologyAddEquiv_mk, cohomologyAddEquiv_mk]
    change _ = (((forget R A).obj M).homologyπ n ≫
      HomologicalComplex.homologyMap ((forget R A).map f) n) _
    rw [HomologicalComplex.homologyπ_naturality]
    change ((forget R A).obj N).homologyπ n _ = ((forget R A).obj N).homologyπ n _
    congr 1
    apply (ModuleCat.mono_iff_injective (((forget R A).obj N).iCycles n)).1 inferInstance
    change _ = (HomologicalComplex.cyclesMap ((forget R A).map f) n ≫
      ((forget R A).obj N).iCycles n) _
    rw [HomologicalComplex.cyclesMap_i]
    refine (HomologicalComplex.i_cyclesMk ((forget R A).obj N) _ _ _ _).trans ?_
    change _ = ((forget R A).map f).f n
      ((forget₂ (ModuleCat R) Ab).map (((forget R A).obj M).iCycles n) _)
    rw [HomologicalComplex.i_cyclesMk]
    rfl

/-- Naturality of `cohomologyAddEquiv`, as an equality of additive maps.
@isnad1 id=eq.0h6v.s13.dd03e084661c from=translated src=- shape=b689e4c2 vocab=b1a1b67d
-/
theorem cohomologyAddEquiv_comp_map (n : ℤ) :
    (cohomologyAddEquiv R N n).toAddMonoidHom.comp (cohomology.map f.hom n) =
      (HomologicalComplex.homologyMap ((forget R A).map f) n).hom.toAddMonoidHom.comp
        (cohomologyAddEquiv R M n).toAddMonoidHom :=
  AddMonoidHom.ext (cohomologyAddEquiv_naturality R f n)

end Naturality

end DGModuleCat

end DG
