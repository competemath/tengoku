import Tengoku.TdaLib.TDA.Persistence.ConstructibleBarcode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real-barcode reconstruction boundary cases

The grid has values -2 and 3. Two copies of `[1,2)` in the padded chain become
two real intervals `[-2,3)`, while `[2,3)` becomes the essential interval `[3,∞)`.
An empty grid has an empty barcode and a zero realization.
-/

set_option autoImplicit false

namespace TDA.Persistence.ConstructibleBarcodeExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible
open scoped ZeroObject

private def grid : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 2 => if i = 0 then (-2 : ℝ) else 3)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private def finiteBar : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩
private def essentialBar : FiniteInterval 3 := ⟨2, 3, by decide, by decide⟩
private def bars : Multiset (FiniteInterval 3) :=
  finiteBar ::ₘ finiteBar ::ₘ essentialBar ::ₘ 0

private theorem bars_birth_pos (I : FiniteInterval 3) (hI : I ∈ bars) : 0 < I.birth := by
  simp only [bars, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hI
  rcases hI with rfl | rfl | rfl <;> decide

private noncomputable def diagram : Diagram ℝ :=
  ofIndexBars grid grid.strictMono (reindexBarcode (Fin.succOrderEmb 2).toOrderHom bars)

/-- All three occurrences, including the repeated finite interval, survive unpadding.
@isnad1 id=eq.0h0v.s6.0d833430286b from=translated src=- shape=fa15e25c vocab=e9830335
-/
theorem all_occurrences_retained :
    (reindexBarcode (Fin.succOrderEmb 2).toOrderHom bars).card = 3 := by
  rw [RealBarcode.reindexBarcode_succ_card bars bars_birth_pos]
  rfl

/-- Exact real endpoints retain both finite copies and the essential tail.
@isnad1 id=eq.0h0v.s6.f19e10387fe9 from=translated src=- shape=6ab66bf8 vocab=0d0ae106
-/
theorem diagram_points : diagram.points =
    ((-2 : ℝ), ((3 : ℝ) : WithTop ℝ)) ::ₘ (-2, ((3 : ℝ) : WithTop ℝ)) ::ₘ (3, ⊤) ::ₘ 0 := by
  unfold diagram
  rw [RealBarcode.ofIndexBars_points]
  have hf := RealBarcode.restrictAlong_succ finiteBar (show 0 < finiteBar.birth by decide)
  have he := RealBarcode.restrictAlong_succ essentialBar (show 0 < essentialBar.birth by decide)
  simp only [reindexBarcode, bars,
    Multiset.filterMap_cons_some _ _ _ hf, Multiset.filterMap_cons_some _ _ _ he,
    Multiset.filterMap_zero, Multiset.map_cons, Multiset.map_zero]
  rfl

/-- The finite interval includes its birth and excludes its finite death.
@isnad1 id=and.0h0v.s6.75a0c122a614 from=translated src=- shape=dc450160 vocab=22e72b26
-/
theorem finite_boundary :
    RealBarcode.alive (-2, (3 : WithTop ℝ)) (-2) ∧
      ¬ RealBarcode.alive (-2, (3 : WithTop ℝ)) 3 := by
  constructor
  · exact ⟨le_rfl, WithTop.coe_lt_coe.mpr (by norm_num)⟩
  · intro h
    exact (lt_irrefl (3 : WithTop ℝ)) h.2

/-- The essential interval remains alive at every parameter at or above its birth.
@isnad1 id=alive.1h1v.s5.a2e58b17bac0 from=translated src=- shape=9c17f132 vocab=fcff1217
-/
theorem essential_tail (t : ℝ) (ht : 3 ≤ t) : RealBarcode.alive (3, ⊤) t :=
  ⟨ht, WithTop.coe_lt_top t⟩

/-- Multiplicity is two at the finite pair and one at the essential pair.
@isnad1 id=and.0h0v.s7.7e857c1362ef from=translated src=- shape=63a40073 vocab=3be66d9a
-/
theorem duplicate_multiplicity :
    diagram.points.count (-2, (3 : WithTop ℝ)) = 2 ∧
      diagram.points.count (3, ⊤) = 1 := by
  classical
  rw [diagram_points]
  norm_num

private noncomputable def inputModule : PModule.{0,0,0} ℚ ℝ :=
  reindex (cellIndex grid) (barcodeModule (k := ℚ) bars)

private theorem initial_zero : IsZero ((barcodeModule (k := ℚ) bars).obj 0) := by
  have : Subsingleton ((barcodeModule (k := ℚ) bars).obj 0) := by
    change Subsingleton (∀ i : Fin bars.toList.length, FiniteInterval.fiber (k := ℚ) (bars.toList.get i) 0)
    refine ⟨fun x y => funext (fun i => ?_)⟩
    apply Subtype.ext
    have hb := bars_birth_pos _ (Multiset.mem_toList.mp (List.get_mem bars.toList i))
    have hn : ¬ (bars.toList.get i).alive 0 := by
      simp only [FiniteInterval.alive, Fin.val_zero]
      omega
    have hx : (x i : ℚ) = 0 := by
      simpa only [FiniteInterval.fiber, ite_eq_right hn, Submodule.mem_bot] using (x i).property
    have hy : (y i : ℚ) = 0 := by
      simpa only [FiniteInterval.fiber, ite_eq_right hn, Submodule.mem_bot] using (y i).property
    exact hx.trans hy.symm
  exact ModuleCat.isZero_of_subsingleton _

private theorem input_constructible : IsConstructible grid inputModule :=
  isConstructible_reindex grid _ initial_zero

private theorem critical_finite (i : Fin 2) : FiniteDimensional ℚ (inputModule.obj (grid i)) := by
  change FiniteDimensional ℚ ((barcodeModule (k := ℚ) bars).obj (cellIndex grid (grid i)))
  infer_instance

/-- The explicit interval transport gives a natural isomorphism to the expected endpoints.-/
noncomputable def explicitBarcodeIso : inputModule ≅ RealBarcode.realize (k := ℚ) diagram :=
  RealBarcode.barcodePullbackIso grid bars bars_birth_pos

/-- The full finite-decomposition/reconstruction composition applies using only critical fibers.-/
noncomputable def reconstructedBarcodeIso : inputModule ≅
    RealBarcode.realize (k := ℚ) (moduleDiagram grid inputModule critical_finite) :=
  barcodeRealizationIso grid inputModule input_constructible critical_finite

private def emptyGrid : Fin 0 ↪o ℝ :=
  ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun {i} => Fin.elim0 i⟩

private noncomputable def zeroModule : PModule.{0,0,0} ℚ ℝ :=
  (Functor.const ℝ).obj (0 : ModuleCat ℚ)

/-- The empty-grid diagram has no endpoints, so no nonexistent critical value is selected.
@isnad1 id=eq.0h0v.s8.28d068131144 from=translated src=- shape=bf64fdf2 vocab=88b225bd
-/
theorem empty_diagram : (moduleDiagram emptyGrid zeroModule (fun i => Fin.elim0 i)).points = 0 :=
  moduleDiagram_empty_grid emptyGrid zeroModule

/-- The empty-grid realization is a zero module.
@isnad1 id=iszero.0h0v.s8.c5c8c48246bc from=translated src=- shape=60e5da98 vocab=3f9fd392
-/
theorem empty_realization : IsZero (RealBarcode.realize (k := ℚ)
    (moduleDiagram emptyGrid zeroModule (fun i => Fin.elim0 i))) :=
  RealBarcode.realize_isZero_of_points_eq_zero _ empty_diagram

/-- The capstone also constructs its natural isomorphism for an empty critical sequence.-/
noncomputable def emptyBarcodeIso : zeroModule ≅ RealBarcode.realize (k := ℚ)
    (moduleDiagram emptyGrid zeroModule (fun i => Fin.elim0 i)) :=
  barcodeRealizationIso emptyGrid zeroModule
    ((isConstructible_empty_iff emptyGrid zeroModule).mpr (fun _ => isZero_zero (ModuleCat ℚ)))
    (fun i => Fin.elim0 i)

end TDA.Persistence.ConstructibleBarcodeExamples
