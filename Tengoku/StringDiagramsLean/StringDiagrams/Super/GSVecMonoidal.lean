import Tengoku.StringDiagramsLean.StringDiagrams.Super.GSVec
import Tengoku.StringDiagramsLean.StringDiagrams.Super.GradedMonoidal
import Tengoku.StringDiagramsLean.StringDiagrams.Super.MonoidalPi
import Tengoku.Seed.LinearAlgebra.DirectSum.TensorProduct
import Tengoku.Seed.Algebra.Module.Submodule.Bilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The graded monoidal supercategory of graded superspaces

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (before
Definition 6.1): the tensor product of graded superspaces, `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`.

* `GradedSuperspace.tensorObj V W`: the tensor product of superspaces `V ⊗ W` (of
  `StringDiagrams.Super.SVec`, with the Koszul sign rule) with the grading
  `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ` (`GradedSuperspace.tensorDeg`). That this is a grading, i.e.
  that `V ⊗ W` is the internal direct sum of these submodules, is proved via the projections
  `V ⊗ W → V ⊗ W` onto `(V ⊗ W)ₙ` obtained from `V ⊗ W ≅ ⨁_{(r,s)} Vᵣ ⊗ Wₛ`
  (`GradedSuperspace.tensorProj`, `GradedSuperspace.isInternal_tensorDeg`).
* `GradedSuperspace.unit`: the unit `k`, in degree `0` and even parity.
* With the whiskerings, associator and unitors of `SVec k`, which preserve degrees,
  `GSVec k` is a monoidal supercategory (`GSVec.instMonoidalSupercategory`) and a graded
  monoidal supercategory (`GSVec.instGradedMonoidalSupercategory`); its underlying category
  `GradedSupercategory.GUnderlying k (GSVec k)` is the paper's monoidal category `GSVec̲` of
  graded superspaces and even linear maps of degree zero. The symmetric braiding (that of
  `SVec k`, of degree zero), and the symmetric monoidal structure of `GSVec̲`, are in
  `StringDiagrams.Super.GSVecBraided`.
* `GSVec k` is a monoidal Π-supercategory with `π := Π k` and `ζ : Π k → k` the identity
  function (`GSVec.instMonoidalPiSupercategory`, the graded analogue of Example 1.13(i) for
  `A = k`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory TensorProduct

universe u

variable {k : Type u} [CommRing k]

namespace GradedSuperspace

variable (V W : GradedSuperspace k)

/-! ## The grading of `V ⊗ W` -/

/-- The submodule `Vᵣ ⊗ Wₛ` of `V ⊗ W`.-/
def tensorPiece (rs : ℤ × ℤ) : Submodule k (V.toSVec ⊗[k] W.toSVec) :=
  Submodule.map₂ (TensorProduct.mk k V.toSVec W.toSVec) (V.deg rs.1) (W.deg rs.2)

/-- The homogeneous component `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`.-/
def tensorDeg (n : ℤ) : Submodule k (V.toSVec ⊗[k] W.toSVec) :=
  ⨆ (rs : ℤ × ℤ) (_ : rs.1 + rs.2 = n), V.tensorPiece W rs

theorem tmul_mem_tensorDeg {r s : ℤ} {v : V.toSVec} {w : W.toSVec} (hv : v ∈ V.deg r)
    (hw : w ∈ W.deg s) : v ⊗ₜ w ∈ V.tensorDeg W (r + s) :=
  Submodule.mem_iSup_of_mem (r, s)
    (Submodule.mem_iSup_of_mem rfl (Submodule.apply_mem_map₂ _ hv hw))

/-- `(V ⊗ W)ₙ` is spanned by the `v ⊗ w` with `v ∈ Vᵣ`, `w ∈ Wₛ`, `r + s = n`.-/
theorem tensorDeg_le_iff {n : ℤ} {S : Submodule k (V.toSVec ⊗[k] W.toSVec)} :
    V.tensorDeg W n ≤ S ↔
      ∀ (r s : ℤ), r + s = n → ∀ v ∈ V.deg r, ∀ w ∈ W.deg s, v ⊗ₜ w ∈ S :=
  ⟨fun h _ _ hrs _ hv _ hw => h (hrs ▸ tmul_mem_tensorDeg V W hv hw),
    fun h => iSup₂_le fun rs hrs => Submodule.map₂_le.2 fun v hv w hw => h rs.1 rs.2 hrs v hv w hw⟩

/-- The projection of `V ⊗ W` onto `(V ⊗ W)ₙ`, through `V ⊗ W ≅ ⨁_{(r,s)} Vᵣ ⊗ Wₛ`.-/
def tensorProj (n : ℤ) : V.toSVec ⊗[k] W.toSVec →ₗ[k] V.toSVec ⊗[k] W.toSVec :=
  letI := V.degreeDecomposition
  letI := W.degreeDecomposition
  DirectSum.toModule k (ℤ × ℤ) (V.toSVec ⊗[k] W.toSVec) (fun rs =>
      if rs.1 + rs.2 = n then TensorProduct.map (V.deg rs.1).subtype (W.deg rs.2).subtype else 0) ∘ₗ
    (TensorProduct.directSum k k (fun r => V.deg r) (fun s => W.deg s)).toLinearMap ∘ₗ
      TensorProduct.map (DirectSum.decomposeLinearEquiv V.deg).toLinearMap
        (DirectSum.decomposeLinearEquiv W.deg).toLinearMap

theorem tensorProj_tmul (n r s : ℤ) {v : V.toSVec} {w : W.toSVec} (hv : v ∈ V.deg r)
    (hw : w ∈ W.deg s) : V.tensorProj W n (v ⊗ₜ w) = if r + s = n then v ⊗ₜ w else 0 := by
  let := V.degreeDecomposition
  let := W.degreeDecomposition
  have hv' : DirectSum.decompose V.deg v = DirectSum.lof k ℤ (fun r => V.deg r) r ⟨v, hv⟩ :=
    DirectSum.decompose_of_mem V.deg hv
  have hw' : DirectSum.decompose W.deg w = DirectSum.lof k ℤ (fun s => W.deg s) s ⟨w, hw⟩ :=
    DirectSum.decompose_of_mem W.deg hw
  simp only [tensorProj, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, hv', hw', TensorProduct.directSum_lof_tmul_lof,
    DirectSum.toModule_lof]
  split_ifs
  · simp
  · rfl

theorem tensorPiece_le_eqLocus (n : ℤ) (rs : ℤ × ℤ) (h : rs.1 + rs.2 = n) :
    V.tensorPiece W rs ≤ LinearMap.eqLocus (V.tensorProj W n) LinearMap.id :=
  Submodule.map₂_le.2 fun v hv w hw => LinearMap.mem_eqLocus.2 (by
    rw [TensorProduct.mk_apply, tensorProj_tmul V W n rs.1 rs.2 hv hw, ite_eq_left h]; rfl)

theorem tensorPiece_le_ker (n : ℤ) (rs : ℤ × ℤ) (h : rs.1 + rs.2 ≠ n) :
    V.tensorPiece W rs ≤ LinearMap.ker (V.tensorProj W n) :=
  Submodule.map₂_le.2 fun v hv w hw => LinearMap.mem_ker.2 (by
    rw [TensorProduct.mk_apply, tensorProj_tmul V W n rs.1 rs.2 hv hw, ite_eq_right h])

theorem tensorProj_of_mem {n : ℤ} {x : V.toSVec ⊗[k] W.toSVec} (hx : x ∈ V.tensorDeg W n) :
    V.tensorProj W n x = x :=
  LinearMap.mem_eqLocus.1
    ((iSup₂_le fun rs hrs => tensorPiece_le_eqLocus V W n rs hrs : V.tensorDeg W n ≤ _) hx)

theorem tensorProj_of_mem_ne {m n : ℤ} (h : m ≠ n) {x : V.toSVec ⊗[k] W.toSVec}
    (hx : x ∈ V.tensorDeg W m) : V.tensorProj W n x = 0 :=
  LinearMap.mem_ker.1 ((iSup₂_le fun rs hrs =>
    tensorPiece_le_ker V W n rs fun e => h (hrs.symm.trans e) : V.tensorDeg W m ≤ _) hx)

theorem iSupIndep_tensorDeg : iSupIndep (V.tensorDeg W) :=
  iSupIndep_of_projections _ (V.tensorProj W)
    (fun n => iSup₂_le fun rs hrs => tensorPiece_le_eqLocus V W n rs hrs)
    (fun n _ hmn => iSup₂_le fun rs hrs =>
      tensorPiece_le_ker V W n rs fun h => hmn (hrs.symm.trans h))

theorem sgn_mem {b : ZMod 2} {n : ℤ} {v : V.toSVec} (hv : v ∈ V.deg n) : V.toSVec.sgn b v ∈ V.deg n := by
  rw [SVec.sgn_apply]
  exact Submodule.add_mem _ (V.proj_mem 0 hv) (Submodule.smul_mem _ _ (V.proj_mem 1 hv))

/-- The unit graded superspace `k`, in degree `0` and even parity.-/
def unit : GradedSuperspace k where
  toSVec := SVec.unit
  deg n := if n = 0 then ⊤ else ⊥
  isInternal_deg := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro i
      by_cases hi : i = 0
      · subst hi
        refine Disjoint.mono_right (iSup₂_le fun j hj => ?_) disjoint_bot_right
        rw [ite_eq_right hj]
      · rw [ite_eq_right hi]; exact disjoint_bot_left
    · exact le_antisymm le_top (le_iSup_of_le 0 (by rw [ite_eq_left rfl]))
  odd_mem {n v} _ := by
    change (0 : k) ∈ _
    exact Submodule.zero_mem _

@[simp] theorem unit_toSVec : (unit : GradedSuperspace k).toSVec = SVec.unit := rfl

theorem unit_deg (n : ℤ) : (unit : GradedSuperspace k).deg n = if n = 0 then ⊤ else ⊥ := rfl

theorem mem_unit_deg_zero (r : (unit : GradedSuperspace k).toSVec) :
    r ∈ (unit : GradedSuperspace k).deg 0 := by
  rw [unit_deg, ite_eq_left rfl]; trivial

theorem eq_zero_of_mem_unit_deg {n : ℤ} (hn : n ≠ 0) {r : (unit : GradedSuperspace k).toSVec}
    (hr : r ∈ (unit : GradedSuperspace k).deg n) : r = 0 := by
  rwa [unit_deg, ite_eq_right hn, Submodule.mem_bot] at hr

/-! ## The whiskerings and coherence maps preserve degrees -/

variable {V W}

end GradedSuperspace

/-! ## The monoidal supercategory `GSVec` -/

namespace GSVec

open GradedSuperspace GradedSubcategory

/-- The unit object `k`.-/
abbrev unit : GSVec k := of GradedSuperspace.unit

end GSVec

end StringDiagrams

end
