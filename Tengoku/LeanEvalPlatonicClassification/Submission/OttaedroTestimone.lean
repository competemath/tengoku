import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Fondamenta
import Tengoku.LeanEvalPlatonicClassification.Submission.TetraedroStadio2
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasferimento
import Tengoku.LeanEvalPlatonicClassification.Submission.CuboTestimone

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FASE 1B, N3 — L'OTTAEDRO (3,4), stadio 1 + faccetta regolare (18 lug, notte).
I sei vertici ±eᵢ sulla sfera unitaria; la faccia (+,+,+) è il triangolo
{o0,o1,o2}, esposta da lX+lY+lZ, ruotata dal 3-ciclo diagonale rotDiag
(ereditato dal cubo: la stessa rotazione serve entrambi i solidi).
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Real Set Metric Tengoku.LeanEvalPlatonicClassification.FiniteConvexPolytope PlatoniciL3
open scoped RealInnerProductSpace

noncomputable section

def _root_.Tengoku.LeanEvalPlatonicClassification.o0 : E3 := WithLp.toLp 2 ![1, 0, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.o1 : E3 := WithLp.toLp 2 ![0, 1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.o2 : E3 := WithLp.toLp 2 ![0, 0, 1]
def _root_.Tengoku.LeanEvalPlatonicClassification.o3 : E3 := WithLp.toLp 2 ![-1, 0, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.o4 : E3 := WithLp.toLp 2 ![0, -1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.o5 : E3 := WithLp.toLp 2 ![0, 0, -1]

open Classical in
def _root_.Tengoku.LeanEvalPlatonicClassification.verticiOtta : Finset E3 := {o0, o1, o2, o3, o4, o5}

theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_verticiOtta_iff {v : E3} : v ∈ verticiOtta ↔
    v = o0 ∨ v = o1 ∨ v = o2 ∨ v = o3 ∨ v = o4 ∨ v = o5 := by
  simp [verticiOtta]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.norm_vertici_otta : ∀ v ∈ verticiOtta, ‖v‖ = 1 := by
  intro v hv
  rcases mem_verticiOtta_iff.mp hv with h | h | h | h | h | h <;> subst h
  · show ‖(WithLp.toLp 2 ![(1:ℝ), 0, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), 1, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), 0, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), 0, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), -1, 0] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(0:ℝ), 0, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num

/-- L'OTTAEDRO (stadio 1): politopo convesso finito legittimo.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.ottaedro : FiniteConvexPolytope E3 where
  vertices := verticiOtta
  nonempty := ⟨o0, by simp [verticiOtta]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiOtta : Set E3) ⊆ Metric.sphere 0 1 := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici_otta v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 1 _ hV).symm

/-! ## Il funzionale della faccia (+,+,+) e i suoi valori -/

theorem _root_.Tengoku.LeanEvalPlatonicClassification.lS_vertici_otta : (lX + lY + lZ) o0 = 1 ∧ (lX + lY + lZ) o1 = 1 ∧
    (lX + lY + lZ) o2 = 1 ∧ (lX + lY + lZ) o3 = -1 ∧
    (lX + lY + lZ) o4 = -1 ∧ (lX + lY + lZ) o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [add_apply]; norm_num [lX, lY, lZ, o0, o1,
      o2, o3, o4, o5]) <;>
    rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.facciaOtta : Finset E3 := {o0, o1, o2}

/-- Il triangolo della faccia (+,+,+).-/
def _root_.Tengoku.LeanEvalPlatonicClassification.T₀ : Set E3 := convexHull ℝ (facciaOtta : Set E3)

theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiOtta :
    {x ∈ (verticiOtta : Set E3) | (lX + lY + lZ) x = 1}
      = (facciaOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · simp [facciaOtta]
    · simp [facciaOtta]
    · simp [facciaOtta]
    · exfalso; rw [lS_vertici_otta.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lS_vertici_otta.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lS_vertici_otta.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
      simpa [facciaOtta] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨by simp [verticiOtta], lS_vertici_otta.1⟩
    · exact ⟨by simp [verticiOtta], lS_vertici_otta.2.1⟩
    · exact ⟨by simp [verticiOtta], lS_vertici_otta.2.2.1⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.toSet_otta_le : ∀ z ∈ ottaedro.toSet, (lX + lY + lZ) z ≤ 1 := by
  intro z hz
  have hsub : (verticiOtta : Set E3) ⊆ {w : E3 | (lX + lY + lZ) w ≤ 1} := by
    intro w hw
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_ofPred_eq] <;>
      first
        | (rw [lS_vertici_otta.1])
        | (rw [lS_vertici_otta.2.1])
        | (rw [lS_vertici_otta.2.2.1])
        | (rw [lS_vertici_otta.2.2.2.1]; norm_num)
        | (rw [lS_vertici_otta.2.2.2.2.1]; norm_num)
        | (rw [lS_vertici_otta.2.2.2.2.2]; norm_num)
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear (lX + lY + lZ).toLinearMap) 1) hz

theorem _root_.Tengoku.LeanEvalPlatonicClassification.T₀_ge_uno : ∀ z ∈ T₀, 1 ≤ (lX + lY + lZ) z := by
  intro z hz
  have hsub : (facciaOtta : Set E3) ⊆ {w : E3 | 1 ≤ (lX + lY + lZ) w} := by
    intro w hw
    have hcasi : w = o0 ∨ w = o1 ∨ w = o2 := by
      simpa [facciaOtta] using hw
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [Set.mem_ofPred_eq]
    · rw [lS_vertici_otta.1]
    · rw [lS_vertici_otta.2.1]
    · rw [lS_vertici_otta.2.2.1]
  exact convexHull_min hsub
    (convex_halfSpace_ge (LinearMap.isLinear (lX + lY + lZ).toLinearMap) 1) hz

/-! ## Il ciclo di rotDiag sulla faccia e la regolarità -/

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotDiag_o : rotDiag o0 = o1 ∧ rotDiag o1 = o2 ∧ rotDiag o2 = o0 ∧
    rotDiag o3 = o4 ∧ rotDiag o4 = o5 ∧ rotDiag o5 = o3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [rotDiag, cicloCoord, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrLeft])

theorem _root_.Tengoku.LeanEvalPlatonicClassification.o0_ne_o1 : o0 ≠ o1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [o0, o1] at this

theorem _root_.Tengoku.LeanEvalPlatonicClassification.o0_ne_o2 : o0 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [o0, o2] at this

theorem _root_.Tengoku.LeanEvalPlatonicClassification.o1_ne_o2 : o1 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [o1, o2] at this

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotDiag_preserva_T₀ : (⇑rotDiag.toAffineIsometryEquiv) '' T₀ = T₀ := by
  show (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑rotDiag.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑rotDiag.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull rotDiag.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑rotDiag.toAffineIsometryEquiv) u = rotDiag u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [rotDiag_o.1, rotDiag_o.2.1, rotDiag_o.2.2.1] <;>
      simp [facciaOtta]
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o2 := by
      simpa [facciaOtta] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o2, by simp [facciaOtta], rotDiag_o.2.2.1⟩
    · exact ⟨o0, by simp [facciaOtta], rotDiag_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], rotDiag_o.2.1⟩

/-! ## Lo span 2D della faccia -/

noncomputable def _root_.Tengoku.LeanEvalPlatonicClassification.dOtta1 : E3 := o0 - o1
noncomputable def _root_.Tengoku.LeanEvalPlatonicClassification.dOtta2 : E3 := o0 - o2

theorem _root_.Tengoku.LeanEvalPlatonicClassification.indep_dOtta : LinearIndependent ℝ ![dOtta1, dOtta2] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
    simp [dOtta2, o0, o2] at this
  · intro a h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
    simp [dOtta1, dOtta2, o0, o1, o2] at this

theorem _root_.Tengoku.LeanEvalPlatonicClassification.T₀_nonempty : T₀.Nonempty :=
  ⟨o0, subset_convexHull ℝ _ (by simp [facciaOtta])⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.o0_mem_T₀ : o0 ∈ T₀ :=
  subset_convexHull ℝ _ (by simp [facciaOtta])

/-! ## La dimensione globale e il lemma dei vertici esposti -/

theorem _root_.Tengoku.LeanEvalPlatonicClassification.ottaedro_finrank :
    Module.finrank ℝ (vectorSpan ℝ (ottaedro.vertices : Set E3)) = 3 := by
  have ho0 : o0 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho1 : o1 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho2 : o2 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho3 : o3 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho4 : o4 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have ho5 : o5 ∈ (ottaedro.vertices : Set E3) := by simp [ottaedro, verticiOtta]
  have htop : vectorSpan ℝ (ottaedro.vertices : Set E3) = ⊤ := by
    apply le_antisymm le_top
    rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    all_goals simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      SetLike.mem_coe]
    · show EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (ottaedro.vertices : Set E3)
      have hd : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (o0 -ᵥ o3) := by
        ext j <;> fin_cases j <;>
          simp [o0, o3, PiLp.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ ho0 ho3)
    · show EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (ottaedro.vertices : Set E3)
      have hd : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (o1 -ᵥ o4) := by
        ext j <;> fin_cases j <;>
          simp [o1, o4, PiLp.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ ho1 ho4)
    · show EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (ottaedro.vertices : Set E3)
      have hd : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (o2 -ᵥ o5) := by
        ext j <;> fin_cases j <;>
          simp [o2, o5, PiLp.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ ho2 ho5)
  rw [htop, finrank_top]
  simp [E3]

open Classical in
/-- Ogni faccia esposta dell'ottaedro è l'hull dei vertici che contiene.-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.exposedFace_eq_convexHull_vertices_otta {F : Set E3}
    (hF : ottaedro.IsFace F) :
    F = convexHull ℝ ((ottaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := ottaedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact ottaedro.toSet :=
    (ottaedro.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ ottaedro.toSet.extremePoints ℝ) ↔
      x ∈ ottaedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← ottaedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((ottaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

/-! ## I valori di un funzionale generico sui sei vertici -/

section ClassOtta

variable (l : E3 →L[ℝ] ℝ)

theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_o0 : l o0 = compL l 0 := by
  show l (WithLp.toLp 2 ![1, 0, 0]) = _
  rw [l_toLp3]; ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_o1 : l o1 = compL l 1 := by
  show l (WithLp.toLp 2 ![0, 1, 0]) = _
  rw [l_toLp3]; ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_o2 : l o2 = compL l 2 := by
  show l (WithLp.toLp 2 ![0, 0, 1]) = _
  rw [l_toLp3]; ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_o3 : l o3 = -compL l 0 := by
  show l (WithLp.toLp 2 ![-1, 0, 0]) = _
  rw [l_toLp3]; ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_o4 : l o4 = -compL l 1 := by
  show l (WithLp.toLp 2 ![0, -1, 0]) = _
  rw [l_toLp3]; ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_o5 : l o5 = -compL l 2 := by
  show l (WithLp.toLp 2 ![0, 0, -1]) = _
  rw [l_toLp3]; ring

end ClassOtta

/-! ## Le azioni dei segni sui vertici dell'ottaedro -/

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_o : segnoX o0 = o3 ∧ segnoX o1 = o1 ∧ segnoX o2 = o2 ∧
    segnoX o3 = o0 ∧ segnoX o4 = o4 ∧ segnoX o5 = o5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoX, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrRight])

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoY_o : segnoY o0 = o0 ∧ segnoY o1 = o4 ∧ segnoY o2 = o2 ∧
    segnoY o3 = o3 ∧ segnoY o4 = o1 ∧ segnoY o5 = o5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoY, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrRight])

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoZ_o : segnoZ o0 = o0 ∧ segnoZ o1 = o1 ∧ segnoZ o2 = o5 ∧
    segnoZ o3 = o3 ∧ segnoZ o4 = o4 ∧ segnoZ o5 = o2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoZ, o0, o1, o2, o3, o4, o5,
        LinearIsometryEquiv.piLpCongrRight])

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_overtset :
    (⇑segnoX) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [segnoX_o.1, segnoX_o.2.1, segnoX_o.2.2.1, segnoX_o.2.2.2.1,
        segnoX_o.2.2.2.2.1, segnoX_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o3, by simp [verticiOtta], segnoX_o.2.2.2.1⟩
    · exact ⟨o1, by simp [verticiOtta], segnoX_o.2.1⟩
    · exact ⟨o2, by simp [verticiOtta], segnoX_o.2.2.1⟩
    · exact ⟨o0, by simp [verticiOtta], segnoX_o.1⟩
    · exact ⟨o4, by simp [verticiOtta], segnoX_o.2.2.2.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], segnoX_o.2.2.2.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoY_overtset :
    (⇑segnoY) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [segnoY_o.1, segnoY_o.2.1, segnoY_o.2.2.1, segnoY_o.2.2.2.1,
        segnoY_o.2.2.2.2.1, segnoY_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o0, by simp [verticiOtta], segnoY_o.1⟩
    · exact ⟨o4, by simp [verticiOtta], segnoY_o.2.2.2.2.1⟩
    · exact ⟨o2, by simp [verticiOtta], segnoY_o.2.2.1⟩
    · exact ⟨o3, by simp [verticiOtta], segnoY_o.2.2.2.1⟩
    · exact ⟨o1, by simp [verticiOtta], segnoY_o.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], segnoY_o.2.2.2.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoZ_overtset :
    (⇑segnoZ) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [segnoZ_o.1, segnoZ_o.2.1, segnoZ_o.2.2.1, segnoZ_o.2.2.2.1,
        segnoZ_o.2.2.2.2.1, segnoZ_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o0, by simp [verticiOtta], segnoZ_o.1⟩
    · exact ⟨o1, by simp [verticiOtta], segnoZ_o.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], segnoZ_o.2.2.2.2.2⟩
    · exact ⟨o3, by simp [verticiOtta], segnoZ_o.2.2.2.1⟩
    · exact ⟨o4, by simp [verticiOtta], segnoZ_o.2.2.2.2.1⟩
    · exact ⟨o2, by simp [verticiOtta], segnoZ_o.2.2.1⟩

/-- La permutazione dei vertici dell'ottaedro passa alla composizione.-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.overtset_trans (f g : E3 ≃ₗᵢ[ℝ] E3)
    (hf : (⇑f) '' (verticiOtta : Set E3) = (verticiOtta : Set E3))
    (hg : (⇑g) '' (verticiOtta : Set E3) = (verticiOtta : Set E3)) :
    (⇑(f.trans g)) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  have hcomp : (⇑(f.trans g)) '' (verticiOtta : Set E3)
      = (⇑g) '' ((⇑f) '' (verticiOtta : Set E3)) := by
    rw [← Set.image_comp]
    rfl
  rw [hcomp, hf, hg]

/-- Se un'isometria lineare permuta i vertici dell'ottaedro, la versione
affine preserva il corpo.-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.preserva_toSet_otta (g : E3 ≃ₗᵢ[ℝ] E3)
    (hv : (⇑g) '' (verticiOtta : Set E3) = (verticiOtta : Set E3)) :
    (⇑g.toAffineIsometryEquiv) '' ottaedro.toSet = ottaedro.toSet := by
  show (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiOtta : Set E3))
    = convexHull ℝ (verticiOtta : Set E3)
  have haff : (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiOtta : Set E3))
      = convexHull ℝ ((⇑g.toAffineIsometryEquiv) '' (verticiOtta : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff, show (⇑g.toAffineIsometryEquiv) '' (verticiOtta : Set E3)
    = (verticiOtta : Set E3) from hv]

/-! ## Le otto facce dell'ottaedro e le immagini di T₀ -/

def _root_.Tengoku.LeanEvalPlatonicClassification.fmpp : Finset E3 := {o3, o1, o2}
def _root_.Tengoku.LeanEvalPlatonicClassification.fpmp : Finset E3 := {o0, o4, o2}
def _root_.Tengoku.LeanEvalPlatonicClassification.fppm : Finset E3 := {o0, o1, o5}
def _root_.Tengoku.LeanEvalPlatonicClassification.fmmp : Finset E3 := {o3, o4, o2}
def _root_.Tengoku.LeanEvalPlatonicClassification.fmpm : Finset E3 := {o3, o1, o5}
def _root_.Tengoku.LeanEvalPlatonicClassification.fpmm : Finset E3 := {o0, o4, o5}
def _root_.Tengoku.LeanEvalPlatonicClassification.fmmm : Finset E3 := {o3, o4, o5}

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sXY_o : (segnoX.trans segnoY) o0 = o3 ∧ (segnoX.trans segnoY) o1 = o4
    ∧ (segnoX.trans segnoY) o2 = o2 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoY (segnoX o0) = o3
    rw [segnoX_o.1, segnoY_o.2.2.2.1]
  · show segnoY (segnoX o1) = o4
    rw [segnoX_o.2.1, segnoY_o.2.1]
  · show segnoY (segnoX o2) = o2
    rw [segnoX_o.2.2.1, segnoY_o.2.2.1]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sXZ_o : (segnoX.trans segnoZ) o0 = o3 ∧ (segnoX.trans segnoZ) o1 = o1
    ∧ (segnoX.trans segnoZ) o2 = o5 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoZ (segnoX o0) = o3
    rw [segnoX_o.1, segnoZ_o.2.2.2.1]
  · show segnoZ (segnoX o1) = o1
    rw [segnoX_o.2.1, segnoZ_o.2.1]
  · show segnoZ (segnoX o2) = o5
    rw [segnoX_o.2.2.1, segnoZ_o.2.2.1]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sYZ_o : (segnoY.trans segnoZ) o0 = o0 ∧ (segnoY.trans segnoZ) o1 = o4
    ∧ (segnoY.trans segnoZ) o2 = o5 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoZ (segnoY o0) = o0
    rw [segnoY_o.1, segnoZ_o.1]
  · show segnoZ (segnoY o1) = o4
    rw [segnoY_o.2.1, segnoZ_o.2.2.2.2.1]
  · show segnoZ (segnoY o2) = o5
    rw [segnoY_o.2.2.1, segnoZ_o.2.2.1]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sXYZ_o : ((segnoX.trans segnoY).trans segnoZ) o0 = o3
    ∧ ((segnoX.trans segnoY).trans segnoZ) o1 = o4
    ∧ ((segnoX.trans segnoY).trans segnoZ) o2 = o5 := by
  refine ⟨?_, ?_, ?_⟩
  · show segnoZ ((segnoX.trans segnoY) o0) = o3
    rw [sXY_o.1, segnoZ_o.2.2.2.1]
  · show segnoZ ((segnoX.trans segnoY) o1) = o4
    rw [sXY_o.2.1, segnoZ_o.2.2.2.2.1]
  · show segnoZ ((segnoX.trans segnoY) o2) = o5
    rw [sXY_o.2.2, segnoZ_o.2.2.1]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_f : segnoX o0 = o3 ∧ segnoX o1 = o1 ∧ segnoX o2 = o2 :=
  ⟨segnoX_o.1, segnoX_o.2.1, segnoX_o.2.2.1⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoY_f : segnoY o0 = o0 ∧ segnoY o1 = o4 ∧ segnoY o2 = o2 :=
  ⟨segnoY_o.1, segnoY_o.2.1, segnoY_o.2.2.1⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoZ_f : segnoZ o0 = o0 ∧ segnoZ o1 = o1 ∧ segnoZ o2 = o5 :=
  ⟨segnoZ_o.1, segnoZ_o.2.1, segnoZ_o.2.2.1⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_T₀ : (⇑segnoX.toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmpp : Set E3) := by
  show (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑segnoX.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull segnoX.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoX.toAffineIsometryEquiv) u = segnoX u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [segnoX_f.1, segnoX_f.2.1, segnoX_f.2.2] <;>
      simp [fmpp]
  · intro hz
    have hcasi : z = o3 ∨ z = o1 ∨ z = o2 := by
      simpa [fmpp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], segnoX_f.1⟩
    · exact ⟨o1, by simp [facciaOtta], segnoX_f.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], segnoX_f.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoY_T₀ : (⇑segnoY.toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fpmp : Set E3) := by
  show (⇑segnoY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑segnoY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑segnoY.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull segnoY.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoY.toAffineIsometryEquiv) u = segnoY u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [segnoY_f.1, segnoY_f.2.1, segnoY_f.2.2] <;>
      simp [fpmp]
  · intro hz
    have hcasi : z = o0 ∨ z = o4 ∨ z = o2 := by
      simpa [fpmp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], segnoY_f.1⟩
    · exact ⟨o1, by simp [facciaOtta], segnoY_f.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], segnoY_f.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoZ_T₀ : (⇑segnoZ.toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fppm : Set E3) := by
  show (⇑segnoZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑segnoZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑segnoZ.toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull segnoZ.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoZ.toAffineIsometryEquiv) u = segnoZ u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [segnoZ_f.1, segnoZ_f.2.1, segnoZ_f.2.2] <;>
      simp [fppm]
  · intro hz
    have hcasi : z = o0 ∨ z = o1 ∨ z = o5 := by
      simpa [fppm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], segnoZ_f.1⟩
    · exact ⟨o1, by simp [facciaOtta], segnoZ_f.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], segnoZ_f.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sXY_T₀ : (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmmp : Set E3) := by
  show (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑(segnoX.trans segnoY).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull (segnoX.trans segnoY).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑(segnoX.trans segnoY).toAffineIsometryEquiv) u = (segnoX.trans segnoY) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sXY_o.1, sXY_o.2.1, sXY_o.2.2] <;>
      simp [fmmp]
  · intro hz
    have hcasi : z = o3 ∨ z = o4 ∨ z = o2 := by
      simpa [fmmp] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sXY_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sXY_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sXY_o.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sXZ_T₀ : (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmpm : Set E3) := by
  show (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull (segnoX.trans segnoZ).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑(segnoX.trans segnoZ).toAffineIsometryEquiv) u = (segnoX.trans segnoZ) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sXZ_o.1, sXZ_o.2.1, sXZ_o.2.2] <;>
      simp [fmpm]
  · intro hz
    have hcasi : z = o3 ∨ z = o1 ∨ z = o5 := by
      simpa [fmpm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sXZ_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sXZ_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sXZ_o.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sYZ_T₀ : (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fpmm : Set E3) := by
  show (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull (segnoY.trans segnoZ).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑(segnoY.trans segnoZ).toAffineIsometryEquiv) u = (segnoY.trans segnoZ) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sYZ_o.1, sYZ_o.2.1, sYZ_o.2.2] <;>
      simp [fpmm]
  · intro hz
    have hcasi : z = o0 ∨ z = o4 ∨ z = o5 := by
      simpa [fpmm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sYZ_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sYZ_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sYZ_o.2.2⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.sXYZ_T₀ : (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' T₀
    = convexHull ℝ (fmmm : Set E3) := by
  show (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3)) = _
  have haff : (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' (convexHull ℝ (facciaOtta : Set E3))
      = convexHull ℝ ((⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) '' (facciaOtta : Set E3)) :=
    AffineMap.image_convexHull ((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑((segnoX.trans segnoY).trans segnoZ).toAffineIsometryEquiv) u = ((segnoX.trans segnoY).trans segnoZ) u := rfl
    rw [hcv]
    have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
      simpa [facciaOtta] using hu
    rcases hcasi with h | h | h <;> subst h <;>
      simp only [sXYZ_o.1, sXYZ_o.2.1, sXYZ_o.2.2] <;>
      simp [fmmm]
  · intro hz
    have hcasi : z = o3 ∨ z = o4 ∨ z = o5 := by
      simpa [fmmm] using hz
    rcases hcasi with h | h | h <;> subst h
    · exact ⟨o0, by simp [facciaOtta], sXYZ_o.1⟩
    · exact ⟨o1, by simp [facciaOtta], sXYZ_o.2.1⟩
    · exact ⟨o2, by simp [facciaOtta], sXYZ_o.2.2⟩

/-! ## LA CLASSIFICAZIONE DELLE FACCETTE DELL'OTTAEDRO -/

set_option maxHeartbeats 3200000 in
/-- Ogni faccetta dell'ottaedro è una delle otto facce triangolari.-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.facet_classification_otta {F : Set E3} (hF : ottaedro.IsFacet F) :
    F = convexHull ℝ (facciaOtta : Set E3)
    ∨ F = convexHull ℝ (fmpp : Set E3) ∨ F = convexHull ℝ (fpmp : Set E3)
    ∨ F = convexHull ℝ (fppm : Set E3) ∨ F = convexHull ℝ (fmmp : Set E3)
    ∨ F = convexHull ℝ (fmpm : Set E3) ∨ F = convexHull ℝ (fpmm : Set E3)
    ∨ F = convexHull ℝ (fmmm : Set E3) := by
  classical
  obtain ⟨l, hl⟩ := hF.1.1 hF.1.2
  have hFS := exposedFace_eq_convexHull_vertices_otta hF.1
  set S : Finset E3 := ottaedro.vertices.filter (· ∈ F) with hSdef
  have hspanS : vectorSpan ℝ (S : Set E3)
      = vectorSpan ℝ (convexHull ℝ (S : Set E3)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have hd : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hdF := hF.2
    rw [hFS, ← hspanS] at hdF
    exact hdF
  have hSsub : (S : Set E3) ⊆ (ottaedro.vertices : Set E3) := by
    intro u hu
    have : u ∈ ottaedro.vertices.filter (· ∈ F) := by exact_mod_cast hu
    exact_mod_cast Finset.filter_subset _ _ this
  have hcrit : ∀ u ∈ (ottaedro.vertices : Set E3),
      (u ∈ (S : Set E3) ↔ ∀ w ∈ (ottaedro.vertices : Set E3), l w ≤ l u) := by
    intro u hu
    constructor
    · intro huS w hw
      have huF : u ∈ F :=
        (Finset.mem_filter.mp (by exact_mod_cast huS)).2
      rw [hl] at huF
      exact huF.2 w (subset_convexHull ℝ _ hw)
    · intro hargmax
      have huF : u ∈ F := by
        rw [hl]
        refine ⟨subset_convexHull ℝ _ hu, ?_⟩
        intro y hy
        exact convexHull_min hargmax
          (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) (l u)) hy
      show u ∈ ((ottaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3)
      exact_mod_cast Finset.mem_filter.mpr ⟨by exact_mod_cast hu, huF⟩
  rcases lt_trichotomy (compL l 0) 0 with hx | hx | hx
  · -- a0 N
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a1 N
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (N,N,N)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o4, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o1] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o2] at h
            linarith
          · simp
          · simp
          · simp
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmmm]
        · intro u hu
          have hcasi : u = o3 ∨ u = o4 ∨ u = o5 := by
            simpa [fmmm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o4
          · exact hm_o5
      · -- (N,N,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (N,N,P)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o4, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o1] at h
            linarith
          · simp
          · simp
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o5] at h
            linarith
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmmp]
        · intro u hu
          have hcasi : u = o3 ∨ u = o4 ∨ u = o2 := by
            simpa [fmmp] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o4
          · exact hm_o2
    · -- a1 Z
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (N,Z,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (N,Z,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o3} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (N,Z,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o1] at h
              linarith
            · simp
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 P
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (N,P,N)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o1, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o2] at h
            linarith
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o4] at h
            linarith
          · simp
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmpm]
        · intro u hu
          have hcasi : u = o3 ∨ u = o1 ∨ u = o5 := by
            simpa [fmpm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o1
          · exact hm_o5
      · -- (N,P,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o3, o1} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o0] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o2] at h
              linarith
            · simp
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o4] at h
              linarith
            · exfalso
              have h := hmax o3 (by simp [ottaedro, verticiOtta])
              rw [l_o3, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (N,P,P)
        refine Or.inr (Or.inl ?_)
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o3, o1, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o0] at h
            linarith
          · simp
          · simp
          · simp
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o4] at h
            linarith
          · exfalso
            have h := hmax o3 (by simp [ottaedro, verticiOtta])
            rw [l_o3, l_o5] at h
            linarith
        have hm_o3 : o3 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o3, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fmpp]
        · intro u hu
          have hcasi : u = o3 ∨ u = o1 ∨ u = o2 := by
            simpa [fmpp] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o3
          · exact hm_o1
          · exact hm_o2
  · -- a0 Z
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a1 N
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (Z,N,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o4, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o0] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o1] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o2] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o3] at h
              linarith
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (Z,N,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o4, o4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o0] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o1] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o2] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o3] at h
              linarith
            · simp
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (Z,N,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o4, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o0] at h
              linarith
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o1] at h
              linarith
            · simp
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o3] at h
              linarith
            · simp
            · exfalso
              have h := hmax o4 (by simp [ottaedro, verticiOtta])
              rw [l_o4, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 Z
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (Z,Z,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o5, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o0] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o1] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o2] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o3] at h
              linarith
            · exfalso
              have h := hmax o5 (by simp [ottaedro, verticiOtta])
              rw [l_o5, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (Z,Z,Z)
        exfalso
        have hSall : (S : Set E3) = (ottaedro.vertices : Set E3) := by
          apply Set.Subset.antisymm hSsub
          intro u hu
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h <;> subst h <;>
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h <;>
            simp only [l_o0, l_o1, l_o2, l_o3, l_o4, l_o5] <;>
            linarith
        rw [hSall, ottaedro_finrank] at hd
        omega
      · -- (Z,Z,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o2, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o0] at h
              linarith
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o1] at h
              linarith
            · simp
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o3] at h
              linarith
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o4] at h
              linarith
            · exfalso
              have h := hmax o2 (by simp [ottaedro, verticiOtta])
              rw [l_o2, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 P
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (Z,P,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o1, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o0] at h
              linarith
            · simp
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o2] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o3] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (Z,P,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o1, o1} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o0] at h
              linarith
            · simp
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o2] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o3] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o4] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (Z,P,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o1, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o0] at h
              linarith
            · simp
            · simp
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o3] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o4] at h
              linarith
            · exfalso
              have h := hmax o1 (by simp [ottaedro, verticiOtta])
              rw [l_o1, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
  · -- a0 P
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a1 N
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (P,N,N)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o4, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o1] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o2] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · simp
          · simp
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fpmm]
        · intro u hu
          have hcasi : u = o0 ∨ u = o4 ∨ u = o5 := by
            simpa [fpmm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o4
          · exact hm_o5
      · -- (P,N,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (P,N,P)
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o4, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o1] at h
            linarith
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o5] at h
            linarith
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o4, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o4 : o4 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o4} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fpmp]
        · intro u hu
          have hcasi : u = o0 ∨ u = o4 ∨ u = o2 := by
            simpa [fpmp] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o4
          · exact hm_o2
    · -- a1 Z
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (P,Z,N)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · simp
          have := span_coppia_le hsub
          omega)
      · -- (P,Z,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o0} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (P,Z,P)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o1] at h
              linarith
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
    · -- a1 P
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- (P,P,N)
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o1, o5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o2] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o4] at h
            linarith
          · simp
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o5} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o5 : o5 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [fppm]
        · intro u hu
          have hcasi : u = o0 ∨ u = o1 ∨ u = o5 := by
            simpa [fppm] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o1
          · exact hm_o5
      · -- (P,P,Z)
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {o0, o1} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
              h | h | h | h | h | h <;> subst h
            · simp
            · simp
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o2] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o3] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o4] at h
              linarith
            · exfalso
              have h := hmax o0 (by simp [ottaedro, verticiOtta])
              rw [l_o0, l_o5] at h
              linarith
          have := span_coppia_le hsub
          omega)
      · -- (P,P,P)
        refine Or.inl ?_
        rw [hFS]
        congr 1
        have hsub3 : (S : Set E3) ⊆ {o0, o1, o2} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h <;> subst h
          · simp
          · simp
          · simp
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o3] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o4] at h
            linarith
          · exfalso
            have h := hmax o0 (by simp [ottaedro, verticiOtta])
            rw [l_o0, l_o5] at h
            linarith
        have hm_o0 : o0 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o1, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · exact absurd (h ▸ hu) hno
            · simp [h]
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o1 : o1 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o2} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · exact absurd (h ▸ hu) hno
            · simp [h]
          have := span_coppia_le hp
          omega
        have hm_o2 : o2 ∈ (S : Set E3) := by
          by_contra hno
          have hp : (S : Set E3) ⊆ {o0, o1} := by
            intro u hu
            have hc := hsub3 hu
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (h ▸ hu) hno
          have := span_coppia_le hp
          omega
        apply Set.Subset.antisymm
        · intro u hu
          have hc := hsub3 hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          rcases hc with h | h | h <;> subst h <;> simp [facciaOtta]
        · intro u hu
          have hcasi : u = o0 ∨ u = o1 ∨ u = o2 := by
            simpa [facciaOtta] using hu
          rcases hcasi with h | h | h <;> subst h
          · exact hm_o0
          · exact hm_o1
          · exact hm_o2

/-! ## I funzionali delle facce, i loro semispazi e il polo nord -/

theorem _root_.Tengoku.LeanEvalPlatonicClassification.lX_o : lX o0 = 1 ∧ lX o1 = 0 ∧ lX o2 = 0 ∧ lX o3 = -1 ∧ lX o4 = 0
    ∧ lX o5 = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.lY_o : lY o0 = 0 ∧ lY o1 = 1 ∧ lY o2 = 0 ∧ lY o3 = 0 ∧ lY o4 = -1
    ∧ lY o5 = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.lZ_o : lZ o0 = 0 ∧ lZ o1 = 0 ∧ lZ o2 = 1 ∧ lZ o3 = 0 ∧ lZ o4 = 0
    ∧ lZ o5 = -1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def _root_.Tengoku.LeanEvalPlatonicClassification.fN1 : E3 →L[ℝ] ℝ := (lY + lZ) - lX
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fN1_o : fN1 o0 = -1 ∧ fN1 o1 = 1 ∧ fN1 o2 = 1 ∧ fN1 o3 = 1 ∧ fN1 o4 = -1 ∧ fN1 o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fN1, sub_apply,
      add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

def _root_.Tengoku.LeanEvalPlatonicClassification.fN2 : E3 →L[ℝ] ℝ := lZ - (lX + lY)
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fN2_o : fN2 o0 = -1 ∧ fN2 o1 = -1 ∧ fN2 o2 = 1 ∧ fN2 o3 = 1 ∧ fN2 o4 = 1 ∧ fN2 o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fN2, sub_apply,
      add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

def _root_.Tengoku.LeanEvalPlatonicClassification.fN3 : E3 →L[ℝ] ℝ := (lX + lZ) - lY
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fN3_o : fN3 o0 = 1 ∧ fN3 o1 = -1 ∧ fN3 o2 = 1 ∧ fN3 o3 = -1 ∧ fN3 o4 = 1 ∧ fN3 o5 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fN3, sub_apply,
      add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

def _root_.Tengoku.LeanEvalPlatonicClassification.fS0 : E3 →L[ℝ] ℝ := (lX + lY) - lZ
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fS0_o : fS0 o0 = 1 ∧ fS0 o1 = 1 ∧ fS0 o2 = -1 ∧ fS0 o3 = -1 ∧ fS0 o4 = -1 ∧ fS0 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS0, sub_apply,
      add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

def _root_.Tengoku.LeanEvalPlatonicClassification.fS1 : E3 →L[ℝ] ℝ := lY - (lX + lZ)
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fS1_o : fS1 o0 = -1 ∧ fS1 o1 = 1 ∧ fS1 o2 = -1 ∧ fS1 o3 = 1 ∧ fS1 o4 = -1 ∧ fS1 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS1, sub_apply,
      add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

def _root_.Tengoku.LeanEvalPlatonicClassification.fS2 : E3 →L[ℝ] ℝ := lX - (lY + lZ)
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fS2_o : fS2 o0 = 1 ∧ fS2 o1 = -1 ∧ fS2 o2 = -1 ∧ fS2 o3 = -1 ∧ fS2 o4 = 1 ∧ fS2 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS2, sub_apply,
      add_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

def _root_.Tengoku.LeanEvalPlatonicClassification.fS7 : E3 →L[ℝ] ℝ := (0 : E3 →L[ℝ] ℝ) - ((lX + lY) + lZ)

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fS7_o : fS7 o0 = -1 ∧ fS7 o1 = -1 ∧ fS7 o2 = -1 ∧ fS7 o3 = 1
    ∧ fS7 o4 = 1 ∧ fS7 o5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [fS7, sub_apply,
      add_apply, zero_apply]
     norm_num [lX_o.1, lX_o.2.1, lX_o.2.2.1, lX_o.2.2.2.1,
       lX_o.2.2.2.2.1, lX_o.2.2.2.2.2, lY_o.1, lY_o.2.1,
       lY_o.2.2.1, lY_o.2.2.2.1, lY_o.2.2.2.2.1, lY_o.2.2.2.2.2,
       lZ_o.1, lZ_o.2.1, lZ_o.2.2.1, lZ_o.2.2.2.1,
       lZ_o.2.2.2.2.1, lZ_o.2.2.2.2.2])

/-! ## Il fan del polo nord: σ4 e le quattro facce attorno a o2 -/

/-- La rotazione di π/2 attorno all'asse z: (x,y,z) ↦ (−y,x,z).-/
def _root_.Tengoku.LeanEvalPlatonicClassification.sigma4 : E3 ≃ₗᵢ[ℝ] E3 := scambioXY.trans segnoX

theorem _root_.Tengoku.LeanEvalPlatonicClassification.o3_ne_o2 : o3 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [o3, o2] at this

theorem _root_.Tengoku.LeanEvalPlatonicClassification.o4_ne_o2 : o4 ≠ o2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [o4, o2] at this

/-! ## IL FAN DEL POLO NORD: o2 è 4-ciclico -/

/-! ## Tutti i vertici sono 4-ciclici e IL TESTIMONE -/

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotDiag_overtset :
    (⇑rotDiag) '' (verticiOtta : Set E3) = (verticiOtta : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h <;> subst h <;>
      simp only [rotDiag_o.1, rotDiag_o.2.1, rotDiag_o.2.2.1,
        rotDiag_o.2.2.2.1, rotDiag_o.2.2.2.2.1, rotDiag_o.2.2.2.2.2] <;>
      simp [verticiOtta]
  · intro hz
    rcases mem_verticiOtta_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h <;> subst h
    · exact ⟨o2, by simp [verticiOtta], rotDiag_o.2.2.1⟩
    · exact ⟨o0, by simp [verticiOtta], rotDiag_o.1⟩
    · exact ⟨o1, by simp [verticiOtta], rotDiag_o.2.1⟩
    · exact ⟨o5, by simp [verticiOtta], rotDiag_o.2.2.2.2.2⟩
    · exact ⟨o3, by simp [verticiOtta], rotDiag_o.2.2.2.1⟩
    · exact ⟨o4, by simp [verticiOtta], rotDiag_o.2.2.2.2.1⟩
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
