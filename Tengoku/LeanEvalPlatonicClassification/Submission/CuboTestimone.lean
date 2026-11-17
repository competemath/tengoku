import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Fondamenta
import Tengoku.LeanEvalPlatonicClassification.Submission.TetraedroStadio2
import Tengoku.LeanEvalPlatonicClassification.Submission.FacciaArgmax
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasferimento

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FASE 1B, N2 — IL CUBO, sviluppo import-based (stadio 1 portato + faccia
regolare). Le simmetrie sono permutazioni di coordinate con segni; la faccia
{x = 1} è esposta dal proiettore della prima coordinata, e l'argmax si
schiaccia sui 4 vertici della faccia via `faccia_argmax` (L3, certificato).
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Real Set Metric Tengoku.LeanEvalPlatonicClassification.FiniteConvexPolytope PlatoniciL3
open scoped RealInnerProductSpace

noncomputable section

/-! ## I vertici e il politopo (stadio 1, portato) -/

def _root_.Tengoku.LeanEvalPlatonicClassification.c0 : E3 := WithLp.toLp 2 ![1, 1, 1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c1 : E3 := WithLp.toLp 2 ![1, 1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c2 : E3 := WithLp.toLp 2 ![1, -1, 1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c3 : E3 := WithLp.toLp 2 ![1, -1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c4 : E3 := WithLp.toLp 2 ![-1, 1, 1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c5 : E3 := WithLp.toLp 2 ![-1, 1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c6 : E3 := WithLp.toLp 2 ![-1, -1, 1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c7 : E3 := WithLp.toLp 2 ![-1, -1, -1]

open Classical in
def _root_.Tengoku.LeanEvalPlatonicClassification.verticiCubo : Finset E3 := {c0, c1, c2, c3, c4, c5, c6, c7}

/--
@isnad1 id=iff.0h1v.s5.88cfdd5c7d41 from=translated src=- shape=4527c427 vocab=ec4d1828
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_verticiCubo_iff {v : E3} : v ∈ verticiCubo ↔
    v = c0 ∨ v = c1 ∨ v = c2 ∨ v = c3 ∨ v = c4 ∨ v = c5 ∨ v = c6 ∨ v = c7 := by
  simp [verticiCubo]

/--
@isnad1 id=eq.1h1v.s6.44cebfd3c3e2 from=translated src=- shape=3bc45c0e vocab=70835f9d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.norm_vertici_cubo : ∀ v ∈ verticiCubo, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  rcases mem_verticiCubo_iff.mp hv with h | h | h | h | h | h | h | h <;> subst h
  · show ‖(WithLp.toLp 2 ![(1:ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(1:ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(1:ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(1:ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · show ‖(WithLp.toLp 2 ![(-1:ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num

/-- IL TESTIMONE (stadio 1): il cubo è un politopo convesso finito legittimo.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.cubo : FiniteConvexPolytope E3 where
  vertices := verticiCubo
  nonempty := ⟨c0, by simp [verticiCubo]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiCubo : Set E3) ⊆ Metric.sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici_cubo v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 (Real.sqrt 3) _ hV).symm

/-! ## La rotazione della faccia {x = 1} -/

def _root_.Tengoku.LeanEvalPlatonicClassification.scambioYZ : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 1 2)

def _root_.Tengoku.LeanEvalPlatonicClassification.segnoY : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

/-- La rotazione di π/2 attorno all'asse x: (x, y, z) ↦ (x, −z, y).-/
def _root_.Tengoku.LeanEvalPlatonicClassification.rotFacciaX : E3 ≃ₗᵢ[ℝ] E3 := scambioYZ.trans segnoY

/--
@isnad1 id=eq.0h0v.s9.92ccc4880274 from=translated src=- shape=b764bacb vocab=504b064b
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotX_c0 : rotFacciaX c0 = c2 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c0, c2, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

/--
@isnad1 id=eq.0h0v.s9.062b65e2e7d2 from=translated src=- shape=b764bacb vocab=f9774894
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotX_c2 : rotFacciaX c2 = c3 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c2, c3, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

/--
@isnad1 id=eq.0h0v.s9.8ce54e427dae from=translated src=- shape=b764bacb vocab=80d3cbb1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotX_c3 : rotFacciaX c3 = c1 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c3, c1, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

/--
@isnad1 id=eq.0h0v.s9.a2e33f66df8e from=translated src=- shape=b764bacb vocab=e48c1497
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotX_c1 : rotFacciaX c1 = c0 := by
  ext j <;> fin_cases j <;>
    simp [rotFacciaX, scambioYZ, segnoY, c1, c0, Equiv.swap_apply_def,
      LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.piLpCongrRight]

/-- La versione affine della rotazione.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.rotAffX : E3 ≃ᵃⁱ[ℝ] E3 := rotFacciaX.toAffineIsometryEquiv

/--
@isnad1 id=eq.0h1v.s11.3ad6eff78c5b from=translated src=- shape=42ede9b0 vocab=637969f6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotAffX_apply (z : E3) : rotAffX z = rotFacciaX z := rfl

/-! ## La faccia {x = 1} e il suo ciclo -/

open Classical in
def _root_.Tengoku.LeanEvalPlatonicClassification.facciaX1 : Finset E3 := {c0, c2, c3, c1}

def _root_.Tengoku.LeanEvalPlatonicClassification.F₀ : Set E3 := convexHull ℝ (facciaX1 : Set E3)

/-- Le coordinate distinguono i vertici del ciclo.
@isnad1 id=ne.0h0v.s2.76fab73e5957 from=translated src=- shape=54c8eceb vocab=6f6dcbde
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c0_ne_c2 : c0 ≠ c2 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c0, c2] at this
  norm_num at this

/--
@isnad1 id=ne.0h0v.s2.cbe3c3940672 from=translated src=- shape=54c8eceb vocab=2008fdc0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c0_ne_c3 : c0 ≠ c3 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c0, c3] at this
  norm_num at this

/--
@isnad1 id=ne.0h0v.s2.f108ddc15eb4 from=translated src=- shape=54c8eceb vocab=ef3adae3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c0_ne_c1 : c0 ≠ c1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
  simp [c0, c1] at this
  norm_num at this

/--
@isnad1 id=ne.0h0v.s2.b98a03003d40 from=translated src=- shape=54c8eceb vocab=5c26e40f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c2_ne_c3 : c2 ≠ c3 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
  simp [c2, c3] at this
  norm_num at this

/--
@isnad1 id=ne.0h0v.s2.7e76d6a99f5e from=translated src=- shape=54c8eceb vocab=ad400783
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c2_ne_c1 : c2 ≠ c1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c2, c1] at this
  norm_num at this

/--
@isnad1 id=ne.0h0v.s2.697f8223b00d from=translated src=- shape=54c8eceb vocab=78a0c3e9
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c3_ne_c1 : c3 ≠ c1 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
  simp [c3, c1] at this
  norm_num at this

/-! ## L'esposizione della faccia {x = 1} e la regolarità -/

/-- Il proiettore della prima coordinata.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.lX : E3 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 3)

/--
@isnad1 id=and.0h0v.s11.fa3a03f6cc3b from=translated src=- shape=1c5cdd4d vocab=bbc8f943
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.lX_vertici : lX c0 = 1 ∧ lX c1 = 1 ∧ lX c2 = 1 ∧ lX c3 = 1 ∧
    lX c4 = -1 ∧ lX c5 = -1 ∧ lX c6 = -1 ∧ lX c7 = -1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- I vertici con lX = 1 sono esattamente quelli della faccia.
@isnad1 id=eq.0h0v.s8.de554e77655e from=translated src=- shape=a743ce6c vocab=7e5133fa
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiX : {x ∈ (verticiCubo : Set E3) | lX x = 1}
    = (facciaX1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · simp [facciaX1]
    · simp [facciaX1]
    · simp [facciaX1]
    · simp [facciaX1]
    · exfalso; rw [lX_vertici.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
      simpa [facciaX1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lX_vertici.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.1⟩

/-- Il corpo del cubo sta nel semispazio lX ≤ 1.
@isnad1 id=le.1h1v.s8.a730cff89584 from=translated src=- shape=450539c2 vocab=713be4c6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.toSet_le_uno : ∀ z ∈ cubo.toSet, lX z ≤ 1 := by
  intro z hz
  have hsub : (verticiCubo : Set E3) ⊆ {w : E3 | lX w ≤ 1} := by
    intro w hw
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [Set.mem_ofPred_eq] <;>
      first
        | (rw [lX_vertici.1])
        | (rw [lX_vertici.2.1])
        | (rw [lX_vertici.2.2.1])
        | (rw [lX_vertici.2.2.2.1])
        | (rw [lX_vertici.2.2.2.2.1]; norm_num)
        | (rw [lX_vertici.2.2.2.2.2.1]; norm_num)
        | (rw [lX_vertici.2.2.2.2.2.2.1]; norm_num)
        | (rw [lX_vertici.2.2.2.2.2.2.2]; norm_num)
  have hcx : Convex ℝ {w : E3 | lX w ≤ 1} :=
    convex_halfSpace_le (LinearMap.isLinear lX.toLinearMap) 1
  exact convexHull_min hsub hcx hz

/-- La faccia sta nel semispazio lX ≥ 1 (dunque lX = 1 su F₀).
@isnad1 id=le.1h1v.s8.944e653e6462 from=translated src=- shape=4ace406d vocab=9fbf3995
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_ge_uno : ∀ z ∈ F₀, 1 ≤ lX z := by
  intro z hz
  have hsub : (facciaX1 : Set E3) ⊆ {w : E3 | 1 ≤ lX w} := by
    intro w hw
    have hcasi : w = c0 ∨ w = c2 ∨ w = c3 ∨ w = c1 := by
      simpa [facciaX1] using hw
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [Set.mem_ofPred_eq]
    · rw [lX_vertici.1]
    · rw [lX_vertici.2.2.1]
    · rw [lX_vertici.2.2.2.1]
    · rw [lX_vertici.2.1]
  have hcx : Convex ℝ {w : E3 | 1 ≤ lX w} :=
    convex_halfSpace_ge (LinearMap.isLinear lX.toLinearMap) 1
  exact convexHull_min hsub hcx hz

/-- La rotazione preserva la faccia (a livello di hull).
@isnad1 id=eq.0h0v.s10.ffaf269f15e9 from=translated src=- shape=9139f438 vocab=01f7aa21
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotAffX_preserva_F₀ : (⇑rotAffX) '' F₀ = F₀ := by
  show (⇑rotAffX) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑rotAffX) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑rotAffX) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull rotAffX.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hcasi : y = c0 ∨ y = c2 ∨ y = c3 ∨ y = c1 := by
      simpa [facciaX1] using hy
    rcases hcasi with h | h | h | h <;> subst h <;>
      rw [rotAffX_apply] <;>
      first
        | (rw [rotX_c0]; simp [facciaX1])
        | (rw [rotX_c2]; simp [facciaX1])
        | (rw [rotX_c3]; simp [facciaX1])
        | (rw [rotX_c1]; simp [facciaX1])
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c3 ∨ z = c1 := by
      simpa [facciaX1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c1, by simp [facciaX1], by rw [rotAffX_apply, rotX_c1]⟩
    · exact ⟨c0, by simp [facciaX1], by rw [rotAffX_apply, rotX_c0]⟩
    · exact ⟨c2, by simp [facciaX1], by rw [rotAffX_apply, rotX_c2]⟩
    · exact ⟨c3, by simp [facciaX1], by rw [rotAffX_apply, rotX_c3]⟩

/-! ## Lo span bidimensionale e la faccetta regolare -/

/-- I due lati uscenti da c0.-/
noncomputable def _root_.Tengoku.LeanEvalPlatonicClassification.d1 : E3 := c0 - c2
noncomputable def _root_.Tengoku.LeanEvalPlatonicClassification.d2 : E3 := c0 - c1

/--
@isnad1 id=linearin.0h0v.s7.833ed06ff119 from=translated src=- shape=6fc31a08 vocab=c15c55d1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.indep_d : LinearIndependent ℝ ![d1, d2] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 2) h
    simp [d2, c0, c1] at this
  · intro a h
    have := congrArg (fun v : E3 => (WithLp.ofLp v) 1) h
    simp [d1, d2, c0, c1, c2] at this
    norm_num at this

/--
@isnad1 id=nonempty.0h0v.s1.cccc31389436 from=translated src=- shape=25b03439 vocab=82d171e2
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_nonempty : F₀.Nonempty :=
  ⟨c0, subset_convexHull ℝ _ (by simp [facciaX1])⟩

/--
@isnad1 id=mem.0h0v.s3.1531edb9f7b7 from=translated src=- shape=d1530203 vocab=ff4062de
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c0_mem_F₀ : c0 ∈ F₀ :=
  subset_convexHull ℝ _ (by simp [facciaX1])

/-! ## La dimensione globale del cubo e il lemma dei vertici esposti -/

/-- I vertici del cubo generano tutto lo spazio: span direzionale 3D.
@isnad1 id=eq.0h0v.s10.0139fbb54282 from=translated src=- shape=774ba165 vocab=7738448f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.cubo_finrank :
    Module.finrank ℝ (vectorSpan ℝ (cubo.vertices : Set E3)) = 3 := by
  have hc0 : c0 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc1 : c1 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc2 : c2 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have hc4 : c4 ∈ (cubo.vertices : Set E3) := by simp [cubo, verticiCubo]
  have htop : vectorSpan ℝ (cubo.vertices : Set E3) = ⊤ := by
    apply le_antisymm le_top
    rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    all_goals simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      SetLike.mem_coe]
    · show EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (cubo.vertices : Set E3)
      have hd : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (c0 -ᵥ c4) := by
        ext j <;> fin_cases j <;>
          simp [c0, c4, PiLp.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hc0 hc4)
    · show EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (cubo.vertices : Set E3)
      have hd : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (c0 -ᵥ c2) := by
        ext j <;> fin_cases j <;>
          simp [c0, c2, PiLp.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hc0 hc2)
    · show EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
        ∈ vectorSpan ℝ (cubo.vertices : Set E3)
      have hd : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
          = (2⁻¹ : ℝ) • (c0 -ᵥ c1) := by
        ext j <;> fin_cases j <;>
          simp [c0, c1, PiLp.single_apply] <;> norm_num
      rw [hd]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hc0 hc1)
  rw [htop, finrank_top]
  simp [E3]

open Classical in
/-- Ogni faccia esposta del cubo è l'hull dei vertici che contiene
(il pattern del tetraedro, parola per parola).
@isnad1 id=eq.1h1v.s8.9d2b0b99ea13 from=translated src=- shape=d419a73e vocab=4b3c76d3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.exposedFace_eq_convexHull_vertices_cubo {F : Set E3}
    (hF : cubo.IsFace F) :
    F = convexHull ℝ ((cubo.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := cubo.vertices.filter (· ∈ F)
  have hPcompact : IsCompact cubo.toSet :=
    (cubo.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ cubo.toSet.extremePoints ℝ) ↔
      x ∈ cubo.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← cubo.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((cubo.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

/-! ## Le sei simmetrie che portano la faccia {x=1} sulle sei facce -/

def _root_.Tengoku.LeanEvalPlatonicClassification.segnoX : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.scambioXY : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

def _root_.Tengoku.LeanEvalPlatonicClassification.scambioXZ : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 2)

/-- (x,y,z) ↦ (a,−1,b) sulla faccia {x=1}: porta {x=1} su {y=−1}.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.portaYm : E3 ≃ₗᵢ[ℝ] E3 := segnoX.trans scambioXY

/-- porta {x=1} su {z=−1}.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.portaZm : E3 ≃ₗᵢ[ℝ] E3 := segnoX.trans scambioXZ

/-- Le azioni di segnoX sugli otto vertici.
@isnad1 id=and.0h0v.s12.f2f39b022552 from=translated src=- shape=831afe37 vocab=d819a83c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_vertici : segnoX c0 = c4 ∧ segnoX c1 = c5 ∧ segnoX c2 = c6 ∧
    segnoX c3 = c7 ∧ segnoX c4 = c0 ∧ segnoX c5 = c1 ∧ segnoX c6 = c2 ∧
    segnoX c7 = c3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [segnoX, c0, c1, c2, c3, c4, c5, c6, c7,
        LinearIsometryEquiv.piLpCongrRight])

/-- Le azioni di scambioXY sugli otto vertici.
@isnad1 id=and.0h0v.s12.3e3e0609761c from=translated src=- shape=e3376a64 vocab=9e0205a1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.scambioXY_vertici : scambioXY c0 = c0 ∧ scambioXY c1 = c1 ∧
    scambioXY c2 = c4 ∧ scambioXY c3 = c5 ∧ scambioXY c4 = c2 ∧
    scambioXY c5 = c3 ∧ scambioXY c6 = c6 ∧ scambioXY c7 = c7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [scambioXY, c0, c1, c2, c3, c4, c5, c6, c7, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft])

/-- Le azioni di scambioXZ sugli otto vertici.
@isnad1 id=and.0h0v.s12.1cee3ff28fbe from=translated src=- shape=5166c790 vocab=afd9c333
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.scambioXZ_vertici : scambioXZ c0 = c0 ∧ scambioXZ c1 = c4 ∧
    scambioXZ c2 = c2 ∧ scambioXZ c3 = c6 ∧ scambioXZ c4 = c1 ∧
    scambioXZ c5 = c5 ∧ scambioXZ c6 = c3 ∧ scambioXZ c7 = c7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [scambioXZ, c0, c1, c2, c3, c4, c5, c6, c7, Equiv.swap_apply_def,
        LinearIsometryEquiv.piLpCongrLeft])

/-! ## L'aritmetica dell'argmax -/

/-- I proiettori delle altre due coordinate.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.lY : E3 →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 3)
def _root_.Tengoku.LeanEvalPlatonicClassification.lZ : E3 →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)

/--
@isnad1 id=and.0h0v.s11.cd5703c64db3 from=translated src=- shape=a085122f vocab=a096a1f1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.lY_vertici : lY c0 = 1 ∧ lY c1 = 1 ∧ lY c2 = -1 ∧ lY c3 = -1 ∧
    lY c4 = 1 ∧ lY c5 = 1 ∧ lY c6 = -1 ∧ lY c7 = -1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
@isnad1 id=and.0h0v.s11.eca84018d7d9 from=translated src=- shape=0ebb01ee vocab=0cb02cd8
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.lZ_vertici : lZ c0 = 1 ∧ lZ c1 = -1 ∧ lZ c2 = 1 ∧ lZ c3 = -1 ∧
    lZ c4 = 1 ∧ lZ c5 = -1 ∧ lZ c6 = 1 ∧ lZ c7 = -1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Classificazione

variable (l : E3 →L[ℝ] ℝ)

/-- Le tre componenti del funzionale.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.compL (i : Fin 3) : ℝ := l (EuclideanSpace.single i 1)

/--
@isnad1 id=eq.0h3v.s9.89fb28aee620 from=translated src=- shape=0c276ab6 vocab=0ac0ee61
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.decomposizione_toLp (s0 s1 s2 : ℝ) :
    (WithLp.toLp 2 ![s0, s1, s2] : E3)
      = s0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        + s1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
        + s2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
  ext j <;> fin_cases j <;> simp [PiLp.single_apply]

/--
@isnad1 id=eq.0h4v.s9.08bec30f7043 from=translated src=- shape=86ea6b4e vocab=7eef30e2
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_toLp3 (s0 s1 s2 : ℝ) :
    l (WithLp.toLp 2 ![s0, s1, s2])
      = s0 * compL l 0 + s1 * compL l 1 + s2 * compL l 2 := by
  rw [decomposizione_toLp, map_add, map_add, map_smul, map_smul, map_smul]
  simp [compL, smul_eq_mul]

/--
@isnad1 id=eq.0h1v.s9.dc1e2b25c228 from=translated src=- shape=33ed46a8 vocab=d948ada2
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c0 : l c0 = compL l 0 + compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![1, 1, 1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.a441bbbb3dc4 from=translated src=- shape=b793baa9 vocab=939f7260
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c1 : l c1 = compL l 0 + compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![1, 1, -1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.2406aa2c5cfa from=translated src=- shape=b793baa9 vocab=b5316c83
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c2 : l c2 = compL l 0 - compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![1, -1, 1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.e2b8efb335b9 from=translated src=- shape=33ed46a8 vocab=c37ad807
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c3 : l c3 = compL l 0 - compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![1, -1, -1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.16f3227c21e5 from=translated src=- shape=92a386a6 vocab=15ed49f6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c4 : l c4 = -compL l 0 + compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![-1, 1, 1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.d32b653c6b33 from=translated src=- shape=9a3934b0 vocab=89ebc052
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c5 : l c5 = -compL l 0 + compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![-1, 1, -1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.3f1f18927644 from=translated src=- shape=9a3934b0 vocab=00b17ee3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c6 : l c6 = -compL l 0 - compL l 1 + compL l 2 := by
  show l (WithLp.toLp 2 ![-1, -1, 1]) = _
  rw [l_toLp3]
  ring

/--
@isnad1 id=eq.0h1v.s9.861c4c52bff6 from=translated src=- shape=92a386a6 vocab=52459f0f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.l_c7 : l c7 = -compL l 0 - compL l 1 - compL l 2 := by
  show l (WithLp.toLp 2 ![-1, -1, -1]) = _
  rw [l_toLp3]
  ring

end Classificazione

/-- Lo span di un insieme dentro una coppia ha rango ≤ 1.
@isnad1 id=le.1h3v.s10.b4ccd5d4e8dc from=translated src=- shape=ca54627f vocab=598d3784
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.span_coppia_le {T : Set E3} {v w : E3} (hT : T ⊆ {v, w}) :
    Module.finrank ℝ (vectorSpan ℝ T) ≤ 1 := by
  have hmono : vectorSpan ℝ T ≤ vectorSpan ℝ ({v, w} : Set E3) :=
    vectorSpan_mono ℝ hT
  have hle := Submodule.finrank_mono hmono
  have hpair : Module.finrank ℝ (vectorSpan ℝ ({v, w} : Set E3)) ≤ 1 := by
    rw [vectorSpan_pair]
    rcases eq_or_ne (v -ᵥ w) 0 with h0 | h0
    · rw [h0, Submodule.span_zero_singleton]
      simp
    · rw [finrank_span_singleton h0]
  omega

/-! ## Le sei facce come Finset e le caratterizzazioni per coordinate -/

def _root_.Tengoku.LeanEvalPlatonicClassification.facciaXm : Finset E3 := {c4, c6, c7, c5}
def _root_.Tengoku.LeanEvalPlatonicClassification.facciaY1 : Finset E3 := {c0, c4, c5, c1}
def _root_.Tengoku.LeanEvalPlatonicClassification.facciaYm : Finset E3 := {c2, c6, c7, c3}
def _root_.Tengoku.LeanEvalPlatonicClassification.facciaZ1 : Finset E3 := {c0, c2, c6, c4}
def _root_.Tengoku.LeanEvalPlatonicClassification.facciaZm : Finset E3 := {c1, c3, c7, c5}

/--
@isnad1 id=eq.0h0v.s8.80a1c7718ac2 from=translated src=- shape=12cae476 vocab=eaa53fef
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiXm : {x ∈ (verticiCubo : Set E3) | lX x = -1}
    = (facciaXm : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exfalso; rw [lX_vertici.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lX_vertici.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaXm]
    · simp [facciaXm]
    · simp [facciaXm]
    · simp [facciaXm]
  · intro hz
    have hcasi : z = c4 ∨ z = c6 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaXm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨by simp [verticiCubo], lX_vertici.2.2.2.2.2.1⟩

/--
@isnad1 id=eq.0h0v.s8.8e266d944a09 from=translated src=- shape=a743ce6c vocab=f67b04ea
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiY1 : {x ∈ (verticiCubo : Set E3) | lY x = 1}
    = (facciaY1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · simp [facciaY1]
    · simp [facciaY1]
    · exfalso; rw [lY_vertici.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaY1]
    · simp [facciaY1]
    · exfalso; rw [lY_vertici.2.2.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.2.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = c0 ∨ z = c4 ∨ z = c5 ∨ z = c1 := by
      simpa [facciaY1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lY_vertici.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.1⟩

/--
@isnad1 id=eq.0h0v.s8.b0344dbbe2e8 from=translated src=- shape=12cae476 vocab=6eae1099
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiYm : {x ∈ (verticiCubo : Set E3) | lY x = -1}
    = (facciaYm : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exfalso; rw [lY_vertici.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.1] at hlz; norm_num at hlz
    · simp [facciaYm]
    · simp [facciaYm]
    · exfalso; rw [lY_vertici.2.2.2.2.1] at hlz; norm_num at hlz
    · exfalso; rw [lY_vertici.2.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaYm]
    · simp [facciaYm]
  · intro hz
    have hcasi : z = c2 ∨ z = c6 ∨ z = c7 ∨ z = c3 := by
      simpa [facciaYm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨by simp [verticiCubo], lY_vertici.2.2.2.1⟩

/--
@isnad1 id=eq.0h0v.s8.7c4881876c16 from=translated src=- shape=a743ce6c vocab=cdbc42ea
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiZ1 : {x ∈ (verticiCubo : Set E3) | lZ x = 1}
    = (facciaZ1 : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.1] at hlz; norm_num at hlz
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZ1]
    · exfalso; rw [lZ_vertici.2.2.2.2.2.2.2] at hlz; norm_num at hlz
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c6 ∨ z = c4 := by
      simpa [facciaZ1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lZ_vertici.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.1⟩

/--
@isnad1 id=eq.0h0v.s8.1c573fcee8e5 from=translated src=- shape=12cae476 vocab=c8c1b80c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.argmax_verticiZm : {x ∈ (verticiCubo : Set E3) | lZ x = -1}
    = (facciaZm : Set E3) := by
  ext z
  constructor
  · rintro ⟨hz, hlz⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exfalso; rw [lZ_vertici.1] at hlz; norm_num at hlz
    · simp [facciaZm]
    · exfalso; rw [lZ_vertici.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZm]
    · exfalso; rw [lZ_vertici.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZm]
    · exfalso; rw [lZ_vertici.2.2.2.2.2.2.1] at hlz; norm_num at hlz
    · simp [facciaZm]
  · intro hz
    have hcasi : z = c1 ∨ z = c3 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaZm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.1⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨by simp [verticiCubo], lZ_vertici.2.2.2.2.2.1⟩

/-! ## Le sei esclusioni di segno -/

section Esclusioni

variable (l : E3 →L[ℝ] ℝ)

/--
@isnad1 id=eq.3h2v.s10.4335b2267cfb from=translated src=- shape=ff18494d vocab=41c9a1cf
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.esclusione_xp (hx : 0 < compL l 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lX u = 1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact lX_vertici.1
  · exact lX_vertici.2.1
  · exact lX_vertici.2.2.1
  · exact lX_vertici.2.2.2.1
  · exfalso; have h := hmax c0 (by simp [verticiCubo])
    rw [l_c0, l_c4] at h; linarith
  · exfalso; have h := hmax c1 (by simp [verticiCubo])
    rw [l_c1, l_c5] at h; linarith
  · exfalso; have h := hmax c2 (by simp [verticiCubo])
    rw [l_c2, l_c6] at h; linarith
  · exfalso; have h := hmax c3 (by simp [verticiCubo])
    rw [l_c3, l_c7] at h; linarith

/--
@isnad1 id=eq.3h2v.s10.b1584d35bdcc from=translated src=- shape=da4bd317 vocab=2917e9a1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.esclusione_xm (hx : compL l 0 < 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lX u = -1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exfalso; have h := hmax c4 (by simp [verticiCubo])
    rw [l_c4, l_c0] at h; linarith
  · exfalso; have h := hmax c5 (by simp [verticiCubo])
    rw [l_c5, l_c1] at h; linarith
  · exfalso; have h := hmax c6 (by simp [verticiCubo])
    rw [l_c6, l_c2] at h; linarith
  · exfalso; have h := hmax c7 (by simp [verticiCubo])
    rw [l_c7, l_c3] at h; linarith
  · exact lX_vertici.2.2.2.2.1
  · exact lX_vertici.2.2.2.2.2.1
  · exact lX_vertici.2.2.2.2.2.2.1
  · exact lX_vertici.2.2.2.2.2.2.2

/--
@isnad1 id=eq.3h2v.s10.6da43ebe83df from=translated src=- shape=ff18494d vocab=83ee7e62
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.esclusione_yp (hy : 0 < compL l 1) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lY u = 1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact lY_vertici.1
  · exact lY_vertici.2.1
  · exfalso; have h := hmax c0 (by simp [verticiCubo])
    rw [l_c0, l_c2] at h; linarith
  · exfalso; have h := hmax c1 (by simp [verticiCubo])
    rw [l_c1, l_c3] at h; linarith
  · exact lY_vertici.2.2.2.2.1
  · exact lY_vertici.2.2.2.2.2.1
  · exfalso; have h := hmax c4 (by simp [verticiCubo])
    rw [l_c4, l_c6] at h; linarith
  · exfalso; have h := hmax c5 (by simp [verticiCubo])
    rw [l_c5, l_c7] at h; linarith

/--
@isnad1 id=eq.3h2v.s10.07be95a082d6 from=translated src=- shape=da4bd317 vocab=a80f0fc9
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.esclusione_ym (hy : compL l 1 < 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lY u = -1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exfalso; have h := hmax c2 (by simp [verticiCubo])
    rw [l_c2, l_c0] at h; linarith
  · exfalso; have h := hmax c3 (by simp [verticiCubo])
    rw [l_c3, l_c1] at h; linarith
  · exact lY_vertici.2.2.1
  · exact lY_vertici.2.2.2.1
  · exfalso; have h := hmax c6 (by simp [verticiCubo])
    rw [l_c6, l_c4] at h; linarith
  · exfalso; have h := hmax c7 (by simp [verticiCubo])
    rw [l_c7, l_c5] at h; linarith
  · exact lY_vertici.2.2.2.2.2.2.1
  · exact lY_vertici.2.2.2.2.2.2.2

/--
@isnad1 id=eq.3h2v.s10.f85c20f32eda from=translated src=- shape=ff18494d vocab=935dc966
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.esclusione_zp (hz : 0 < compL l 2) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lZ u = 1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exact lZ_vertici.1
  · exfalso; have h := hmax c0 (by simp [verticiCubo])
    rw [l_c0, l_c1] at h; linarith
  · exact lZ_vertici.2.2.1
  · exfalso; have h := hmax c2 (by simp [verticiCubo])
    rw [l_c2, l_c3] at h; linarith
  · exact lZ_vertici.2.2.2.2.1
  · exfalso; have h := hmax c4 (by simp [verticiCubo])
    rw [l_c4, l_c5] at h; linarith
  · exact lZ_vertici.2.2.2.2.2.2.1
  · exfalso; have h := hmax c6 (by simp [verticiCubo])
    rw [l_c6, l_c7] at h; linarith

/--
@isnad1 id=eq.3h2v.s10.512b4c0f2242 from=translated src=- shape=da4bd317 vocab=7a5a28e0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.esclusione_zm (hz : compL l 2 < 0) {u : E3}
    (hu : u ∈ (verticiCubo : Set E3))
    (hmax : ∀ w ∈ (verticiCubo : Set E3), l w ≤ l u) : lZ u = -1 := by
  rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
    h | h | h | h | h | h | h | h <;> subst h
  · exfalso; have h := hmax c1 (by simp [verticiCubo])
    rw [l_c1, l_c0] at h; linarith
  · exact lZ_vertici.2.1
  · exfalso; have h := hmax c3 (by simp [verticiCubo])
    rw [l_c3, l_c2] at h; linarith
  · exact lZ_vertici.2.2.2.1
  · exfalso; have h := hmax c5 (by simp [verticiCubo])
    rw [l_c5, l_c4] at h; linarith
  · exact lZ_vertici.2.2.2.2.2.1
  · exfalso; have h := hmax c7 (by simp [verticiCubo])
    rw [l_c7, l_c6] at h; linarith
  · exact lZ_vertici.2.2.2.2.2.2.2

end Esclusioni

/-! ## Azioni delle composizioni sui vertici -/

/--
@isnad1 id=and.0h0v.s12.5ac095b4fafc from=translated src=- shape=19eaed7b vocab=5e3f940a
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.portaYm_vertici : portaYm c0 = c2 ∧ portaYm c1 = c3 ∧ portaYm c2 = c6 ∧
    portaYm c3 = c7 ∧ portaYm c4 = c0 ∧ portaYm c5 = c1 ∧ portaYm c6 = c4 ∧
    portaYm c7 = c5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [portaYm, segnoX, scambioXY, c0, c1, c2, c3, c4, c5, c6, c7,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft,
        LinearIsometryEquiv.piLpCongrRight])

/--
@isnad1 id=and.0h0v.s12.8bfda53c8b5b from=translated src=- shape=ad2de696 vocab=3a1947b1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.portaZm_vertici : portaZm c0 = c1 ∧ portaZm c1 = c5 ∧ portaZm c2 = c3 ∧
    portaZm c3 = c7 ∧ portaZm c4 = c0 ∧ portaZm c5 = c4 ∧ portaZm c6 = c2 ∧
    portaZm c7 = c6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j <;> fin_cases j <;>
      simp [portaZm, segnoX, scambioXZ, c0, c1, c2, c3, c4, c5, c6, c7,
        Equiv.swap_apply_def, LinearIsometryEquiv.piLpCongrLeft,
        LinearIsometryEquiv.piLpCongrRight])

/-! ## Le cinque permutazioni dei vertici e la preservazione del politopo -/

/--
@isnad1 id=eq.0h0v.s10.6d2ed18abb42 from=translated src=- shape=d59c196b vocab=5cdc7f14
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_vertset :
    (⇑segnoX) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [segnoX_vertici.1, segnoX_vertici.2.1, segnoX_vertici.2.2.1,
        segnoX_vertici.2.2.2.1, segnoX_vertici.2.2.2.2.1,
        segnoX_vertici.2.2.2.2.2.1, segnoX_vertici.2.2.2.2.2.2.1,
        segnoX_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c4, by simp [verticiCubo], segnoX_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], segnoX_vertici.2.2.2.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], segnoX_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], segnoX_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c0, by simp [verticiCubo], segnoX_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], segnoX_vertici.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], segnoX_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], segnoX_vertici.2.2.2.1⟩

/--
@isnad1 id=eq.0h0v.s10.cecc07d25506 from=translated src=- shape=d59c196b vocab=3bef0c17
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.scambioXY_vertset :
    (⇑scambioXY) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [scambioXY_vertici.1, scambioXY_vertici.2.1,
        scambioXY_vertici.2.2.1, scambioXY_vertici.2.2.2.1,
        scambioXY_vertici.2.2.2.2.1, scambioXY_vertici.2.2.2.2.2.1,
        scambioXY_vertici.2.2.2.2.2.2.1, scambioXY_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c0, by simp [verticiCubo], scambioXY_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], scambioXY_vertici.2.1⟩
    · exact ⟨c4, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], scambioXY_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], scambioXY_vertici.2.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], scambioXY_vertici.2.2.2.2.2.2.2⟩

/--
@isnad1 id=eq.0h0v.s10.d1dd082e95aa from=translated src=- shape=d59c196b vocab=ba7a5ace
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.scambioXZ_vertset :
    (⇑scambioXZ) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [scambioXZ_vertici.1, scambioXZ_vertici.2.1,
        scambioXZ_vertici.2.2.1, scambioXZ_vertici.2.2.2.1,
        scambioXZ_vertici.2.2.2.2.1, scambioXZ_vertici.2.2.2.2.2.1,
        scambioXZ_vertici.2.2.2.2.2.2.1, scambioXZ_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c0, by simp [verticiCubo], scambioXZ_vertici.1⟩
    · exact ⟨c4, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], scambioXZ_vertici.2.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c1, by simp [verticiCubo], scambioXZ_vertici.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], scambioXZ_vertici.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], scambioXZ_vertici.2.2.2.2.2.2.2⟩

/--
@isnad1 id=eq.0h0v.s10.330c6d100767 from=translated src=- shape=d59c196b vocab=715e1301
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.portaYm_vertset :
    (⇑portaYm) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [portaYm_vertici.1, portaYm_vertici.2.1, portaYm_vertici.2.2.1,
        portaYm_vertici.2.2.2.1, portaYm_vertici.2.2.2.2.1,
        portaYm_vertici.2.2.2.2.2.1, portaYm_vertici.2.2.2.2.2.2.1,
        portaYm_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c4, by simp [verticiCubo], portaYm_vertici.2.2.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], portaYm_vertici.2.2.2.2.2.1⟩
    · exact ⟨c0, by simp [verticiCubo], portaYm_vertici.1⟩
    · exact ⟨c1, by simp [verticiCubo], portaYm_vertici.2.1⟩
    · exact ⟨c6, by simp [verticiCubo], portaYm_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], portaYm_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c2, by simp [verticiCubo], portaYm_vertici.2.2.1⟩
    · exact ⟨c3, by simp [verticiCubo], portaYm_vertici.2.2.2.1⟩

/--
@isnad1 id=eq.0h0v.s10.fa307a49bd63 from=translated src=- shape=d59c196b vocab=97ed06db
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.portaZm_vertset :
    (⇑portaZm) '' (verticiCubo : Set E3) = (verticiCubo : Set E3) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
      h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [portaZm_vertici.1, portaZm_vertici.2.1, portaZm_vertici.2.2.1,
        portaZm_vertici.2.2.2.1, portaZm_vertici.2.2.2.2.1,
        portaZm_vertici.2.2.2.2.2.1, portaZm_vertici.2.2.2.2.2.2.1,
        portaZm_vertici.2.2.2.2.2.2.2] <;>
      simp [verticiCubo]
  · intro hz
    rcases mem_verticiCubo_iff.mp (by exact_mod_cast hz) with
      h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨c4, by simp [verticiCubo], portaZm_vertici.2.2.2.2.1⟩
    · exact ⟨c0, by simp [verticiCubo], portaZm_vertici.1⟩
    · exact ⟨c6, by simp [verticiCubo], portaZm_vertici.2.2.2.2.2.2.1⟩
    · exact ⟨c2, by simp [verticiCubo], portaZm_vertici.2.2.1⟩
    · exact ⟨c5, by simp [verticiCubo], portaZm_vertici.2.2.2.2.2.1⟩
    · exact ⟨c1, by simp [verticiCubo], portaZm_vertici.2.1⟩
    · exact ⟨c7, by simp [verticiCubo], portaZm_vertici.2.2.2.2.2.2.2⟩
    · exact ⟨c3, by simp [verticiCubo], portaZm_vertici.2.2.2.1⟩

/-- Se un'isometria lineare permuta i vertici, la versione affine preserva il
corpo del cubo.
@isnad1 id=eq.1h1v.s11.6d0e009f9c1b from=translated src=- shape=3836ef24 vocab=049d988f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.preserva_toSet_di_vertici (g : E3 ≃ₗᵢ[ℝ] E3)
    (hv : (⇑g) '' (verticiCubo : Set E3) = (verticiCubo : Set E3)) :
    (⇑g.toAffineIsometryEquiv) '' cubo.toSet = cubo.toSet := by
  show (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiCubo : Set E3))
    = convexHull ℝ (verticiCubo : Set E3)
  have haff : (⇑g.toAffineIsometryEquiv) '' (convexHull ℝ (verticiCubo : Set E3))
      = convexHull ℝ ((⇑g.toAffineIsometryEquiv) '' (verticiCubo : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff, show (⇑g.toAffineIsometryEquiv) '' (verticiCubo : Set E3)
    = (verticiCubo : Set E3) from hv]

/-! ## Le cinque immagini della faccia F₀ -/

/--
@isnad1 id=eq.0h0v.s10.ea64c1d2e774 from=translated src=- shape=a5ba5df3 vocab=a05bd25a
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.segnoX_F₀ : (⇑segnoX.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaXm : Set E3) := by
  show (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑segnoX.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑segnoX.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull segnoX.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑segnoX.toAffineIsometryEquiv) u = segnoX u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [segnoX_vertici.1, segnoX_vertici.2.1, segnoX_vertici.2.2.1,
        segnoX_vertici.2.2.2.1] <;>
      simp [facciaXm]
  · intro hz
    have hcasi : z = c4 ∨ z = c6 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaXm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], segnoX_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], segnoX_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], segnoX_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], segnoX_vertici.2.1⟩

/--
@isnad1 id=eq.0h0v.s10.5d7c22f8a84c from=translated src=- shape=a5ba5df3 vocab=c1627a18
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.scambioXY_F₀ : (⇑scambioXY.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaY1 : Set E3) := by
  show (⇑scambioXY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑scambioXY.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑scambioXY.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull scambioXY.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑scambioXY.toAffineIsometryEquiv) u = scambioXY u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [scambioXY_vertici.1, scambioXY_vertici.2.1,
        scambioXY_vertici.2.2.1, scambioXY_vertici.2.2.2.1] <;>
      simp [facciaY1]
  · intro hz
    have hcasi : z = c0 ∨ z = c4 ∨ z = c5 ∨ z = c1 := by
      simpa [facciaY1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], scambioXY_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], scambioXY_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], scambioXY_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], scambioXY_vertici.2.1⟩

/--
@isnad1 id=eq.0h0v.s10.3c56854175c2 from=translated src=- shape=a5ba5df3 vocab=7e2a7e15
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.portaYm_F₀ : (⇑portaYm.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaYm : Set E3) := by
  show (⇑portaYm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑portaYm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑portaYm.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull portaYm.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑portaYm.toAffineIsometryEquiv) u = portaYm u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [portaYm_vertici.1, portaYm_vertici.2.1, portaYm_vertici.2.2.1,
        portaYm_vertici.2.2.2.1] <;>
      simp [facciaYm]
  · intro hz
    have hcasi : z = c2 ∨ z = c6 ∨ z = c7 ∨ z = c3 := by
      simpa [facciaYm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], portaYm_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], portaYm_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], portaYm_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], portaYm_vertici.2.1⟩

/--
@isnad1 id=eq.0h0v.s10.3ee46ec2df77 from=translated src=- shape=a5ba5df3 vocab=b31c0a29
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.scambioXZ_F₀ : (⇑scambioXZ.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaZ1 : Set E3) := by
  show (⇑scambioXZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑scambioXZ.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑scambioXZ.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull scambioXZ.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑scambioXZ.toAffineIsometryEquiv) u = scambioXZ u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [scambioXZ_vertici.1, scambioXZ_vertici.2.1,
        scambioXZ_vertici.2.2.1, scambioXZ_vertici.2.2.2.1] <;>
      simp [facciaZ1]
  · intro hz
    have hcasi : z = c0 ∨ z = c2 ∨ z = c6 ∨ z = c4 := by
      simpa [facciaZ1] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], scambioXZ_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], scambioXZ_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], scambioXZ_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], scambioXZ_vertici.2.1⟩

/--
@isnad1 id=eq.0h0v.s10.657eb975d269 from=translated src=- shape=a5ba5df3 vocab=171350d5
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.portaZm_F₀ : (⇑portaZm.toAffineIsometryEquiv) '' F₀
    = convexHull ℝ (facciaZm : Set E3) := by
  show (⇑portaZm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3)) = _
  have haff : (⇑portaZm.toAffineIsometryEquiv) '' (convexHull ℝ (facciaX1 : Set E3))
      = convexHull ℝ ((⇑portaZm.toAffineIsometryEquiv) '' (facciaX1 : Set E3)) :=
    AffineMap.image_convexHull portaZm.toAffineIsometryEquiv.toAffineIsometry.toAffineMap _
  rw [haff]
  congr 1
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcv : (⇑portaZm.toAffineIsometryEquiv) u = portaZm u := rfl
    rw [hcv]
    have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
      simpa [facciaX1] using hu
    rcases hcasi with h | h | h | h <;> subst h <;>
      simp only [portaZm_vertici.1, portaZm_vertici.2.1, portaZm_vertici.2.2.1,
        portaZm_vertici.2.2.2.1] <;>
      simp [facciaZm]
  · intro hz
    have hcasi : z = c1 ∨ z = c3 ∨ z = c7 ∨ z = c5 := by
      simpa [facciaZm] using hz
    rcases hcasi with h | h | h | h <;> subst h
    · exact ⟨c0, by simp [facciaX1], portaZm_vertici.1⟩
    · exact ⟨c2, by simp [facciaX1], portaZm_vertici.2.2.1⟩
    · exact ⟨c3, by simp [facciaX1], portaZm_vertici.2.2.2.1⟩
    · exact ⟨c1, by simp [facciaX1], portaZm_vertici.2.1⟩

/-! ## LA CLASSIFICAZIONE DELLE FACCETTE DEL CUBO -/

set_option maxHeartbeats 1600000 in
/-- LA CLASSIFICAZIONE: ogni faccetta del cubo è una delle sei facce.
@isnad1 id=or.1h1v.s10.478e6de04013 from=translated src=- shape=04512666 vocab=e0146f45
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.facet_classification_cubo {F : Set E3} (hF : cubo.IsFacet F) :
    F = convexHull ℝ (facciaX1 : Set E3) ∨ F = convexHull ℝ (facciaXm : Set E3)
    ∨ F = convexHull ℝ (facciaY1 : Set E3) ∨ F = convexHull ℝ (facciaYm : Set E3)
    ∨ F = convexHull ℝ (facciaZ1 : Set E3) ∨ F = convexHull ℝ (facciaZm : Set E3) := by
  classical
  obtain ⟨l, hl⟩ := hF.1.1 hF.1.2
  have hFS := exposedFace_eq_convexHull_vertices_cubo hF.1
  set S : Finset E3 := cubo.vertices.filter (· ∈ F) with hSdef
  have hspanS : vectorSpan ℝ (S : Set E3)
      = vectorSpan ℝ (convexHull ℝ (S : Set E3)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have hd : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hdF := hF.2
    rw [hFS, ← hspanS] at hdF
    exact hdF
  have hSsub : (S : Set E3) ⊆ (cubo.vertices : Set E3) := by
    intro u hu
    have : u ∈ cubo.vertices.filter (· ∈ F) := by exact_mod_cast hu
    exact_mod_cast Finset.filter_subset _ _ this
  have hcrit : ∀ u ∈ (cubo.vertices : Set E3),
      (u ∈ (S : Set E3) ↔ ∀ w ∈ (cubo.vertices : Set E3), l w ≤ l u) := by
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
      show u ∈ ((cubo.vertices.filter (· ∈ F) : Finset E3) : Set E3)
      exact_mod_cast Finset.mem_filter.mpr ⟨by exact_mod_cast hu, huF⟩
  -- lo scheletro comune dei rami-coppia
  have hcoppia : ∀ v w : E3, (S : Set E3) ⊆ {v, w} → False := by
    intro v w hsub
    have := span_coppia_le hsub
    omega
  rcases lt_trichotomy (compL l 0) 0 with hx | hx | hx
  · -- a0 < 0
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a0 < 0, a1 < 0 → S ⊆ {c6, c7}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c6, c7} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xm l hx hu hmax
          have hy1 := esclusione_ym l hy hu hmax
          have hux : u ∈ (facciaXm : Set E3) := by
            rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
          have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaXm] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · rw [lY_vertici.2.2.2.2.1] at hy1; norm_num at hy1
          · simp
          · simp
          · rw [lY_vertici.2.2.2.2.2.1] at hy1; norm_num at hy1
        have := span_coppia_le hsub
        omega)
    · -- a0 < 0, a1 = 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a0 < 0, a2 < 0 → S ⊆ {c5, c7}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c5, c7} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xm l hx hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have hux : u ∈ (facciaXm : Set E3) := by
              rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
            have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
              simpa [facciaXm] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.2.2.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a0 < 0: la faccia {x = -1}
        refine Or.inr (Or.inl ?_)
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xm l hx hu hmax
          rw [← argmax_verticiXm]
          exact ⟨hu, hx1⟩
        · intro huf
          have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaXm] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a0 < 0, a2 > 0 → S ⊆ {c4, c6}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c4, c6} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xm l hx hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have hux : u ∈ (facciaXm : Set E3) := by
              rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
            have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
              simpa [facciaXm] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.2.2.2.2] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
    · -- a0 < 0, a1 > 0 → S ⊆ {c4, c5}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c4, c5} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xm l hx hu hmax
          have hy1 := esclusione_yp l hy hu hmax
          have hux : u ∈ (facciaXm : Set E3) := by
            rw [← argmax_verticiXm]; exact ⟨hu, hx1⟩
          have hcasi : u = c4 ∨ u = c6 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaXm] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · simp
          · rw [lY_vertici.2.2.2.2.2.2.1] at hy1; norm_num at hy1
          · rw [lY_vertici.2.2.2.2.2.2.2] at hy1; norm_num at hy1
          · simp
        have := span_coppia_le hsub
        omega)
  · -- a0 = 0
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a0 = 0, a1 < 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a1 < 0, a2 < 0 → S ⊆ {c3, c7}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c3, c7} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_ym l hy hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have huy : u ∈ (facciaYm : Set E3) := by
              rw [← argmax_verticiYm]; exact ⟨hu, hy1⟩
            have hcasi : u = c2 ∨ u = c6 ∨ u = c7 ∨ u = c3 := by
              simpa [facciaYm] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a1 < 0: la faccia {y = -1}
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hy1 := esclusione_ym l hy hu hmax
          rw [← argmax_verticiYm]
          exact ⟨hu, hy1⟩
        · intro huf
          have hcasi : u = c2 ∨ u = c6 ∨ u = c7 ∨ u = c3 := by
            simpa [facciaYm] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a1 < 0, a2 > 0 → S ⊆ {c2, c6}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c2, c6} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_ym l hy hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have huy : u ∈ (facciaYm : Set E3) := by
              rw [← argmax_verticiYm]; exact ⟨hu, hy1⟩
            have hcasi : u = c2 ∨ u = c6 ∨ u = c7 ∨ u = c3 := by
              simpa [facciaYm] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.2.2.2.2] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
    · -- a0 = 0, a1 = 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- SOLO a2 < 0: la faccia {z = -1}
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hz1 := esclusione_zm l hz hu hmax
          rw [← argmax_verticiZm]
          exact ⟨hu, hz1⟩
        · intro huf
          have hcasi : u = c1 ∨ u = c3 ∨ u = c7 ∨ u = c5 := by
            simpa [facciaZm] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- TUTTI NULLI: S = tutti i vertici, span 3D, assurdo
        exfalso
        have hSall : (S : Set E3) = (cubo.vertices : Set E3) := by
          apply Set.Subset.antisymm hSsub
          intro u hu
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hu) with
            h | h | h | h | h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
        rw [hSall, cubo_finrank] at hd
        omega
      · -- SOLO a2 > 0: la faccia {z = 1}
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hz1 := esclusione_zp l hz hu hmax
          rw [← argmax_verticiZ1]
          exact ⟨hu, hz1⟩
        · intro huf
          have hcasi : u = c0 ∨ u = c2 ∨ u = c6 ∨ u = c4 := by
            simpa [facciaZ1] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
    · -- a0 = 0, a1 > 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a1 > 0, a2 < 0 → S ⊆ {c1, c5}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c1, c5} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_yp l hy hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have huy : u ∈ (facciaY1 : Set E3) := by
              rw [← argmax_verticiY1]; exact ⟨hu, hy1⟩
            have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
              simpa [facciaY1] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a1 > 0: la faccia {y = 1}
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hy1 := esclusione_yp l hy hu hmax
          rw [← argmax_verticiY1]
          exact ⟨hu, hy1⟩
        · intro huf
          have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
            simpa [facciaY1] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a1 > 0, a2 > 0 → S ⊆ {c0, c4}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c0, c4} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hy1 := esclusione_yp l hy hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have huy : u ∈ (facciaY1 : Set E3) := by
              rw [← argmax_verticiY1]; exact ⟨hu, hy1⟩
            have hcasi : u = c0 ∨ u = c4 ∨ u = c5 ∨ u = c1 := by
              simpa [facciaY1] using huy
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
  · -- a0 > 0
    rcases lt_trichotomy (compL l 1) 0 with hy | hy | hy
    · -- a0 > 0, a1 < 0 → S ⊆ {c2, c3}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c2, c3} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xp l hx hu hmax
          have hy1 := esclusione_ym l hy hu hmax
          have hux : u ∈ (facciaX1 : Set E3) := by
            rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
          have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
            simpa [facciaX1] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · rw [lY_vertici.1] at hy1; norm_num at hy1
          · simp
          · simp
          · rw [lY_vertici.2.1] at hy1; norm_num at hy1
        have := span_coppia_le hsub
        omega)
    · -- a0 > 0, a1 = 0
      rcases lt_trichotomy (compL l 2) 0 with hz | hz | hz
      · -- a0 > 0, a2 < 0 → S ⊆ {c1, c3}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c1, c3} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xp l hx hu hmax
            have hz1 := esclusione_zm l hz hu hmax
            have hux : u ∈ (facciaX1 : Set E3) := by
              rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
            have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
              simpa [facciaX1] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · rw [lZ_vertici.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.2.1] at hz1; norm_num at hz1
            · simp
            · simp
          have := span_coppia_le hsub
          omega)
      · -- SOLO a0 > 0: la faccia {x = 1}, identità
        refine Or.inl ?_
        rw [hFS]
        congr 1
        ext u
        constructor
        · intro huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xp l hx hu hmax
          rw [← argmax_verticiX]
          exact ⟨hu, hx1⟩
        · intro huf
          have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
            simpa [facciaX1] using huf
          have hu : u ∈ (cubo.vertices : Set E3) := by
            rcases hcasi with h | h | h | h <;> subst h <;>
              simp [cubo, verticiCubo]
          refine (hcrit u hu).mpr ?_
          intro w hw
          rcases mem_verticiCubo_iff.mp (by exact_mod_cast hw) with
            h | h | h | h | h | h | h | h <;> subst h <;>
          rcases hcasi with h | h | h | h <;> subst h <;>
            simp only [l_c0, l_c1, l_c2, l_c3, l_c4, l_c5, l_c6, l_c7] <;>
            linarith
      · -- a0 > 0, a2 > 0 → S ⊆ {c0, c2}
        exact absurd hd (by
          have hsub : (S : Set E3) ⊆ {c0, c2} := by
            intro u huS
            have hu := hSsub huS
            have hmax := (hcrit u hu).mp huS
            have hx1 := esclusione_xp l hx hu hmax
            have hz1 := esclusione_zp l hz hu hmax
            have hux : u ∈ (facciaX1 : Set E3) := by
              rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
            have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
              simpa [facciaX1] using hux
            rcases hcasi with h | h | h | h <;> subst h
            · simp
            · simp
            · rw [lZ_vertici.2.2.2.1] at hz1; norm_num at hz1
            · rw [lZ_vertici.2.1] at hz1; norm_num at hz1
          have := span_coppia_le hsub
          omega)
    · -- a0 > 0, a1 > 0 → S ⊆ {c0, c1}
      exact absurd hd (by
        have hsub : (S : Set E3) ⊆ {c0, c1} := by
          intro u huS
          have hu := hSsub huS
          have hmax := (hcrit u hu).mp huS
          have hx1 := esclusione_xp l hx hu hmax
          have hy1 := esclusione_yp l hy hu hmax
          have hux : u ∈ (facciaX1 : Set E3) := by
            rw [← argmax_verticiX]; exact ⟨hu, hx1⟩
          have hcasi : u = c0 ∨ u = c2 ∨ u = c3 ∨ u = c1 := by
            simpa [facciaX1] using hux
          rcases hcasi with h | h | h | h <;> subst h
          · simp
          · rw [lY_vertici.2.2.1] at hy1; norm_num at hy1
          · rw [lY_vertici.2.2.2.1] at hy1; norm_num at hy1
          · simp
        have := span_coppia_le hsub
        omega)

/-! ## Il 3-ciclo diagonale e i semispazi delle facce -/

def _root_.Tengoku.LeanEvalPlatonicClassification.cicloCoord : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- La rotazione di 2π/3 attorno alla diagonale (1,1,1): (x,y,z) ↦ (z,x,y).-/
def _root_.Tengoku.LeanEvalPlatonicClassification.rotDiag : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ cicloCoord

/-! ## Semispazi per lY e lZ -/

/-! ## L'argmax triplo: solo c0 ha tutte e tre le coordinate a 1 -/

/--
@isnad1 id=ne.0h0v.s2.3d86eca9517b from=translated src=- shape=54c8eceb vocab=29cde015
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c0_ne_c4 : c0 ≠ c4 := by
  intro h
  have := congrArg (fun v : E3 => (WithLp.ofLp v) 0) h
  simp [c0, c4] at this
  norm_num at this

/-! ## Le tre facce del fan sono distinte -/

/-! ## IL FAN DEL VERTICE c0 -/

/-! ## Gli otto vertici sono ciclici: simmetrie di segno e trasferimento -/

def _root_.Tengoku.LeanEvalPlatonicClassification.segnoZ : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]

/-! ## IL TESTIMONE -/
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
