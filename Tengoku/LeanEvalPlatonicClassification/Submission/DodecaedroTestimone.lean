import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Fondamenta
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasferimento
import Tengoku.LeanEvalPlatonicClassification.Submission.TetraedroStadio2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/Solarys431/lean-eval-platonic-classification@3cd00dfd965e, `Submission/DodecaedroTestimone.lean`: removed 5 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
DODECAEDRO — TESTIMONE (5,3), port a modulo (18 lug 2026, notte).

Sorgente: `teoremi/Platonici_DodecaedroCompleto.lean` (sol, fascicoli 6-8,
CERTIFICATO 177/177). Le definizioni condivise vengono da `Fondamenta`,
i lemmi di trasferimento dal modulo `Trasferimento`, `E3`/`norma_toLp` dal
modulo del tetraedro. Rinomine anti-collisione: suffisso `D` su F₀, c0-c3,
d1, d2, segnoX/Y/Z; `cosferico_extremePoints_dodeca`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Metric Tengoku.LeanEvalPlatonicClassification.FiniteConvexPolytope
open scoped RealInnerProductSpace

noncomputable section


variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-! ## Aritmetica aurea e coordinate -/

local notation "φ" => Real.goldenRatio

/--
@isnad1 id=eq.0h0v.s4.9dcb06fbeb49 from=translated src=- shape=b3e66441 vocab=cc66d9f9
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_inv : φ⁻¹ = φ - 1 := by
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

/--
@isnad1 id=eq.0h0v.s6.4bd68aaabfb4 from=translated src=- shape=ab1b7eb4 vocab=0e325edc
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_norm_sq_nf : (2 / (1 + Real.sqrt 5)) ^ 2 + (φ + 1) = 3 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : 1 + Real.sqrt 5 ≠ 0 := by positivity
  rw [Real.goldenRatio]
  field_simp
  nlinarith

/--
@isnad1 id=eq.0h0v.s5.30eb00443692 from=translated src=- shape=28ce7b61 vocab=5a76c882
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_inv_nf : 2 / (1 + Real.sqrt 5) = φ - 1 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : 1 + Real.sqrt 5 ≠ 0 := by positivity
  rw [Real.goldenRatio]
  field_simp
  nlinarith

/--
@isnad1 id=eq.0h0v.s5.01db373415d4 from=translated src=- shape=1dc66942 vocab=f1a4693c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_sqrt_five : Real.sqrt 5 = 2 * φ - 1 := by
  rw [Real.goldenRatio]
  ring

/--
@isnad1 id=eq.0h0v.s5.ea9ef7bcc835 from=translated src=- shape=fe6c4183 vocab=421c5835
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_den_self : (1 + Real.sqrt 5) / (1 + Real.sqrt 5) = 1 := by
  field_simp

/--
@isnad1 id=lt.0h0v.s3.267a2c64fe74 from=translated src=- shape=62e5f382 vocab=b2a104af
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_inv_pos : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos

/-! ## I venti vertici -/

def _root_.Tengoku.LeanEvalPlatonicClassification.a0 : E3 := WithLp.toLp 2 ![-1, -1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a1 : E3 := WithLp.toLp 2 ![-1, -1,  1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a2 : E3 := WithLp.toLp 2 ![-1,  1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a3 : E3 := WithLp.toLp 2 ![-1,  1,  1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a4 : E3 := WithLp.toLp 2 ![ 1, -1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a5 : E3 := WithLp.toLp 2 ![ 1, -1,  1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a6 : E3 := WithLp.toLp 2 ![ 1,  1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.a7 : E3 := WithLp.toLp 2 ![ 1,  1,  1]

def _root_.Tengoku.LeanEvalPlatonicClassification.b0 : E3 := WithLp.toLp 2 ![0, -φ⁻¹, -φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.b1 : E3 := WithLp.toLp 2 ![0, -φ⁻¹,  φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.b2 : E3 := WithLp.toLp 2 ![0,  φ⁻¹, -φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.b3 : E3 := WithLp.toLp 2 ![0,  φ⁻¹,  φ]

def _root_.Tengoku.LeanEvalPlatonicClassification.c0D : E3 := WithLp.toLp 2 ![-φ, 0, -φ⁻¹]
def _root_.Tengoku.LeanEvalPlatonicClassification.c1D : E3 := WithLp.toLp 2 ![-φ, 0,  φ⁻¹]
def _root_.Tengoku.LeanEvalPlatonicClassification.c2D : E3 := WithLp.toLp 2 ![ φ, 0, -φ⁻¹]
def _root_.Tengoku.LeanEvalPlatonicClassification.c3D : E3 := WithLp.toLp 2 ![ φ, 0,  φ⁻¹]

def _root_.Tengoku.LeanEvalPlatonicClassification.d0 : E3 := WithLp.toLp 2 ![-φ⁻¹, -φ, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.d1D : E3 := WithLp.toLp 2 ![-φ⁻¹,  φ, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.d2D : E3 := WithLp.toLp 2 ![ φ⁻¹, -φ, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.d3 : E3 := WithLp.toLp 2 ![ φ⁻¹,  φ, 0]

open Classical in
def _root_.Tengoku.LeanEvalPlatonicClassification.verticiDodeca : Finset E3 :=
  {a0, a1, a2, a3, a4, a5, a6, a7,
   b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3}

/--
@isnad1 id=eq.1h1v.s6.d2acb506e941 from=translated src=- shape=3bc45c0e vocab=727caa51
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.norm_verticiDodeca : ∀ v ∈ verticiDodeca, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]
  all_goals rw [norma_toLp]
  all_goals congr 1
  all_goals norm_num [golden_inv, Real.goldenRatio_sq] <;>
    nlinarith [golden_norm_sq_nf]

/-! Il lemma cosferico usato anche per il tetraedro. -/

/--
@isnad1 id=eq.1h4v.s7.8ba8e447e686 from=translated src=- shape=3c79d8e4 vocab=bd3cbdd4
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.cosferico_extremePoints_dodeca {B : Type*} [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [Nontrivial B]
    (x : B) (r : ℝ) (V : Set B) (hV : V ⊆ sphere x r) :
    (convexHull ℝ V).extremePoints ℝ = V := by
  refine le_antisymm extremePoints_convexHull_subset ?_
  have hball : convexHull ℝ V ⊆ closedBall x r :=
    convexHull_min (hV.trans sphere_subset_closedBall) (convex_closedBall x r)
  intro v hv
  have hsfera : v ∈ (closedBall x r).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hV hv
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ V hv, hsfera⟩

def _root_.Tengoku.LeanEvalPlatonicClassification.dodecaedro : FiniteConvexPolytope E3 where
  vertices := verticiDodeca
  nonempty := ⟨a0, by simp [verticiDodeca]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiDodeca : Set E3) ⊆ sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_verticiDodeca v (by exact_mod_cast hv)
    exact (cosferico_extremePoints_dodeca 0 (Real.sqrt 3) _ hV).symm

/-! ## Dimensione affine tre -/

def _root_.Tengoku.LeanEvalPlatonicClassification.cubeBasisPoints : Fin 4 → E3 := ![a7, a4, a2, a1]

/--
@isnad1 id=affinein.0h0v.s8.dab13a3298cd from=translated src=- shape=7e71be5a vocab=2b6196a7
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.cubeBasisPoints_affineIndependent :
    AffineIndependent ℝ cubeBasisPoints := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun x : E3 => x j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [cubeBasisPoints, a7, a4, a2, a1, Fin.sum_univ_four] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  change u 0 * 1 + u 1 * 1 + u 2 * (-1) + u 3 * (-1) =
    v 0 * 1 + v 1 * 1 + v 2 * (-1) + v 3 * (-1) at h0
  change u 0 * 1 + u 1 * (-1) + u 2 * 1 + u 3 * (-1) =
    v 0 * 1 + v 1 * (-1) + v 2 * 1 + v 3 * (-1) at h1
  change u 0 * 1 + u 1 * (-1) + u 2 * (-1) + u 3 * 1 =
    v 0 * 1 + v 1 * (-1) + v 2 * (-1) + v 3 * 1 at h2
  rw [Fin.sum_univ_four] at hu hv
  have e0 : u 0 = v 0 := by linarith
  have e1 : u 1 = v 1 := by linarith
  have e2 : u 2 = v 2 := by linarith
  have e3 : u 3 = v 3 := by linarith
  fin_cases i <;> assumption

/--
@isnad1 id=le.0h0v.s4.98564ef8cd14 from=translated src=- shape=75b2c703 vocab=c7490070
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.range_cubeBasisPoints_subset :
    Set.range cubeBasisPoints ⊆ (verticiDodeca : Set E3) := by
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp [cubeBasisPoints, verticiDodeca]

/--
@isnad1 id=eq.0h0v.s10.6cd67af6c5b9 from=translated src=- shape=774ba165 vocab=07c99c60
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.dodecaedro_finrank :
    Module.finrank ℝ (vectorSpan ℝ (dodecaedro.vertices : Set E3)) = 3 := by
  change Module.finrank ℝ (vectorSpan ℝ (verticiDodeca : Set E3)) = 3
  have htop : vectorSpan ℝ (Set.range cubeBasisPoints) = ⊤ :=
    cubeBasisPoints_affineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp)
  have hspan : vectorSpan ℝ (verticiDodeca : Set E3) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact vectorSpan_mono ℝ range_cubeBasisPoints_subset
  rw [hspan]
  simp

/-! ## La faccia scelta e il suo piano di supporto -/

def _root_.Tengoku.LeanEvalPlatonicClassification.x0 : E3 := a7
def _root_.Tengoku.LeanEvalPlatonicClassification.x1 : E3 := b3
def _root_.Tengoku.LeanEvalPlatonicClassification.x2 : E3 := b1
def _root_.Tengoku.LeanEvalPlatonicClassification.x3 : E3 := a5
def _root_.Tengoku.LeanEvalPlatonicClassification.x4 : E3 := c3D

/-- I vertici sono gia' ordinati nel verso della rotazione costruita sotto.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle : Fin 5 → E3 := ![x0, x1, x2, x3, x4]

/--
@isnad1 id=eq.0h0v.s4.3b6f3d20c792 from=translated src=- shape=fdee698a vocab=8c9f6232
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_zero : faceCycle 0 = x0 := rfl
/--
@isnad1 id=eq.0h0v.s4.3ee62a86da31 from=translated src=- shape=fdee698a vocab=71e9d16e
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_one : faceCycle 1 = x1 := rfl
/--
@isnad1 id=eq.0h0v.s4.c09004e46cd8 from=translated src=- shape=fdee698a vocab=6fb6ac4c
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_two : faceCycle 2 = x2 := rfl
/--
@isnad1 id=eq.0h0v.s4.0a83ae7c47c3 from=translated src=- shape=fdee698a vocab=41b6ca78
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_three : faceCycle 3 = x3 := rfl
/--
@isnad1 id=eq.0h0v.s4.11522717b68a from=translated src=- shape=fdee698a vocab=0639722d
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_four : faceCycle 4 = x4 := rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.F₀D : Set E3 := convexHull ℝ (Set.range faceCycle)

/-- La lunghezza del lato nel modello di raggio `sqrt 3`.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.ℓ₀ : ℝ := 2 * φ⁻¹

/--
@isnad1 id=lt.0h0v.s3.4ba29fa38061 from=translated src=- shape=ff3a10fc vocab=13f2a611
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.ℓ₀_pos : 0 < ℓ₀ := by
  dsimp [ℓ₀]
  positivity

/-- Il normale della faccia e' `(1,0,φ)`; il livello di supporto e' `φ+1`.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.supportL : E3 →L[ℝ] ℝ :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 0) +
    φ • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2)

/--
@isnad1 id=eq.0h1v.s9.baad8d811051 from=translated src=- shape=2134e8f4 vocab=7c2f6b1e
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_apply (z : E3) : supportL z = z 0 + φ * z 2 := by
  rfl

/--
@isnad1 id=eq.0h1v.s8.cea8ccb5bf19 from=translated src=- shape=00dc9ee7 vocab=c96bf3a6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_faceCycle (i : Fin 5) : supportL (faceCycle i) = φ + 1 := by
  fin_cases i
  · change (1 : ℝ) + φ * 1 = φ + 1
    ring
  · change (0 : ℝ) + φ * φ = φ + 1
    nlinarith [golden_inv_nf, Real.goldenRatio_sq]
  · change (0 : ℝ) + φ * φ = φ + 1
    nlinarith [Real.goldenRatio_sq]
  · change (1 : ℝ) + φ * 1 = φ + 1
    ring
  · change φ + φ * φ⁻¹ = φ + 1
    rw [Real.inv_goldenRatio, mul_neg, Real.goldenRatio_mul_goldenConj]
    ring

/--
@isnad1 id=mem.0h1v.s4.b7c3f41e6ef4 from=translated src=- shape=a46a3632 vocab=510cd9b2
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_mem_vertices (i : Fin 5) :
    faceCycle i ∈ (verticiDodeca : Set E3) := by
  fin_cases i <;> simp [faceCycle, x0, x1, x2, x3, x4,
    verticiDodeca]

/--
@isnad1 id=injectiv.0h0v.s3.7ae8453d7c8a from=translated src=- shape=bfe16b09 vocab=7710954b
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_injective : Function.Injective faceCycle := by
  have hφ : 0 < φ := Real.goldenRatio_pos
  have hq : 0 < 2 / (1 + Real.sqrt 5) := by positivity
  have hsqrt : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    exfalso
    have h0 := congrArg (fun z : E3 => z 0) hij
    have h1 := congrArg (fun z : E3 => z 1) hij
    have h2 := congrArg (fun z : E3 => z 2) hij
  all_goals norm_num [faceCycle, x0, x1, x2, x3, x4,
    a7, b3, b1, a5, c3D] at h0
  all_goals norm_num [faceCycle, x0, x1, x2, x3, x4,
    a7, b3, b1, a5, c3D] at h1
  all_goals norm_num [faceCycle, x0, x1, x2, x3, x4,
    a7, b3, b1, a5, c3D] at h2
  all_goals nlinarith

/--
@isnad1 id=le.1h1v.s8.b750c599ebd8 from=translated src=- shape=d683e783 vocab=841df16f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_vertices_le (v : E3) (hv : v ∈ verticiDodeca) :
    supportL v ≤ φ + 1 := by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [supportL, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals nlinarith [golden_inv_nf, Real.goldenRatio_sq]

/--
@isnad1 id=mem.2h1v.s8.4caf0335fcb9 from=translated src=- shape=205389f6 vocab=5fe20d57
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_eq_imp_faceCycle (v : E3) (hv : v ∈ verticiDodeca)
    (heq : supportL v = φ + 1) : v ∈ Set.range faceCycle := by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | skip
  all_goals exfalso
  all_goals norm_num [supportL, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3] at heq
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at heq
  all_goals nlinarith [golden_inv_nf, Real.goldenRatio_sq]

/--
@isnad1 id=nonempty.0h0v.s1.0a8d759bd2d3 from=translated src=- shape=25b03439 vocab=ce955137
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_nonemptyD : F₀D.Nonempty := by
  exact ⟨x0, subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩⟩

/--
@isnad1 id=le.0h0v.s6.5d0c7884abce from=translated src=- shape=0ab70a54 vocab=68c1f402
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_subset_dodecaedro : F₀D ⊆ dodecaedro.toSet := by
  apply convexHull_mono
  rintro z ⟨i, rfl⟩
  exact faceCycle_mem_vertices i

/--
@isnad1 id=le.1h1v.s8.2132c62ef8b3 from=translated src=- shape=6a4d503a vocab=41c06902
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_polytope_le (z : E3) (hz : z ∈ dodecaedro.toSet) :
    supportL z ≤ φ + 1 := by
  have hc : ConvexOn ℝ Set.univ supportL :=
    supportL.toLinearMap.convexOn convex_univ
  obtain ⟨v, hv, hzv⟩ := hc.exists_ge_of_mem_convexHull
    (Set.subset_univ (s := (verticiDodeca : Set E3))) hz
  exact hzv.trans (supportL_vertices_le v hv)

/--
@isnad1 id=eq.1h1v.s8.ffc2088f36e5 from=translated src=- shape=d683e783 vocab=1e99dac6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_eq_on_F₀ (z : E3) (hz : z ∈ F₀D) :
    supportL z = φ + 1 := by
  have hc : ConvexOn ℝ Set.univ supportL :=
    supportL.toLinearMap.convexOn convex_univ
  have hcc : ConcaveOn ℝ Set.univ supportL :=
    supportL.toLinearMap.concaveOn convex_univ
  obtain ⟨u, ⟨i, rfl⟩, hzu⟩ := hc.exists_ge_of_mem_convexHull
    (Set.subset_univ (s := Set.range faceCycle)) hz
  obtain ⟨v, ⟨j, rfl⟩, hvz⟩ := hcc.exists_le_of_mem_convexHull
    (Set.subset_univ (s := Set.range faceCycle)) hz
  rw [supportL_faceCycle i] at hzu
  rw [supportL_faceCycle j] at hvz
  exact le_antisymm hzu hvz

/-- Un punto dell'hull totale sul piano di supporto usa soltanto i cinque
vertici massimizzanti, dunque appartiene alla faccia.
@isnad1 id=mem.2h1v.s8.211a9d0d2578 from=translated src=- shape=f92d9fd0 vocab=906b1676
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₀_of_mem_polytope_support_eq (z : E3) (hz : z ∈ dodecaedro.toSet)
    (hzeq : supportL z = φ + 1) : z ∈ F₀D := by
  classical
  change z ∈ convexHull ℝ (Set.range faceCycle)
  change z ∈ convexHull ℝ (verticiDodeca : Set E3) at hz
  obtain ⟨w, hw0, hw1, hsum⟩ := (Finset.mem_convexHull').mp hz
  have hLsum : ∑ y ∈ verticiDodeca, w y * supportL y = supportL z := by
    have h := congrArg supportL hsum
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  have hdef : ∑ y ∈ verticiDodeca, w y * ((φ + 1) - supportL y) = 0 := by
    calc
      ∑ y ∈ verticiDodeca, w y * ((φ + 1) - supportL y) =
          ∑ y ∈ verticiDodeca,
            (w y * (φ + 1) - w y * supportL y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ y ∈ verticiDodeca, w y * (φ + 1)) -
            ∑ y ∈ verticiDodeca, w y * supportL y :=
              by rw [Finset.sum_sub_distrib]
      _ = (φ + 1) * (∑ y ∈ verticiDodeca, w y) -
            ∑ y ∈ verticiDodeca, w y * supportL y := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (φ + 1) - supportL z := by rw [hw1, hLsum]; ring
      _ = 0 := by rw [hzeq]; ring
  have hterm (y : E3) (hy : y ∈ verticiDodeca) :
      w y * ((φ + 1) - supportL y) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef y hy
    intro u hu
    exact mul_nonneg (hw0 u hu)
      (sub_nonneg.mpr (supportL_vertices_le u hu))
  have hwzero (y : E3) (hy : y ∈ verticiDodeca)
      (hyface : y ∉ Set.range faceCycle) : w y = 0 := by
    have hne : (φ + 1) - supportL y ≠ 0 := by
      intro h
      apply hyface
      apply supportL_eq_imp_faceCycle y hy
      linarith
    exact (mul_eq_zero.mp (hterm y hy)).resolve_right hne
  let I := {y // y ∈ verticiDodeca}
  let z' : I → E3 := fun y =>
    if y.1 ∈ Set.range faceCycle then y.1 else x0
  refine mem_convexHull_of_exists_fintype
    (fun y : I => w y.1) z' ?_ ?_ ?_ ?_
  · intro y
    exact hw0 y.1 y.2
  · change (∑ y : {y // y ∈ verticiDodeca}, w y.1) = 1
    rw [← Finset.sum_subtype verticiDodeca (by simp) w]
    exact hw1
  · intro y
    dsimp [z']
    split_ifs with h
    · exact h
    · exact ⟨0, rfl⟩
  · have hzterm (y : I) : w y.1 • z' y = w y.1 • y.1 := by
      by_cases hface : y.1 ∈ Set.range faceCycle
      · change w y.1 • (if y.1 ∈ Set.range faceCycle then y.1 else x0) = _
        rw [ite_eq_left hface]
      · change w y.1 • (if y.1 ∈ Set.range faceCycle then y.1 else x0) = _
        rw [ite_eq_right hface, hwzero y.1 y.2 hface]
        simp
    calc
      ∑ y : I, w y.1 • z' y = ∑ y : I, w y.1 • y.1 := by
        apply Fintype.sum_congr
        exact hzterm
      _ = ∑ y ∈ verticiDodeca, w y • y := by
        change (∑ y : {y // y ∈ verticiDodeca}, w y.1 • y.1) = _
        rw [← Finset.sum_subtype verticiDodeca (by simp)
          (fun y => w y • y)]
      _ = z := hsum

/--
@isnad1 id=isexpose.0h0v.s8.e75d65644cd1 from=translated src=- shape=ff65ec80 vocab=0ecf7a24
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_isExposed : IsExposed ℝ dodecaedro.toSet F₀D := by
  intro _hne
  refine ⟨supportL, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨F₀_subset_dodecaedro hz, ?_⟩
    intro y hy
    rw [supportL_eq_on_F₀ z hz]
    exact supportL_polytope_le y hy
  · rintro ⟨hzP, hzmax⟩
    have hx0P : x0 ∈ dodecaedro.toSet :=
      F₀_subset_dodecaedro (subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩)
    have hlo : φ + 1 ≤ supportL z := by
      simpa [show supportL x0 = φ + 1 from supportL_faceCycle 0] using hzmax x0 hx0P
    have hhi := supportL_polytope_le z hzP
    exact mem_F₀_of_mem_polytope_support_eq z hzP (le_antisymm hhi hlo)

/-! ## Dimensione due della faccia -/

def _root_.Tengoku.LeanEvalPlatonicClassification.baseTriple : Fin 3 → E3 := ![x0, x1, x2]

/--
@isnad1 id=affinein.0h0v.s8.88c787080958 from=translated src=- shape=7e71be5a vocab=42a52130
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.baseTriple_affineIndependent : AffineIndependent ℝ baseTriple := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun z : E3 => z j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [baseTriple, x0, x1, x2, a7, b3, b1, Fin.sum_univ_three] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  change u 0 * 1 + u 1 * 0 + u 2 * 0 =
    v 0 * 1 + v 1 * 0 + v 2 * 0 at h0
  change u 0 * 1 + u 1 * (2 / (1 + Real.sqrt 5)) +
      u 2 * (-(2 / (1 + Real.sqrt 5))) =
    v 0 * 1 + v 1 * (2 / (1 + Real.sqrt 5)) +
      v 2 * (-(2 / (1 + Real.sqrt 5))) at h1
  rw [Fin.sum_univ_three] at hu hv
  have hq : 0 < 2 / (1 + Real.sqrt 5) := by positivity
  have e0 : u 0 = v 0 := by linarith
  have e1 : u 1 = v 1 := by nlinarith
  have e2 : u 2 = v 2 := by nlinarith
  fin_cases i <;> assumption

def _root_.Tengoku.LeanEvalPlatonicClassification.weights3 : Fin 3 → ℝ := ![1, -φ, φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.weights4 : Fin 3 → ℝ := ![φ, -φ, 1]

/--
@isnad1 id=eq.0h0v.s5.cc5477d01e6f from=translated src=- shape=c69a548c vocab=f36b8582
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.weights3_sum : ∑ i : Fin 3, weights3 i = 1 := by
  simp [weights3, Fin.sum_univ_three]

/--
@isnad1 id=eq.0h0v.s5.e2ce7eb70c21 from=translated src=- shape=c69a548c vocab=9781a13d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.weights4_sum : ∑ i : Fin 3, weights4 i = 1 := by
  simp [weights4, Fin.sum_univ_three]

/--
@isnad1 id=eq.3h2v.s8.4515c5c0c19b from=translated src=- shape=cdd7b04e vocab=2aa62595
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.E3_ext {u v : E3} (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (h2 : u 2 = v 2) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/--
@isnad1 id=eq.0h0v.s10.112c46b077fd from=translated src=- shape=e8ffb5aa vocab=ce4a8625
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.combo_x3 :
    Finset.univ.affineCombination ℝ baseTriple weights3 = x3 := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using weights3_sum)]
  rw [Fin.sum_univ_three]
  apply E3_ext
  · change (1 : ℝ) * 1 + (-φ) * 0 + φ * 0 = 1
    ring
  · change (1 : ℝ) * 1 + (-φ) * φ⁻¹ + φ * (-φ⁻¹) = -1
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]
  · change (1 : ℝ) * 1 + (-φ) * φ + φ * φ = 1
    ring

/--
@isnad1 id=eq.0h0v.s10.92a12451d726 from=translated src=- shape=e8ffb5aa vocab=5e20cdc7
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.combo_x4 :
    Finset.univ.affineCombination ℝ baseTriple weights4 = x4 := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using weights4_sum)]
  rw [Fin.sum_univ_three]
  apply E3_ext
  · change φ * 1 + (-φ) * 0 + (1 : ℝ) * 0 = φ
    ring
  · change φ * 1 + (-φ) * φ⁻¹ + (1 : ℝ) * (-φ⁻¹) = 0
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]
  · change φ * 1 + (-φ) * φ + (1 : ℝ) * φ = φ⁻¹
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]

/--
@isnad1 id=mem.0h0v.s10.99a1d25c6902 from=translated src=- shape=5d7a5b8d vocab=70ae235f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.x3_mem_affineSpan_base : x3 ∈ affineSpan ℝ (Set.range baseTriple) := by
  have h := affineCombination_mem_affineSpan
    (s := (Finset.univ : Finset (Fin 3))) (w := weights3)
    (by simpa using weights3_sum) baseTriple
  rw [combo_x3] at h
  exact h

/--
@isnad1 id=mem.0h0v.s10.e91b881767a7 from=translated src=- shape=5d7a5b8d vocab=ed85196c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.x4_mem_affineSpan_base : x4 ∈ affineSpan ℝ (Set.range baseTriple) := by
  have h := affineCombination_mem_affineSpan
    (s := (Finset.univ : Finset (Fin 3))) (w := weights4)
    (by simpa using weights4_sum) baseTriple
  rw [combo_x4] at h
  exact h

/--
@isnad1 id=eq.0h0v.s5.c8d9639c4886 from=translated src=- shape=1a72343f vocab=532dd8d7
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.range_faceCycle_eq : Set.range faceCycle =
    insert x4 (insert x3 (Set.range baseTriple)) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨0, rfl⟩)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨1, rfl⟩)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨2, rfl⟩)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert _ _
  · rw [Set.mem_insert_iff, Set.mem_insert_iff]
    rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact ⟨4, rfl⟩
    · exact ⟨3, rfl⟩
    · fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩

/--
@isnad1 id=coplanar.0h0v.s8.f81e42c06802 from=translated src=- shape=fc514820 vocab=b75cf4af
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_coplanar : Coplanar ℝ (Set.range faceCycle) := by
  have hbaseRank :
      Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) = 2 :=
    baseTriple_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
  have hbase : Coplanar ℝ (Set.range baseTriple) := by
    rw [coplanar_iff_finrank_le_two, hbaseRank]
  have h3 : Coplanar ℝ (insert x3 (Set.range baseTriple)) :=
    (coplanar_insert_iff_of_mem_affineSpan x3_mem_affineSpan_base).2 hbase
  have hx4 : x4 ∈ affineSpan ℝ (insert x3 (Set.range baseTriple)) := by
    exact (affineSpan_mono ℝ (Set.subset_insert x3 _)) x4_mem_affineSpan_base
  rw [range_faceCycle_eq]
  exact (coplanar_insert_iff_of_mem_affineSpan hx4).2 h3

/--
@isnad1 id=eq.0h0v.s10.8a34b1439ba7 from=translated src=- shape=9278a3b4 vocab=4cd2cdb6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_finrank : Module.finrank ℝ (vectorSpan ℝ F₀D) = 2 := by
  have hupper : Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycle)) ≤ 2 :=
    faceCycle_coplanar.finrank_le_two
  have hlower : 2 ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycle)) := by
    have hbaseRank :
        Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) = 2 :=
      baseTriple_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
    calc
      2 = Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) := hbaseRank.symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycle)) := by
        apply Submodule.finrank_mono
        apply vectorSpan_mono ℝ
        intro z hz
        rw [range_faceCycle_eq]
        exact Set.mem_insert_of_mem x4 (Set.mem_insert_of_mem x3 hz)
  rw [F₀D, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  omega

/--
@isnad1 id=isfacet.0h0v.s6.740f3860d183 from=translated src=- shape=54c8eceb vocab=e21be659
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_isFacet : dodecaedro.IsFacet F₀D :=
  ⟨⟨F₀_isExposed, F₀_nonemptyD⟩, F₀_finrank⟩

/-! ## La rotazione aurea di ordine cinque -/

/-- La matrice e' `1/2 * [[1,-φ,φ⁻¹],[φ,φ⁻¹,-1],[φ⁻¹,1,φ]]`.
Non e' una permutazione delle coordinate.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.rhoFormula (z : E3) : E3 := WithLp.toLp 2 ![
  (z 0 - φ * z 1 + φ⁻¹ * z 2) / 2,
  (φ * z 0 + φ⁻¹ * z 1 - z 2) / 2,
  (φ⁻¹ * z 0 + z 1 + φ * z 2) / 2]

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinearMap : E3 →ₗ[ℝ] E3 where
  toFun := rhoFormula
  map_add' u v := by
    apply E3_ext <;> simp [rhoFormula] <;> ring
  map_smul' c u := by
    apply E3_ext <;> simp [rhoFormula] <;> ring

/--
@isnad1 id=eq.0h1v.s9.2000eb20ed89 from=translated src=- shape=0bcbeaca vocab=baaf0ffb
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinearMap_apply (z : E3) : rhoLinearMap z = rhoFormula z := rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinearIsometry : E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := rhoLinearMap
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    change
      ((z 0 - φ * z 1 + φ⁻¹ * z 2) / 2) ^ 2 +
        ((φ * z 0 + φ⁻¹ * z 1 - z 2) / 2) ^ 2 +
        ((φ⁻¹ * z 0 + z 1 + φ * z 2) / 2) ^ 2 =
      z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2
    rw [golden_inv]
    ring_nf
    have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [hs]
    ring

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinear : E3 ≃ₗᵢ[ℝ] E3 :=
  rhoLinearIsometry.toLinearIsometryEquiv rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.ρ : E3 ≃ᵃⁱ[ℝ] E3 := rhoLinear.toAffineIsometryEquiv

/--
@isnad1 id=eq.0h1v.s10.0462389fd393 from=translated src=- shape=8145cf1c vocab=bb2542aa
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_apply (z : E3) : ρ z = rhoFormula z := by
  rfl

/--
@isnad1 id=eq.0h1v.s10.47a156fc594f from=translated src=- shape=6ebb8b81 vocab=0477d4ac
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_faceCycle (i : Fin 5) :
    ρ (faceCycle i) = faceCycle (finRotate 5 i) := by
  have h01 : ρ x0 = x1 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x0, x1, a7, b3]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  have h12 : ρ x1 = x2 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x1, x2, b3, b1]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  have h23 : ρ x2 = x3 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x2, x3, b1, a5]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  have h34 : ρ x3 = x4 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x3, x4, a5, c3D]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [golden_sqrt_five, Real.goldenRatio_sq]
  have h40 : ρ x4 = x0 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x4, x0, c3D, a7]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals try simp only [golden_den_self] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h40

/--
@isnad1 id=eq.0h0v.s10.adc7af3ecef8 from=translated src=- shape=6bc53fa2 vocab=8d4c2d13
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_x0 : ρ x0 = x1 := by simpa using rho_faceCycle 0
/--
@isnad1 id=eq.0h0v.s10.0438648cd72e from=translated src=- shape=6bc53fa2 vocab=d5e011a5
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_x1 : ρ x1 = x2 := by simpa using rho_faceCycle 1
/--
@isnad1 id=eq.0h0v.s10.fdf58f0067c3 from=translated src=- shape=6bc53fa2 vocab=7c9c97fe
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_x2 : ρ x2 = x3 := by simpa using rho_faceCycle 2
/--
@isnad1 id=eq.0h0v.s10.1ae4db744c5b from=translated src=- shape=6bc53fa2 vocab=d7a12cdb
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_x3 : ρ x3 = x4 := by simpa using rho_faceCycle 3
/--
@isnad1 id=eq.0h0v.s10.cacd729af797 from=translated src=- shape=6bc53fa2 vocab=9ef02782
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_x4 : ρ x4 = x0 := by simpa using rho_faceCycle 4

/-! ## Assemblaggio dello spike -/

/-! ## FASCICOLO 7 — il fan del vertice `a7 = (1,1,1)` -/

/-- Il ciclo delle coordinate `(x,y,z) ↦ (z,x,y)`.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.sigmaLinear : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 3)

def _root_.Tengoku.LeanEvalPlatonicClassification.σ : E3 ≃ᵃⁱ[ℝ] E3 := sigmaLinear.toAffineIsometryEquiv

/--
@isnad1 id=eq.0h1v.s10.df1a3c18a1a4 from=translated src=- shape=afa6c3c1 vocab=48d2d9e8
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_apply_zero (z : E3) : σ z 0 = z 2 := by
  rfl

/--
@isnad1 id=eq.0h1v.s10.e3510363bb1d from=translated src=- shape=afa6c3c1 vocab=48d2d9e8
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_apply_one (z : E3) : σ z 1 = z 0 := by
  rfl

/--
@isnad1 id=eq.0h1v.s10.20891f1e52a3 from=translated src=- shape=afa6c3c1 vocab=48d2d9e8
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_apply_two (z : E3) : σ z 2 = z 1 := by
  rfl

/--
@isnad1 id=eq.0h1v.s10.be6f6f887c94 from=translated src=- shape=6f897cec vocab=a14992c1
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_formula (z : E3) :
    σ z = WithLp.toLp 2 ![z 2, z 0, z 1] := by
  apply E3_ext <;> rfl

/--
@isnad1 id=eq.0h1v.s11.02c658bffb46 from=translated src=- shape=ac49f2b6 vocab=1b85a538
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_three (z : E3) : σ (σ (σ z)) = z := by
  apply E3_ext <;> rfl

/--
@isnad1 id=eq.0h0v.s10.cc4cc6899a34 from=translated src=- shape=6bc53fa2 vocab=39150b10
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_a7 : σ a7 = a7 := by
  apply E3_ext <;> rfl

/--
@isnad1 id=mem.1h1v.s10.161506ebde6f from=translated src=- shape=7a298a1d vocab=2b383b05
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    σ v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [sigma_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]

/--
@isnad1 id=eq.0h0v.s10.d3088719ed3a from=translated src=- shape=0bc3b51f vocab=7311d113
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_image_vertices :
    (⇑σ) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact sigma_vertices v hv
  · intro v hv
    refine ⟨σ (σ v), sigma_vertices _ (sigma_vertices _ hv), ?_⟩
    exact sigma_three v

/--
@isnad1 id=eq.0h0v.s10.4bec8c2fb240 from=translated src=- shape=05619176 vocab=e2b06016
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_preserves_polytope :
    (⇑σ) '' dodecaedro.toSet = dodecaedro.toSet := by
  change (⇑σ) '' convexHull ℝ (verticiDodeca : Set E3) =
    convexHull ℝ (verticiDodeca : Set E3)
  calc
    (⇑σ) '' convexHull ℝ (verticiDodeca : Set E3) =
        convexHull ℝ ((⇑σ) '' (verticiDodeca : Set E3)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        (σ.toAffineEquiv.toAffineMap.image_convexHull
          (verticiDodeca : Set E3))
    _ = convexHull ℝ (verticiDodeca : Set E3) := by
      rw [sigma_image_vertices]

/--
@isnad1 id=iff.0h1v.s10.33e41b4fbc04 from=translated src=- shape=f143b44c vocab=23159f84
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_mem_polytope_iff (z : E3) :
    σ z ∈ dodecaedro.toSet ↔ z ∈ dodecaedro.toSet := by
  constructor
  · intro hz
    have h₁ : σ (σ z) ∈ dodecaedro.toSet := by
      rw [← sigma_preserves_polytope]
      exact ⟨σ z, hz, rfl⟩
    have h₂ : σ (σ (σ z)) ∈ dodecaedro.toSet := by
      rw [← sigma_preserves_polytope]
      exact ⟨σ (σ z), h₁, rfl⟩
    rwa [sigma_three] at h₂
  · intro hz
    rw [← sigma_preserves_polytope]
    exact ⟨z, hz, rfl⟩

/--
@isnad1 id=isexpose.1h1v.s10.e130daf22f24 from=translated src=- shape=31a2f771 vocab=f9c4b55a
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_image_isExposed {F : Set E3}
    (hF : IsExposed ℝ dodecaedro.toSet F) :
    IsExposed ℝ dodecaedro.toSet ((⇑σ) '' F) := by
  intro himage
  have hFne : F.Nonempty := by
    obtain ⟨x, hx⟩ := himage
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy⟩
  obtain ⟨l, hl⟩ := hF hFne
  let l' : E3 →L[ℝ] ℝ :=
    l.comp sigmaLinear.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨l', ?_⟩
  rw [hl]
  ext x
  constructor
  · rintro ⟨u, ⟨huP, humax⟩, rfl⟩
    refine ⟨(sigma_mem_polytope_iff u).2 huP, ?_⟩
    intro y hyP
    obtain ⟨z, rfl⟩ := σ.surjective y
    have hzP : z ∈ dodecaedro.toSet :=
      (sigma_mem_polytope_iff z).1 hyP
    simpa [l', σ] using humax z hzP
  · rintro ⟨hxP, hxmax⟩
    obtain ⟨u, rfl⟩ := σ.surjective x
    have huP : u ∈ dodecaedro.toSet :=
      (sigma_mem_polytope_iff u).1 hxP
    refine ⟨u, ⟨huP, ?_⟩, rfl⟩
    intro z hzP
    have hσzP : σ z ∈ dodecaedro.toSet :=
      (sigma_mem_polytope_iff z).2 hzP
    simpa [l', σ] using hxmax (σ z) hσzP

/--
@isnad1 id=eq.0h1v.s12.95a9422a27d2 from=translated src=- shape=e0dd9b59 vocab=71a00318
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_image_finrank (F : Set E3) :
    Module.finrank ℝ (vectorSpan ℝ ((⇑σ) '' F)) =
      Module.finrank ℝ (vectorSpan ℝ F) := by
  change Module.finrank ℝ
      (vectorSpan ℝ ((⇑σ.toAffineEquiv.toAffineMap) '' F)) = _
  rw [← σ.toAffineEquiv.toAffineMap.map_vectorSpan]
  exact sigmaLinear.toLinearEquiv.finrank_map_eq (vectorSpan ℝ F)

/--
@isnad1 id=isfacet.1h1v.s10.176fc8ef2df6 from=translated src=- shape=45dc3b19 vocab=ecfe3b7d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_image_isFacet {F : Set E3} (hF : dodecaedro.IsFacet F) :
    dodecaedro.IsFacet ((⇑σ) '' F) := by
  refine ⟨⟨sigma_image_isExposed hF.1.1, hF.1.2.image _⟩, ?_⟩
  rw [sigma_image_finrank, hF.2]

def _root_.Tengoku.LeanEvalPlatonicClassification.F₁ : Set E3 := (⇑σ) '' F₀D
def _root_.Tengoku.LeanEvalPlatonicClassification.F₂ : Set E3 := (⇑σ) '' F₁

def _root_.Tengoku.LeanEvalPlatonicClassification.fanFace : Fin 3 → Set E3 := ![F₀D, F₁, F₂]

/--
@isnad1 id=isfacet.0h0v.s6.0a098f4405f3 from=translated src=- shape=54c8eceb vocab=3e2eb6ff
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₁_isFacet : dodecaedro.IsFacet F₁ :=
  sigma_image_isFacet F₀_isFacet

/--
@isnad1 id=isfacet.0h0v.s6.63e65bc63d0f from=translated src=- shape=54c8eceb vocab=0e391c29
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₂_isFacet : dodecaedro.IsFacet F₂ :=
  sigma_image_isFacet F₁_isFacet

/--
@isnad1 id=eq.0h0v.s10.6ee19492e9be from=translated src=- shape=9139f438 vocab=5f1e97df
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_image_F₂ : (⇑σ) '' F₂ = F₀D := by
  ext z
  constructor
  · rintro ⟨u, ⟨v, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [sigma_three]
    exact hw
  · intro hz
    refine ⟨σ (σ z), ⟨σ z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
    exact sigma_three z

/--
@isnad1 id=eq.0h1v.s10.6bdaa907a62e from=translated src=- shape=67147a53 vocab=34434df0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.sigma_image_fanFace (i : Fin 3) :
    (⇑σ) '' fanFace i = fanFace (finRotate 3 i) := by
  fin_cases i
  · rfl
  · rfl
  · exact sigma_image_F₂

/--
@isnad1 id=eq.1h1v.s8.2ce0b058228f from=translated src=- shape=3e6cff48 vocab=5440ee33
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₀_support (z : E3) (hz : z ∈ F₀D) :
    z 0 + φ * z 2 = φ + 1 := by
  exact supportL_eq_on_F₀ z hz

/--
@isnad1 id=eq.1h1v.s7.580960906dac from=translated src=- shape=c2c76c0b vocab=9e8aada6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₁_support (z : E3) (hz : z ∈ F₁) :
    φ * z 0 + z 1 = φ + 1 := by
  rcases hz with ⟨u, hu, rfl⟩
  have h := supportL_eq_on_F₀ u hu
  change u 0 + φ * u 2 = φ + 1 at h
  change φ * u 2 + u 0 = φ + 1
  linarith

/--
@isnad1 id=eq.1h1v.s7.e38b39bf3473 from=translated src=- shape=c2c76c0b vocab=7b274cde
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₂_support (z : E3) (hz : z ∈ F₂) :
    φ * z 1 + z 2 = φ + 1 := by
  rcases hz with ⟨u, ⟨v, hv, rfl⟩, rfl⟩
  have h := supportL_eq_on_F₀ v hv
  change v 0 + φ * v 2 = φ + 1 at h
  change φ * v 2 + v 0 = φ + 1
  linarith

/--
@isnad1 id=mem.0h0v.s3.6e663be06832 from=translated src=- shape=d1530203 vocab=13539ff6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.a7_mem_F₀ : a7 ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩

/--
@isnad1 id=mem.0h1v.s4.cd1932f09dbc from=translated src=- shape=15a27d57 vocab=d3903799
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.a7_mem_fanFace (i : Fin 3) : a7 ∈ fanFace i := by
  fin_cases i
  · exact a7_mem_F₀
  · exact ⟨a7, a7_mem_F₀, sigma_a7⟩
  · exact ⟨a7, ⟨a7, a7_mem_F₀, sigma_a7⟩, sigma_a7⟩

/--
@isnad1 id=mem.0h0v.s3.df779848ea75 from=translated src=- shape=d1530203 vocab=b1ae7a7c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.b1_mem_F₀ : b1 ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨2, rfl⟩

/--
@isnad1 id=mem.0h0v.s3.7e7e279c1f28 from=translated src=- shape=d1530203 vocab=7080519e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c2_mem_F₁ : c2D ∈ F₁ := by
  refine ⟨b1, b1_mem_F₀, ?_⟩
  apply E3_ext <;> rfl

/--
@isnad1 id=not.0h0v.s3.4d88363abb8c from=translated src=- shape=eedf340d vocab=27c287ae
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.b1_not_mem_F₁ : b1 ∉ F₁ := by
  intro h
  have he := mem_F₁_support b1 h
  change φ * 0 + (-φ⁻¹) = φ + 1 at he
  have hp := Real.goldenRatio_pos
  have hi := golden_inv_pos
  nlinarith

/--
@isnad1 id=not.0h0v.s3.58cc5feac2f1 from=translated src=- shape=eedf340d vocab=2e8e605e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.b1_not_mem_F₂ : b1 ∉ F₂ := by
  intro h
  have he := mem_F₂_support b1 h
  change φ * (-φ⁻¹) + φ = φ + 1 at he
  rw [golden_inv] at he
  nlinarith [Real.goldenRatio_sq]

/--
@isnad1 id=not.0h0v.s3.c1f77ebdb2f1 from=translated src=- shape=eedf340d vocab=b4dc6f6f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c2_not_mem_F₂ : c2D ∉ F₂ := by
  intro h
  have he := mem_F₂_support c2D h
  change φ * 0 + (-φ⁻¹) = φ + 1 at he
  have hp := Real.goldenRatio_pos
  have hi := golden_inv_pos
  nlinarith

/--
@isnad1 id=injectiv.0h0v.s3.4b05cdd474c4 from=translated src=- shape=b032868b vocab=efdf4eb3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_injective : Function.Injective fanFace := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals exfalso
  · change F₀D = F₁ at hij
    apply b1_not_mem_F₁
    rw [← hij]
    exact b1_mem_F₀
  · change F₀D = F₂ at hij
    apply b1_not_mem_F₂
    rw [← hij]
    exact b1_mem_F₀
  · change F₁ = F₀D at hij
    apply b1_not_mem_F₁
    rw [hij]
    exact b1_mem_F₀
  · change F₁ = F₂ at hij
    apply c2_not_mem_F₂
    rw [← hij]
    exact c2_mem_F₁
  · change F₂ = F₀D at hij
    apply b1_not_mem_F₂
    rw [hij]
    exact b1_mem_F₀
  · change F₂ = F₁ at hij
    apply c2_not_mem_F₂
    rw [hij]
    exact c2_mem_F₁

/--
@isnad1 id=mem.0h0v.s3.52ef3a26bf9f from=translated src=- shape=d1530203 vocab=807dffc0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c3_mem_F₀ : c3D ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨4, rfl⟩

/--
@isnad1 id=mem.0h0v.s3.ccf6e57ac26c from=translated src=- shape=d1530203 vocab=e34778a9
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.b3_mem_F₀ : b3 ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨1, rfl⟩

/--
@isnad1 id=mem.0h0v.s3.4adf10b0ba31 from=translated src=- shape=d1530203 vocab=0c6a6a62
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c3_mem_F₁ : c3D ∈ F₁ := by
  refine ⟨b3, b3_mem_F₀, ?_⟩
  apply E3_ext <;> rfl

/--
@isnad1 id=mem.0h0v.s3.7b48518a4fec from=translated src=- shape=d1530203 vocab=e3b8ae3e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.d3_mem_F₁ : d3 ∈ F₁ := by
  refine ⟨c3D, c3_mem_F₀, ?_⟩
  apply E3_ext <;> rfl

/--
@isnad1 id=mem.0h0v.s3.22b69f345b72 from=translated src=- shape=d1530203 vocab=046b8aa9
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.d3_mem_F₂ : d3 ∈ F₂ := by
  exact ⟨c3D, c3_mem_F₁, by apply E3_ext <;> rfl⟩

/--
@isnad1 id=mem.0h0v.s3.3c5cc96e47db from=translated src=- shape=d1530203 vocab=ae5fad08
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.b3_mem_F₂ : b3 ∈ F₂ := by
  refine ⟨d3, d3_mem_F₁, ?_⟩
  apply E3_ext <;> rfl

/--
@isnad1 id=ne.0h0v.s2.776965d4873c from=translated src=- shape=54c8eceb vocab=2db27cc0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.c3_ne_a7 : c3D ≠ a7 := by
  intro h
  have h1 := congrArg (fun z : E3 => z 1) h
  norm_num [c3D, a7] at h1

/--
@isnad1 id=ne.0h0v.s2.2277a941338c from=translated src=- shape=54c8eceb vocab=7da34458
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.d3_ne_a7 : d3 ≠ a7 := by
  intro h
  have h2 := congrArg (fun z : E3 => z 2) h
  change (0 : ℝ) = 1 at h2
  norm_num at h2

/--
@isnad1 id=ne.0h0v.s2.2c269c72ba3a from=translated src=- shape=54c8eceb vocab=0e43dc86
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.b3_ne_a7 : b3 ≠ a7 := by
  intro h
  have h0 := congrArg (fun z : E3 => z 0) h
  norm_num [b3, a7] at h0

/--
@isnad1 id=ex.0h1v.s6.d9eea1c539af from=translated src=- shape=d90e0a80 vocab=8341b3ad
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_spigolo (i : Fin 3) :
    ∃ x, x ≠ a7 ∧ x ∈ fanFace i ∩ fanFace (finRotate 3 i) := by
  fin_cases i
  · exact ⟨c3D, c3_ne_a7, c3_mem_F₀, c3_mem_F₁⟩
  · exact ⟨d3, d3_ne_a7, d3_mem_F₁, d3_mem_F₂⟩
  · exact ⟨b3, b3_ne_a7, b3_mem_F₂, b3_mem_F₀⟩

/--
@isnad1 id=eq.3h1v.s5.65911fc44489 from=translated src=- shape=cfe4bbc6 vocab=8772da5f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.three_fan_faces_meet_at_a7 (z : E3)
    (h0 : z ∈ F₀D) (h1 : z ∈ F₁) (h2 : z ∈ F₂) : z = a7 := by
  have e0 := mem_F₀_support z h0
  have e1 := mem_F₁_support z h1
  have e2 := mem_F₂_support z h2
  have q0 : (z 0 - 1) + φ * (z 2 - 1) = 0 := by
    linarith
  have q1 : φ * (z 0 - 1) + (z 1 - 1) = 0 := by
    linarith
  have q2 : φ * (z 1 - 1) + (z 2 - 1) = 0 := by
    linarith
  have qz : (z 2 - 1) - φ ^ 2 * (z 0 - 1) = 0 := by
    linear_combination q2 - φ * q1
  have qx : (1 + φ ^ 3) * (z 0 - 1) = 0 := by
    linear_combination q0 - φ * qz
  have hp : 0 < 1 + φ ^ 3 := by positivity
  have hx : z 0 = 1 := by nlinarith
  have hy : z 1 = 1 := by rw [hx] at q1; linarith
  have hz : z 2 = 1 := by rw [hx] at qz; linarith
  apply E3_ext
  · exact hx
  · exact hy
  · exact hz

/-! ## Il muro: classificazione locale delle faccette incidenti -/

open Classical in
/--
@isnad1 id=eq.1h1v.s8.b145476eea3f from=translated src=- shape=d419a73e vocab=6dfee8ea
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.dodeca_exposedFace_eq_convexHull_vertices {F : Set E3}
    (hF : dodecaedro.IsFace F) :
    F = convexHull ℝ
      ((dodecaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := dodecaedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact dodecaedro.toSet := by
    exact dodecaedro.vertices.finite_toSet.isCompact_convexHull ℝ
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ dodecaedro.toSet.extremePoints ℝ) ↔
      x ∈ dodecaedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← dodecaedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((dodecaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.e₀ : E3 := WithLp.toLp 2 ![1, 0, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.e₁ : E3 := WithLp.toLp 2 ![0, 1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.e₂ : E3 := WithLp.toLp 2 ![0, 0, 1]

/--
@isnad1 id=eq.0h1v.s9.fb23b9e74bda from=translated src=- shape=d469c5d5 vocab=a2a5d1ae
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.E3_decomp (z : E3) :
    z = z 0 • e₀ + z 1 • e₁ + z 2 • e₂ := by
  apply E3_ext <;> simp [e₀, e₁, e₂]

/--
@isnad1 id=eq.0h2v.s11.e760e11eddcb from=translated src=- shape=7901ac12 vocab=87e4ccbb
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_apply_coords (l : E3 →L[ℝ] ℝ) (z : E3) :
    l z = z 0 * l e₀ + z 1 * l e₁ + z 2 * l e₂ := by
  conv_lhs => rw [E3_decomp z]
  simp only [map_add, map_smul, smul_eq_mul]

/--
@isnad1 id=eq.0h1v.s10.71a0a69aa874 from=translated src=- shape=c0064fc2 vocab=7877d01e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_a7 (l : E3 →L[ℝ] ℝ) :
    l a7 = l e₀ + l e₁ + l e₂ := by
  rw [functional_apply_coords]
  simp [a7]

/--
@isnad1 id=eq.0h1v.s10.1ffc195361f7 from=translated src=- shape=fa61e639 vocab=2a281e63
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c3 (l : E3 →L[ℝ] ℝ) :
    l c3D = φ * l e₀ + φ⁻¹ * l e₂ := by
  rw [functional_apply_coords]
  simp [c3D]

/--
@isnad1 id=eq.0h1v.s10.d913f1c11e67 from=translated src=- shape=72c51333 vocab=77aca0ec
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b3 (l : E3 →L[ℝ] ℝ) :
    l b3 = φ⁻¹ * l e₁ + φ * l e₂ := by
  rw [functional_apply_coords]
  simp [b3]

/--
@isnad1 id=eq.0h1v.s10.9806fca058bd from=translated src=- shape=72c51333 vocab=190cf74c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_d3 (l : E3 →L[ℝ] ℝ) :
    l d3 = φ⁻¹ * l e₀ + φ * l e₁ := by
  rw [functional_apply_coords]
  simp [d3]

/--
@isnad1 id=eq.0h1v.s10.bc2882dd8c9a from=translated src=- shape=9815b6cc vocab=fa621d6d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b0 (l : E3 →L[ℝ] ℝ) :
    l b0 = -φ⁻¹ * l e₁ - φ * l e₂ := by
  rw [functional_apply_coords]
  simp [b0]
  ring

/--
@isnad1 id=eq.0h1v.s10.a2a40d5b8711 from=translated src=- shape=9815b6cc vocab=cda1b891
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b1 (l : E3 →L[ℝ] ℝ) :
    l b1 = -φ⁻¹ * l e₁ + φ * l e₂ := by
  rw [functional_apply_coords]
  simp [b1]

/--
@isnad1 id=eq.0h1v.s10.a9cdeb0f7f7a from=translated src=- shape=72c51333 vocab=096b9393
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b2 (l : E3 →L[ℝ] ℝ) :
    l b2 = φ⁻¹ * l e₁ - φ * l e₂ := by
  rw [functional_apply_coords]
  simp [b2]
  ring

/--
@isnad1 id=eq.0h1v.s10.360d100428b2 from=translated src=- shape=5b548002 vocab=07508e32
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c0 (l : E3 →L[ℝ] ℝ) :
    l c0D = -φ * l e₀ - φ⁻¹ * l e₂ := by
  rw [functional_apply_coords]
  simp [c0D]
  ring

/--
@isnad1 id=eq.0h1v.s10.b3a91769d469 from=translated src=- shape=5b548002 vocab=558adb5a
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c1 (l : E3 →L[ℝ] ℝ) :
    l c1D = -φ * l e₀ + φ⁻¹ * l e₂ := by
  rw [functional_apply_coords]
  simp [c1D]

/--
@isnad1 id=eq.0h1v.s10.57eebb33632b from=translated src=- shape=fa61e639 vocab=dc0fe9e6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c2 (l : E3 →L[ℝ] ℝ) :
    l c2D = φ * l e₀ - φ⁻¹ * l e₂ := by
  rw [functional_apply_coords]
  simp [c2D]
  ring

/--
@isnad1 id=eq.0h1v.s10.470587f5af2c from=translated src=- shape=9815b6cc vocab=1c39faf6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_d0 (l : E3 →L[ℝ] ℝ) :
    l d0 = -φ⁻¹ * l e₀ - φ * l e₁ := by
  rw [functional_apply_coords]
  simp [d0]
  ring

/--
@isnad1 id=eq.0h1v.s10.cf02eaa5b107 from=translated src=- shape=9815b6cc vocab=1563e2b8
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_d1 (l : E3 →L[ℝ] ℝ) :
    l d1D = -φ⁻¹ * l e₀ + φ * l e₁ := by
  rw [functional_apply_coords]
  simp [d1D]

/--
@isnad1 id=eq.0h1v.s10.87c270dcd81d from=translated src=- shape=72c51333 vocab=1c113b2e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_d2 (l : E3 →L[ℝ] ℝ) :
    l d2D = φ⁻¹ * l e₀ - φ * l e₁ := by
  rw [functional_apply_coords]
  simp [d2D]
  ring

/--
@isnad1 id=and.7h6v.s7.f22ee1f2d790 from=translated src=- shape=6fda1b5b vocab=7b7bf493
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.weighted_terms_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a * x + b * y + c * z = 0) :
    a * x = 0 ∧ b * y = 0 ∧ c * z = 0 := by
  have hax : 0 ≤ a * x := mul_nonneg ha hx
  have hby : 0 ≤ b * y := mul_nonneg hb hy
  have hcz : 0 ≤ c * z := mul_nonneg hc hz
  constructor
  · nlinarith
  constructor <;> nlinarith

/--
@isnad1 id=and.7h6v.s7.e252569645d0 from=translated src=- shape=b6d6af39 vocab=caf967d0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.weighted_first_two_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hsum : a * x + b * y + c * z = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨hax, hby, _⟩ := weighted_terms_eq_zero hx hy hz
    ha.le hb.le hc hsum
  exact ⟨(mul_eq_zero.mp hax).resolve_left ha.ne',
    (mul_eq_zero.mp hby).resolve_left hb.ne'⟩

/--
@isnad1 id=and.7h6v.s7.10681e9cbf37 from=translated src=- shape=fac890bc vocab=caf967d0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.weighted_first_third_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (hsum : a * x + b * y + c * z = 0) : x = 0 ∧ z = 0 := by
  obtain ⟨hax, _, hcz⟩ := weighted_terms_eq_zero hx hy hz
    ha.le hb hc.le hsum
  exact ⟨(mul_eq_zero.mp hax).resolve_left ha.ne',
    (mul_eq_zero.mp hcz).resolve_left hc.ne'⟩

/--
@isnad1 id=and.7h6v.s7.5fc59c79006d from=translated src=- shape=e1edec85 vocab=caf967d0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.weighted_last_two_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * x + b * y + c * z = 0) : y = 0 ∧ z = 0 := by
  obtain ⟨_, hby, hcz⟩ := weighted_terms_eq_zero hx hy hz
    ha hb.le hc.le hsum
  exact ⟨(mul_eq_zero.mp hby).resolve_left hb.ne',
    (mul_eq_zero.mp hcz).resolve_left hc.ne'⟩

/-- I tre gap locali non negativi controllano tutti i vertici massimizzanti.
@isnad1 id=or.3h2v.s13.57f77f4f4a33 from=translated src=- shape=9b5bf1da vocab=e0b3e297
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.local_maximizer_dichotomy (l : E3 →L[ℝ] ℝ)
    (hmax : ∀ v ∈ verticiDodeca, l v ≤ l a7)
    (v : E3) (hv : v ∈ verticiDodeca) (heq : l v = l a7) :
    v = a7 ∨
    (v = c3D ∧ l c3D = l a7) ∨
    (v = b3 ∧ l b3 = l a7) ∨
    (v = d3 ∧ l d3 = l a7) ∨
    (l c3D = l a7 ∧ l b3 = l a7) ∨
    (l c3D = l a7 ∧ l d3 = l a7) ∨
    (l b3 = l a7 ∧ l d3 = l a7) := by
  let gc : ℝ := l a7 - l c3D
  let gb : ℝ := l a7 - l b3
  let gd : ℝ := l a7 - l d3
  have hgc : 0 ≤ gc := sub_nonneg.mpr (hmax c3D (by simp [verticiDodeca]))
  have hgb : 0 ≤ gb := sub_nonneg.mpr (hmax b3 (by simp [verticiDodeca]))
  have hgd : 0 ≤ gd := sub_nonneg.mpr (hmax d3 (by simp [verticiDodeca]))
  have hp1 : 0 < φ - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hp2 : 0 < 2 - φ := sub_pos.mpr Real.goldenRatio_lt_two
  have heq_raw := heq
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [gc, gb, gd] at hgc hgb hgd
  · right; right; right; right; left
    have hid : gc + gb + gd = (2 - φ) * (l a7 - l a0) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a0, golden_inv]
      simp [a0]
      ring
    rw [heq] at hid
    have hsum : 1 * gc + 1 * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0, _⟩ := weighted_terms_eq_zero hgc hgb hgd
      (by positivity) (by positivity) (by positivity) hsum
    have hc0' : l a7 - l c3D = 0 := by simpa using hc0
    have hb0' : l a7 - l b3 = 0 := by simpa using hb0
    exact ⟨(sub_eq_zero.mp hc0').symm, (sub_eq_zero.mp hb0').symm⟩
  · right; right; right; right; left
    have hid : (φ - 1) * gc + 1 * gb + (2 - φ) * gd =
        (2 - φ) * (l a7 - l a1) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a1, golden_inv]
      simp [a1] <;> ring_nf <;>
        (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (φ - 1) * gc + 1 * gb + (2 - φ) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp1 (by norm_num) hp2.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid : (2 - φ) * gc + (φ - 1) * gb + 1 * gd =
        (2 - φ) * (l a7 - l a2) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a2, golden_inv]
      simp [a2] <;> ring_nf <;>
        (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - φ) * gc + (φ - 1) * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp2 hp1 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; right
    have hid : 0 * gc + (φ - 1) * gb + (2 - φ) * gd =
        (2 - φ) * (l a7 - l a3) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a3, golden_inv]
      simp [a3] <;> ring_nf <;>
        (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 0 * gc + (φ - 1) * gb + (2 - φ) * gd = 0 := by
      simpa using hid
    obtain ⟨hb0, hd0⟩ := weighted_last_two_eq_zero hgc hgb hgd
      (by norm_num) hp1 hp2 hsum
    change l a7 - l b3 = 0 at hb0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hb0).symm, (sub_eq_zero.mp hd0).symm⟩
  · right; right; right; right; left
    have hid : 1 * gc + (2 - φ) * gb + (φ - 1) * gd =
        (2 - φ) * (l a7 - l a4) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a4, golden_inv]
      simp [a4] <;> ring_nf <;>
        (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + (2 - φ) * gb + (φ - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      (by norm_num) hp2 hp1.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid : (φ - 1) * gc + (2 - φ) * gb + 0 * gd =
        (2 - φ) * (l a7 - l a5) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a5, golden_inv]
      simp [a5] <;> ring_nf <;>
        (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (φ - 1) * gc + (2 - φ) * gb + 0 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp1 hp2 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; left
    have hid : (2 - φ) * gc + 0 * gb + (φ - 1) * gd =
        (2 - φ) * (l a7 - l a6) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_apply_coords l a6, golden_inv]
      simp [a6] <;> ring_nf <;>
        (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - φ) * gc + 0 * gb + (φ - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hd0⟩ := weighted_first_third_eq_zero hgc hgb hgd
      hp2 (by norm_num) hp1 hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hd0).symm⟩
  · exact Or.inl rfl
  · right; right; right; right; left
    have hid : 1 * gc + (φ - 1) * gb + 1 * gd =
        (2 - φ) * (l a7 - l b0) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_b0, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + (φ - 1) * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      (by norm_num) hp1 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid : (2 - φ) * gc + (φ - 1) * gb + 0 * gd =
        (2 - φ) * (l a7 - l b1) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_b1, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - φ) * gc + (φ - 1) * gb + 0 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp2 hp1 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid : (φ - 1) * gc + (2 - φ) * gb + 1 * gd =
        (2 - φ) * (l a7 - l b2) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_b2, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (φ - 1) * gc + (2 - φ) * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp1 hp2 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, heq_raw⟩))
  · right; right; right; right; left
    have hid : (φ - 1) * gc + 1 * gb + 1 * gd =
        (2 - φ) * (l a7 - l c0D) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_c0, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (φ - 1) * gc + 1 * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp1 (by norm_num) (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid : (2 - φ) * gc + 1 * gb + (φ - 1) * gd =
        (2 - φ) * (l a7 - l c1D) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_c1, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - φ) * gc + 1 * gb + (φ - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      hp2 (by norm_num) hp1.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; left
    have hid : (φ - 1) * gc + 0 * gb + (2 - φ) * gd =
        (2 - φ) * (l a7 - l c2D) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_c2, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (φ - 1) * gc + 0 * gb + (2 - φ) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hd0⟩ := weighted_first_third_eq_zero hgc hgb hgd
      hp1 (by norm_num) hp2 hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hd0).symm⟩
  · exact Or.inr (Or.inl ⟨rfl, heq_raw⟩)
  · right; right; right; right; left
    have hid : 1 * gc + 1 * gb + (φ - 1) * gd =
        (2 - φ) * (l a7 - l d0) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_d0, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + 1 * gb + (φ - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      (by norm_num) (by norm_num) hp1.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; right
    have hid : 0 * gc + (2 - φ) * gb + (φ - 1) * gd =
        (2 - φ) * (l a7 - l d1D) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_d1, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 0 * gc + (2 - φ) * gb + (φ - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hb0, hd0⟩ := weighted_last_two_eq_zero hgc hgb hgd
      (by norm_num) hp2 hp1 hsum
    change l a7 - l b3 = 0 at hb0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hb0).symm, (sub_eq_zero.mp hd0).symm⟩
  · right; right; right; right; left
    have hid : 1 * gc + (φ - 1) * gb + (2 - φ) * gd =
        (2 - φ) * (l a7 - l d2D) := by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3,
        functional_d2, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + (φ - 1) * gb + (2 - φ) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd
      (by norm_num) hp1 hp2.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, heq_raw⟩)))

/--
@isnad1 id=and.2h3v.s7.8d00c94b66eb from=translated src=- shape=1bb45bdf vocab=94de8bd7
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_pair_solve (A B C : ℝ)
    (h₁ : (φ - 1) * A - B + (φ - 2) * C = 0)
    (h₂ : -A + (φ - 2) * B + (φ - 1) * C = 0) :
    B = 0 ∧ C = φ * A := by
  have hs : φ ^ 2 - φ - 1 = 0 := by
    nlinarith [Real.goldenRatio_sq]
  constructor
  · linear_combination (-φ / 2) * h₁ - (1 / 2) * h₂ +
      ((A + C) / 2) * hs
  · linear_combination (-1 / 2) * h₁ + ((1 + φ) / 2) * h₂ -
      ((B + C) / 2) * hs

/--
@isnad1 id=eq.2h2v.s11.6524f2f25780 from=translated src=- shape=9c575f9d vocab=08862233
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_shape₀ (l : E3 →L[ℝ] ℝ)
    (hc : l c3D = l a7) (hb : l b3 = l a7) :
    ∀ z : E3, l z = l e₀ * (z 0 + φ * z 2) := by
  have ec : (φ - 1) * l e₀ - l e₁ + (φ - 2) * l e₂ = 0 := by
    rw [functional_c3, functional_a7, golden_inv] at hc
    linarith
  have eb : -l e₀ + (φ - 2) * l e₁ + (φ - 1) * l e₂ = 0 := by
    rw [functional_b3, functional_a7, golden_inv] at hb
    linarith
  obtain ⟨h1, h2⟩ := golden_pair_solve (l e₀) (l e₁) (l e₂) ec eb
  intro z
  rw [functional_apply_coords, h1, h2]
  ring

/--
@isnad1 id=eq.2h2v.s11.81c8aa29f2bb from=translated src=- shape=7ff25273 vocab=1cd0ce1f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_shape₁ (l : E3 →L[ℝ] ℝ)
    (hc : l c3D = l a7) (hd : l d3 = l a7) :
    ∀ z : E3, l z = l e₁ * (φ * z 0 + z 1) := by
  have ec : (φ - 1) * l e₀ - l e₁ + (φ - 2) * l e₂ = 0 := by
    rw [functional_c3, functional_a7, golden_inv] at hc
    linarith
  have ed : (φ - 2) * l e₀ + (φ - 1) * l e₁ - l e₂ = 0 := by
    rw [functional_d3, functional_a7, golden_inv] at hd
    linarith
  obtain ⟨h2, h0⟩ := golden_pair_solve (l e₁) (l e₂) (l e₀)
    (by linarith [ed]) (by linarith [ec])
  intro z
  rw [functional_apply_coords, h2, h0]
  ring

/--
@isnad1 id=eq.2h2v.s11.5396616889d5 from=translated src=- shape=7ff25273 vocab=3b5e6529
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_shape₂ (l : E3 →L[ℝ] ℝ)
    (hb : l b3 = l a7) (hd : l d3 = l a7) :
    ∀ z : E3, l z = l e₂ * (φ * z 1 + z 2) := by
  have eb : -l e₀ + (φ - 2) * l e₁ + (φ - 1) * l e₂ = 0 := by
    rw [functional_b3, functional_a7, golden_inv] at hb
    linarith
  have ed : (φ - 2) * l e₀ + (φ - 1) * l e₁ - l e₂ = 0 := by
    rw [functional_d3, functional_a7, golden_inv] at hd
    linarith
  obtain ⟨h0, h1⟩ := golden_pair_solve (l e₂) (l e₀) (l e₁)
    (by linarith [eb]) (by linarith [ed])
  intro z
  rw [functional_apply_coords, h0, h1]
  ring

/--
@isnad1 id=le.1h1v.s8.05b317e911b0 from=translated src=- shape=a173ad3d vocab=38b6c32b
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.support₁_polytope_le (z : E3) (hz : z ∈ dodecaedro.toSet) :
    φ * z 0 + z 1 ≤ φ + 1 := by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  have h := supportL_polytope_le u hu
  change u 0 + φ * u 2 ≤ φ + 1 at h
  change φ * u 2 + u 0 ≤ φ + 1
  linarith

/--
@isnad1 id=le.1h1v.s8.2b5d9dd87853 from=translated src=- shape=a173ad3d vocab=38b6c32b
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.support₂_polytope_le (z : E3) (hz : z ∈ dodecaedro.toSet) :
    φ * z 1 + z 2 ≤ φ + 1 := by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  have h := support₁_polytope_le u hu
  change φ * u 0 + u 1 ≤ φ + 1 at h
  change φ * u 0 + u 1 ≤ φ + 1
  exact h

/--
@isnad1 id=mem.2h1v.s8.a9ce5c252229 from=translated src=- shape=dba61586 vocab=6bad8b37
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₁_of_mem_polytope_support₁_eq (z : E3)
    (hz : z ∈ dodecaedro.toSet) (heq : φ * z 0 + z 1 = φ + 1) : z ∈ F₁ := by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  refine ⟨u, mem_F₀_of_mem_polytope_support_eq u hu ?_, rfl⟩
  change φ * u 2 + u 0 = φ + 1 at heq
  change u 0 + φ * u 2 = φ + 1
  linarith

/--
@isnad1 id=mem.2h1v.s8.9ebab6fd9e1a from=translated src=- shape=dba61586 vocab=99a13b2f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₂_of_mem_polytope_support₂_eq (z : E3)
    (hz : z ∈ dodecaedro.toSet) (heq : φ * z 1 + z 2 = φ + 1) : z ∈ F₂ := by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  refine ⟨u, mem_F₁_of_mem_polytope_support₁_eq u hu ?_, rfl⟩
  change φ * u 0 + u 1 = φ + 1 at heq
  exact heq

/--
@isnad1 id=eq.0h0v.s10.e3b7df7bb331 from=translated src=- shape=8514afa1 vocab=8b1dcb66
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.dodecaedro_toSet_finrank :
    Module.finrank ℝ (vectorSpan ℝ dodecaedro.toSet) = 3 := by
  rw [FiniteConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact dodecaedro_finrank

/--
@isnad1 id=ex.2h1v.s6.c8524b69175a from=translated src=- shape=f2cf1dc8 vocab=fd7b832f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.incident_facet_classification {F : Set E3}
    (hF : dodecaedro.IsFacet F) (ha7 : a7 ∈ F) :
    ∃ i : Fin 3, F = fanFace i := by
  classical
  obtain ⟨l, hFl⟩ := hF.1.1 hF.1.2
  have haChar : a7 ∈ {x ∈ dodecaedro.toSet |
      ∀ y ∈ dodecaedro.toSet, l y ≤ l x} := by
    rw [← hFl]
    exact ha7
  have hmaxP : ∀ y ∈ dodecaedro.toSet, l y ≤ l a7 := haChar.2
  have hmaxV : ∀ y ∈ verticiDodeca, l y ≤ l a7 := by
    intro y hy
    apply hmaxP y
    exact subset_convexHull ℝ (verticiDodeca : Set E3) hy
  have vertex_mem_iff (y : E3) (hy : y ∈ verticiDodeca) :
      y ∈ F ↔ l y = l a7 := by
    rw [hFl]
    constructor
    · intro h
      apply le_antisymm (hmaxV y hy)
      exact h.2 a7 haChar.1
    · intro heq
      refine ⟨subset_convexHull ℝ (verticiDodeca : Set E3) hy, ?_⟩
      intro z hz
      rw [heq]
      exact hmaxP z hz
  have hlne : l ≠ 0 := by
    intro hl
    have hFP : F = dodecaedro.toSet := by
      apply Set.Subset.antisymm hF.1.1.subset
      intro z hz
      rw [hFl]
      refine ⟨hz, ?_⟩
      intro y hy
      simp [hl]
    have hd := hF.2
    rw [hFP, dodecaedro_toSet_finrank] at hd
    omega
  let S : Finset E3 := dodecaedro.vertices.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S : Set E3) :=
    dodeca_exposedFace_eq_convexHull_vertices hF.1
  have hdS : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hd := hF.2
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull,
      direction_affineSpan] at hd
    exact hd
  have rank_small (u : E3)
      (hu : ∀ y ∈ verticiDodeca, l y = l a7 → y = a7 ∨ y = u) : False := by
    let pair : Fin 2 → E3 := ![a7, u]
    have hsub : (S : Set E3) ⊆ Set.range pair := by
      intro y hy
      have hy' : y ∈ dodecaedro.vertices ∧ y ∈ F := by
        exact Finset.mem_filter.mp hy
      rcases hu y hy'.1 ((vertex_mem_iff y hy'.1).1 hy'.2) with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    have hmono : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) ≤
        Module.finrank ℝ (vectorSpan ℝ (Set.range pair)) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    have hp : Module.finrank ℝ (vectorSpan ℝ (Set.range pair)) ≤ 1 :=
      finrank_vectorSpan_range_le ℝ pair (by simp)
    omega
  let hc : Prop := l c3D = l a7
  let hb : Prop := l b3 = l a7
  let hd : Prop := l d3 = l a7
  by_cases hcb : hc ∧ hb
  · have shape := functional_shape₀ l hcb.1 hcb.2
    have htne : l e₀ ≠ 0 := by
      intro ht
      apply hlne
      ext z
      rw [shape z, ht]
      simp
    have hgap : l a7 - l d3 = 2 * l e₀ := by
      rw [shape a7, shape d3]
      norm_num [a7, d3]
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]
      rw [golden_inv_nf]
      ring
    have htpos : 0 < l e₀ := by
      have := sub_nonneg.mpr (hmaxV d3 (by simp [verticiDodeca]))
      rw [hgap] at this
      exact lt_of_le_of_ne (by linarith) (Ne.symm htne)
    have hEq : F = F₀D := by
      ext z
      constructor
      · intro hz
        have hz' := hz
        rw [hFl] at hz'
        have hloRaw := hz'.2 a7 haChar.1
        rw [shape a7, shape z] at hloRaw
        change l e₀ * ((1 : ℝ) + φ * 1) ≤
          l e₀ * (z 0 + φ * z 2) at hloRaw
        have hlo := (mul_le_mul_iff_right₀ htpos).mp hloRaw
        have hhi := supportL_polytope_le z hz'.1
        exact mem_F₀_of_mem_polytope_support_eq z hz'.1
          (le_antisymm hhi (by norm_num at hlo ⊢; linarith))
      · intro hz
        rw [hFl]
        refine ⟨F₀_subset_dodecaedro hz, ?_⟩
        intro y hy
        rw [shape y, shape z]
        apply (mul_le_mul_iff_right₀ htpos).2
        rw [mem_F₀_support z hz]
        exact supportL_polytope_le y hy
    exact ⟨0, hEq⟩
  by_cases hcd : hc ∧ hd
  · have shape := functional_shape₁ l hcd.1 hcd.2
    have htne : l e₁ ≠ 0 := by
      intro ht
      apply hlne
      ext z
      rw [shape z, ht]
      simp
    have hgap : l a7 - l b3 = 2 * l e₁ := by
      rw [shape a7, shape b3]
      norm_num [a7, b3]
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]
      rw [golden_inv_nf]
      ring
    have htpos : 0 < l e₁ := by
      have := sub_nonneg.mpr (hmaxV b3 (by simp [verticiDodeca]))
      rw [hgap] at this
      exact lt_of_le_of_ne (by linarith) (Ne.symm htne)
    have hEq : F = F₁ := by
      ext z
      constructor
      · intro hz
        have hz' := hz
        rw [hFl] at hz'
        have hloRaw := hz'.2 a7 haChar.1
        rw [shape a7, shape z] at hloRaw
        change l e₁ * (φ * (1 : ℝ) + 1) ≤
          l e₁ * (φ * z 0 + z 1) at hloRaw
        have hlo := (mul_le_mul_iff_right₀ htpos).mp hloRaw
        have hhi := support₁_polytope_le z hz'.1
        exact mem_F₁_of_mem_polytope_support₁_eq z hz'.1
          (le_antisymm hhi (by norm_num at hlo ⊢; linarith))
      · intro hz
        rw [hFl]
        refine ⟨F₁_isFacet.1.1.subset hz, ?_⟩
        intro y hy
        rw [shape y, shape z]
        apply (mul_le_mul_iff_right₀ htpos).2
        rw [mem_F₁_support z hz]
        exact support₁_polytope_le y hy
    exact ⟨1, hEq⟩
  by_cases hbd : hb ∧ hd
  · have shape := functional_shape₂ l hbd.1 hbd.2
    have htne : l e₂ ≠ 0 := by
      intro ht
      apply hlne
      ext z
      rw [shape z, ht]
      simp
    have hgap : l a7 - l c3D = 2 * l e₂ := by
      rw [shape a7, shape c3D]
      norm_num [a7, c3D]
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]
      rw [golden_inv_nf]
      ring
    have htpos : 0 < l e₂ := by
      have := sub_nonneg.mpr (hmaxV c3D (by simp [verticiDodeca]))
      rw [hgap] at this
      exact lt_of_le_of_ne (by linarith) (Ne.symm htne)
    have hEq : F = F₂ := by
      ext z
      constructor
      · intro hz
        have hz' := hz
        rw [hFl] at hz'
        have hloRaw := hz'.2 a7 haChar.1
        rw [shape a7, shape z] at hloRaw
        change l e₂ * (φ * (1 : ℝ) + 1) ≤
          l e₂ * (φ * z 1 + z 2) at hloRaw
        have hlo := (mul_le_mul_iff_right₀ htpos).mp hloRaw
        have hhi := support₂_polytope_le z hz'.1
        exact mem_F₂_of_mem_polytope_support₂_eq z hz'.1
          (le_antisymm hhi (by norm_num at hlo ⊢; linarith))
      · intro hz
        rw [hFl]
        refine ⟨F₂_isFacet.1.1.subset hz, ?_⟩
        intro y hy
        rw [shape y, shape z]
        apply (mul_le_mul_iff_right₀ htpos).2
        rw [mem_F₂_support z hz]
        exact support₂_polytope_le y hy
    exact ⟨2, hEq⟩
  exfalso
  by_cases hc0 : hc
  · apply rank_small c3D
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with
      h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h.1
    · exact (hcb ⟨hc0, h.2⟩).elim
    · exact (hcd ⟨hc0, h.2⟩).elim
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim

  by_cases hb0 : hb
  · apply rank_small b3
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with
      h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hc0 h.2).elim
    · exact Or.inr h.1
    · exact (hbd ⟨hb0, h.2⟩).elim
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim
  by_cases hd0 : hd
  · apply rank_small d3
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with
      h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hc0 h.2).elim
    · exact (hb0 h.2).elim
    · exact Or.inr h.1
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim
  · apply rank_small a7
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with
      h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hc0 h.2).elim
    · exact (hb0 h.2).elim
    · exact (hd0 h.2).elim
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim
/--
@isnad1 id=or.3h3v.s7.8fc22eb3f663 from=translated src=- shape=4279677a vocab=8341b3ad
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_spigolo_due (i j : Fin 3) (z : E3)
    (hz : z ∈ fanFace i ∩ fanFace (finRotate 3 i)) (hz_ne : z ≠ a7)
    (hzj : z ∈ fanFace j) : j = i ∨ j = finRotate 3 i := by
  by_cases hji : j = i
  · exact Or.inl hji
  by_cases hjr : j = finRotate 3 i
  · exact Or.inr hjr
  exfalso
  apply hz_ne
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact three_fan_faces_meet_at_a7 z hz.1 hz.2 hzj
  · exact three_fan_faces_meet_at_a7 z hzj hz.1 hz.2
  · exact three_fan_faces_meet_at_a7 z hz.2 hzj hz.1

def _root_.Tengoku.LeanEvalPlatonicClassification.dodecaCyclicData : dodecaedro.CyclicVertexData a7 3 where
  faccetta := fanFace
  isFacet i := by
    fin_cases i
    · exact F₀_isFacet
    · exact F₁_isFacet
    · exact F₂_isFacet
  mem_v := a7_mem_fanFace
  distinte := fanFace_injective
  complete := by
    intro F hF ha
    exact incident_facet_classification hF ha
  σ := σ
  fissa_v := sigma_a7
  preserva := sigma_preserves_polytope
  ruota := sigma_image_fanFace
  spigolo := fanFace_spigolo
  spigolo_due := fanFace_spigolo_due

def _root_.Tengoku.LeanEvalPlatonicClassification.v₀ : E3 := WithLp.toLp 2 ![1, 1, 1]

/-! ## Simmetrie globali e transitività sui venti vertici -/

/-- Riflessione nella coordinata `x`.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.segnoXD : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

/-- Riflessione nella coordinata `y`.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.segnoYD : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

/-- Riflessione nella coordinata `z`.-/
def _root_.Tengoku.LeanEvalPlatonicClassification.segnoZD : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.τx : E3 ≃ᵃⁱ[ℝ] E3 := segnoXD.toAffineIsometryEquiv
def _root_.Tengoku.LeanEvalPlatonicClassification.τy : E3 ≃ᵃⁱ[ℝ] E3 := segnoYD.toAffineIsometryEquiv
def _root_.Tengoku.LeanEvalPlatonicClassification.τz : E3 ≃ᵃⁱ[ℝ] E3 := segnoZD.toAffineIsometryEquiv

/--
@isnad1 id=eq.0h1v.s10.dc8a69850d79 from=translated src=- shape=cdb8af4a vocab=f3c36221
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_zero (z : E3) : τx z 0 = -z 0 := rfl
/--
@isnad1 id=eq.0h1v.s10.1acb520e1284 from=translated src=- shape=afa6c3c1 vocab=d1a53bba
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_one (z : E3) : τx z 1 = z 1 := rfl
/--
@isnad1 id=eq.0h1v.s10.374cf82accb6 from=translated src=- shape=afa6c3c1 vocab=d1a53bba
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_two (z : E3) : τx z 2 = z 2 := rfl
/--
@isnad1 id=eq.0h1v.s10.76715a50f10c from=translated src=- shape=afa6c3c1 vocab=c1f75d3d
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_zero (z : E3) : τy z 0 = z 0 := rfl
/--
@isnad1 id=eq.0h1v.s10.fdc1a85b9c3e from=translated src=- shape=cdb8af4a vocab=d23b169e
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_one (z : E3) : τy z 1 = -z 1 := rfl
/--
@isnad1 id=eq.0h1v.s10.a0651811e1f1 from=translated src=- shape=afa6c3c1 vocab=c1f75d3d
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_two (z : E3) : τy z 2 = z 2 := rfl
/--
@isnad1 id=eq.0h1v.s10.da7bcf9b78f5 from=translated src=- shape=afa6c3c1 vocab=4c1dd585
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_zero (z : E3) : τz z 0 = z 0 := rfl
/--
@isnad1 id=eq.0h1v.s10.555c48ec540d from=translated src=- shape=afa6c3c1 vocab=4c1dd585
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_one (z : E3) : τz z 1 = z 1 := rfl
/--
@isnad1 id=eq.0h1v.s10.6088a170cb0a from=translated src=- shape=cdb8af4a vocab=0f6f49a6
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_two (z : E3) : τz z 2 = -z 2 := rfl

/--
@isnad1 id=eq.0h1v.s10.23985406c7bb from=translated src=- shape=441ab4ae vocab=07f79430
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_formula (z : E3) :
    τx z = WithLp.toLp 2 ![-z 0, z 1, z 2] := by
  apply E3_ext <;> rfl

/--
@isnad1 id=eq.0h1v.s10.78d0b654fae1 from=translated src=- shape=e7733c6a vocab=3a1d189a
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_formula (z : E3) :
    τy z = WithLp.toLp 2 ![z 0, -z 1, z 2] := by
  apply E3_ext <;> rfl

/--
@isnad1 id=eq.0h1v.s10.b72c10e92343 from=translated src=- shape=b3d2a5fb vocab=99fa22e6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_formula (z : E3) :
    τz z = WithLp.toLp 2 ![z 0, z 1, -z 2] := by
  apply E3_ext <;> rfl

/-- Un'iniezione del finito insieme dei vertici in sé è una permutazione.
@isnad1 id=eq.1h1v.s11.d769804cd614 from=translated src=- shape=14668c1a vocab=bba9007c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.image_verticiDodeca_eq_of_maps (g : E3 ≃ᵃⁱ[ℝ] E3)
    (hmap : ∀ v ∈ verticiDodeca, g v ∈ verticiDodeca) :
    (⇑g) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨v, hv, rfl⟩
    exact hmap v hv
  · rw [Set.ncard_image_of_injective _ g.injective]
  · exact verticiDodeca.finite_toSet

/-- Una simmetria affine che permuta i vertici preserva il dodecaedro.
@isnad1 id=eq.1h1v.s11.57ccee4c1462 from=translated src=- shape=5e7b972f vocab=3ee59c4d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.preserves_dodecaedro_of_image_vertices (g : E3 ≃ᵃⁱ[ℝ] E3)
    (hv : (⇑g) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3)) :
    (⇑g) '' dodecaedro.toSet = dodecaedro.toSet := by
  show (⇑g) '' convexHull ℝ (verticiDodeca : Set E3) =
    convexHull ℝ (verticiDodeca : Set E3)
  have haff : (⇑g) '' convexHull ℝ (verticiDodeca : Set E3) =
      convexHull ℝ ((⇑g) '' (verticiDodeca : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometry.toAffineMap _
  rw [haff, hv]

/--
@isnad1 id=mem.1h1v.s10.42b543168a2e from=translated src=- shape=7a298a1d vocab=5ea8e5d6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    τx v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauX_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]

/--
@isnad1 id=mem.1h1v.s10.32577aa5a112 from=translated src=- shape=7a298a1d vocab=1c4baddd
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    τy v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauY_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]

/--
@isnad1 id=mem.1h1v.s10.915d8a2294c7 from=translated src=- shape=7a298a1d vocab=5d7f417f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    τz v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauZ_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]

/--
@isnad1 id=eq.0h0v.s10.be70cfabb31b from=translated src=- shape=0bc3b51f vocab=797c8fc4
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_image_vertices :
    (⇑τx) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps τx tauX_vertices

/--
@isnad1 id=eq.0h0v.s10.c64f09037f7c from=translated src=- shape=0bc3b51f vocab=ccd6e22a
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_image_vertices :
    (⇑τy) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps τy tauY_vertices

/--
@isnad1 id=eq.0h0v.s10.f1fa3ac6fc06 from=translated src=- shape=0bc3b51f vocab=4e843d66
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_image_vertices :
    (⇑τz) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps τz tauZ_vertices

/--
@isnad1 id=eq.0h0v.s10.249871efbb1d from=translated src=- shape=05619176 vocab=00a72c60
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_preserves_polytope : (⇑τx) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices τx tauX_image_vertices

/--
@isnad1 id=eq.0h0v.s10.dd438936f6ee from=translated src=- shape=05619176 vocab=358df538
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_preserves_polytope : (⇑τy) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices τy tauY_image_vertices

/--
@isnad1 id=eq.0h0v.s10.f7fb632c0275 from=translated src=- shape=05619176 vocab=330ddd86
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_preserves_polytope : (⇑τz) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices τz tauZ_image_vertices

set_option maxHeartbeats 1000000 in
/-- Tabella completa dell'azione della rotazione aurea sui vertici.
@isnad1 id=and.0h0v.s14.9649c4166bff from=translated src=- shape=e056d3af vocab=8ce8a941
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_vertex_actions :
    ρ a0 = b0 ∧ ρ a1 = d2D ∧ ρ a2 = c0D ∧ ρ a3 = a1 ∧
    ρ a4 = a6 ∧ ρ a5 = c3D ∧ ρ a6 = d1D ∧ ρ a7 = b3 ∧
    ρ b0 = b2 ∧ ρ b1 = a5 ∧ ρ b2 = a2 ∧ ρ b3 = b1 ∧
    ρ c0D = a0 ∧ ρ c1D = d0 ∧ ρ c2D = d3 ∧ ρ c3D = a7 ∧
    ρ d0 = a4 ∧ ρ d1D = c1D ∧ ρ d2D = c2D ∧ ρ d3 = a3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply E3_ext
  all_goals norm_num [rhoFormula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals rw [golden_inv_nf] at *
  all_goals try simp only [golden_den_self] at *
  all_goals nlinarith [golden_sqrt_five, Real.goldenRatio_sq]

/--
@isnad1 id=mem.1h1v.s10.31edf4a37f7b from=translated src=- shape=7a298a1d vocab=8b7c8389
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    ρ v ∈ verticiDodeca := by
  rcases rho_vertex_actions with
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
      hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3⟩
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
    hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3]

/--
@isnad1 id=eq.0h0v.s10.8ef1dc329335 from=translated src=- shape=0bc3b51f vocab=a1f96df3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_image_vertices :
    (⇑ρ) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps ρ rho_vertices

/--
@isnad1 id=eq.0h0v.s10.0e6dbfd4f13a from=translated src=- shape=05619176 vocab=54cb0631
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_preserves_polytope : (⇑ρ) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices ρ rho_image_vertices

/-- La preservazione del politopo è stabile per composizione.
@isnad1 id=eq.2h2v.s12.478dfd081bd1 from=translated src=- shape=8484ebe5 vocab=0adbf720
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.preserves_trans (f g : E3 ≃ᵃⁱ[ℝ] E3)
    (hf : (⇑f) '' dodecaedro.toSet = dodecaedro.toSet)
    (hg : (⇑g) '' dodecaedro.toSet = dodecaedro.toSet) :
    (⇑(f.trans g)) '' dodecaedro.toSet = dodecaedro.toSet := by
  rw [show (⇑(f.trans g)) '' dodecaedro.toSet =
      (⇑g) '' ((⇑f) '' dodecaedro.toSet) by
        rw [← Set.image_comp]
        rfl,
    hf, hg]

/--
@isnad1 id=eq.0h0v.s10.5b73e9a4d9b2 from=translated src=- shape=6bc53fa2 vocab=8501bafa
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_a7_eq_b3 : ρ a7 = b3 := by
  simpa [x0, x1] using rho_x0

/-- Per ogni vertice, una simmetria globale che vi porta il vertice base.
@isnad1 id=ex.1h1v.s11.dea01b5d12dd from=translated src=- shape=a04d9e78 vocab=2b50e624
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.dodecaedro_vertex_transitive (v : E3) (hv : v ∈ dodecaedro.vertices) :
    ∃ g : E3 ≃ᵃⁱ[ℝ] E3,
      (⇑g) '' dodecaedro.toSet = dodecaedro.toSet ∧ g v₀ = v := by
  have hxy := preserves_trans τx τy tauX_preserves_polytope tauY_preserves_polytope
  have hxz := preserves_trans τx τz tauX_preserves_polytope tauZ_preserves_polytope
  have hyz := preserves_trans τy τz tauY_preserves_polytope tauZ_preserves_polytope
  have hxyz := preserves_trans (τx.trans τy) τz hxy tauZ_preserves_polytope
  have hB := rho_preserves_polytope
  have hBy := preserves_trans ρ τy hB tauY_preserves_polytope
  have hBz := preserves_trans ρ τz hB tauZ_preserves_polytope
  have hByz := preserves_trans (ρ.trans τy) τz hBy tauZ_preserves_polytope
  have hC := preserves_trans ρ σ hB sigma_preserves_polytope
  have hCx := preserves_trans (ρ.trans σ) τx hC tauX_preserves_polytope
  have hCz := preserves_trans (ρ.trans σ) τz hC tauZ_preserves_polytope
  have hCxz := preserves_trans ((ρ.trans σ).trans τx) τz hCx tauZ_preserves_polytope
  have hD := preserves_trans (ρ.trans σ) σ hC sigma_preserves_polytope
  have hDx := preserves_trans ((ρ.trans σ).trans σ) τx hD tauX_preserves_polytope
  have hDy := preserves_trans ((ρ.trans σ).trans σ) τy hD tauY_preserves_polytope
  have hDxy := preserves_trans (((ρ.trans σ).trans σ).trans τx) τy hDx
    tauY_preserves_polytope
  have hbaseB : ρ v₀ = b3 := by
    change ρ a7 = b3
    exact rho_a7_eq_b3
  have hbaseC : σ (ρ v₀) = c3D := by
    rw [hbaseB]
    apply E3_ext <;> simp [c3D, b3]
  have hbaseD : σ (σ (ρ v₀)) = d3 := by
    rw [hbaseC]
    apply E3_ext <;> simp [d3, c3D]
  change v ∈ verticiDodeca at hv
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(τx.trans τy).trans τz, hxyz, by
      apply E3_ext <;> simp [v₀, a0, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τx.trans τy, hxy, by
      apply E3_ext <;> simp [v₀, a1, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τx.trans τz, hxz, by
      apply E3_ext <;> simp [v₀, a2, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τx, tauX_preserves_polytope, by
      apply E3_ext <;> simp [v₀, a3]⟩
  · exact ⟨τy.trans τz, hyz, by
      apply E3_ext <;> simp [v₀, a4, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τy, tauY_preserves_polytope, by
      apply E3_ext <;> simp [v₀, a5]⟩
  · exact ⟨τz, tauZ_preserves_polytope, by
      apply E3_ext <;> simp [v₀, a6]⟩
  · exact ⟨σ, sigma_preserves_polytope, by simpa [v₀, a7] using sigma_a7⟩
  · exact ⟨(ρ.trans τy).trans τz, hByz, by
      show τz (τy (ρ v₀)) = b0
      rw [hbaseB]
      apply E3_ext <;> simp [b0, b3]⟩
  · exact ⟨ρ.trans τy, hBy, by
      show τy (ρ v₀) = b1
      rw [hbaseB]
      apply E3_ext <;> simp [b1, b3]⟩
  · exact ⟨ρ.trans τz, hBz, by
      show τz (ρ v₀) = b2
      rw [hbaseB]
      apply E3_ext <;> simp [b2, b3]⟩
  · exact ⟨ρ, hB, hbaseB⟩
  · exact ⟨((ρ.trans σ).trans τx).trans τz, hCxz, by
      show τz (τx (σ (ρ v₀))) = c0D
      rw [hbaseC]
      apply E3_ext <;> simp [c0D, c3D]⟩
  · exact ⟨(ρ.trans σ).trans τx, hCx, by
      show τx (σ (ρ v₀)) = c1D
      rw [hbaseC]
      apply E3_ext <;> simp [c1D, c3D]⟩
  · exact ⟨(ρ.trans σ).trans τz, hCz, by
      show τz (σ (ρ v₀)) = c2D
      rw [hbaseC]
      apply E3_ext <;> simp [c2D, c3D]⟩
  · exact ⟨ρ.trans σ, hC, hbaseC⟩
  · exact ⟨(((ρ.trans σ).trans σ).trans τx).trans τy, hDxy, by
      show τy (τx (σ (σ (ρ v₀)))) = d0
      rw [hbaseD]
      apply E3_ext <;> simp [d0, d3]⟩
  · exact ⟨((ρ.trans σ).trans σ).trans τx, hDx, by
      show τx (σ (σ (ρ v₀))) = d1D
      rw [hbaseD]
      apply E3_ext <;> simp [d1D, d3]⟩
  · exact ⟨((ρ.trans σ).trans σ).trans τy, hDy, by
      show τy (σ (σ (ρ v₀))) = d2D
      rw [hbaseD]
      apply E3_ext <;> simp [d2D, d3]⟩
  · exact ⟨(ρ.trans σ).trans σ, hD, hbaseD⟩

/-! ## Assemblaggio globale -/

/-! CONSEGNA

Sono certificati la transitività sui venti vertici, il trasferimento del fan
e della regolarità delle faccette, e il teorema conclusivo
`dodecaedro_cyclicallyRegular : dodecaedro.IsCyclicallyRegularOfType 5 3`.

SHA-256 canonico (tutto il contenuto precedente a questo blocco):
`c00556ea4a0b439bc18f0ead95bdccbadd3948603604a5dc3e12a6b18f547be4`
Compilazione: `lake env lean DodecaedroCompleto.lean` — exit 0, zero errori.
-/
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
