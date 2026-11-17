import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Fondamenta
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasferimento
import Tengoku.LeanEvalPlatonicClassification.Submission.TetraedroStadio2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/Solarys431/lean-eval-platonic-classification@3cd00dfd965e, `Submission/IcosaedroTestimone.lean`: removed 5 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
ICOSAEDRO — TESTIMONE (3,5), port a modulo (18 lug 2026, alba).

Sorgente: `teoremi/Platonici_Icosaedro.lean` (sol, fascicolo 9, CERTIFICATO
135/135). Definizioni da `Fondamenta`, trasferimento dal modulo, E3/norma dal
tetraedro; rinomine anti-collisione con suffisso `I`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Metric Tengoku.LeanEvalPlatonicClassification.FiniteConvexPolytope
open scoped RealInnerProductSpace

noncomputable section


variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-! ## Aritmetica aurea e i dodici vertici -/

local notation "φ" => Real.goldenRatio

theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_invI : φ⁻¹ = φ - 1 := by
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_inv_posI : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos

theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_inv_nfI : 2 / (1 + Real.sqrt 5) = φ - 1 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : 1 + Real.sqrt 5 ≠ 0 := by positivity
  rw [Real.goldenRatio]
  field_simp
  nlinarith

theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_sqrt_fiveI : Real.sqrt 5 = 2 * φ - 1 := by
  rw [Real.goldenRatio]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.golden_den_selfI : (1 + Real.sqrt 5) / (1 + Real.sqrt 5) = 1 := by
  field_simp

theorem _root_.Tengoku.LeanEvalPlatonicClassification.E3_extI {u v : E3} (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (h2 : u 2 = v 2) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

def _root_.Tengoku.LeanEvalPlatonicClassification.a0I : E3 := WithLp.toLp 2 ![-1, 0, -φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.a1I : E3 := WithLp.toLp 2 ![-1, 0,  φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.a2I : E3 := WithLp.toLp 2 ![ 1, 0, -φ]
def _root_.Tengoku.LeanEvalPlatonicClassification.a3I : E3 := WithLp.toLp 2 ![ 1, 0,  φ]

def _root_.Tengoku.LeanEvalPlatonicClassification.b0I : E3 := WithLp.toLp 2 ![-φ, -1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.b1I : E3 := WithLp.toLp 2 ![-φ,  1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.b2I : E3 := WithLp.toLp 2 ![ φ, -1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.b3I : E3 := WithLp.toLp 2 ![ φ,  1, 0]

def _root_.Tengoku.LeanEvalPlatonicClassification.c0I : E3 := WithLp.toLp 2 ![0, -φ, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c1I : E3 := WithLp.toLp 2 ![0, -φ,  1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c2I : E3 := WithLp.toLp 2 ![0,  φ, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.c3I : E3 := WithLp.toLp 2 ![0,  φ,  1]

open Classical in
def _root_.Tengoku.LeanEvalPlatonicClassification.verticiIcosa : Finset E3 :=
  {a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I}

theorem _root_.Tengoku.LeanEvalPlatonicClassification.norm_verticiIcosa : ∀ v ∈ verticiIcosa, ‖v‖ = Real.sqrt (φ + 2) := by
  intro v hv
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I]
  all_goals rw [norma_toLp]
  all_goals congr 1
  all_goals norm_num <;> nlinarith [Real.goldenRatio_sq]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.cosferico_extremePoints_icosa {B : Type*} [NormedAddCommGroup B]
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

def _root_.Tengoku.LeanEvalPlatonicClassification.icosaedro : FiniteConvexPolytope E3 where
  vertices := verticiIcosa
  nonempty := ⟨a0I, by simp [verticiIcosa]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiIcosa : Set E3) ⊆ sphere 0 (Real.sqrt (φ + 2)) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_verticiIcosa v (by exact_mod_cast hv)
    exact (cosferico_extremePoints_icosa 0 (Real.sqrt (φ + 2)) _ hV).symm

/-! ## Dimensione affine tre -/

def _root_.Tengoku.LeanEvalPlatonicClassification.spaceBasisPoints : Fin 4 → E3 := ![a3I, a1I, a2I, b3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.spaceBasisPoints_affineIndependent :
    AffineIndependent ℝ spaceBasisPoints := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun x : E3 => x j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [spaceBasisPoints, a3I, a1I, a2I, b3I, Fin.sum_univ_four] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at h0 h1 h2
  norm_num at h0 h1 h2
  ring_nf at h0 h2
  rw [Fin.sum_univ_four] at hu hv
  have hp : 0 < φ := Real.goldenRatio_pos
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e3 : u 3 = v 3 := by linarith
  have e1 : u 1 = v 1 := by nlinarith [hsq]
  have e2 : u 2 = v 2 := by nlinarith [hsq]
  have e0 : u 0 = v 0 := by linarith
  fin_cases i <;> assumption

theorem _root_.Tengoku.LeanEvalPlatonicClassification.range_spaceBasisPoints_subset :
    Set.range spaceBasisPoints ⊆ (verticiIcosa : Set E3) := by
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp [spaceBasisPoints, verticiIcosa]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.icosaedro_finrank :
    Module.finrank ℝ (vectorSpan ℝ (icosaedro.vertices : Set E3)) = 3 := by
  change Module.finrank ℝ (vectorSpan ℝ (verticiIcosa : Set E3)) = 3
  have htop : vectorSpan ℝ (Set.range spaceBasisPoints) = ⊤ :=
    spaceBasisPoints_affineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one
      (by simp)
  have hspan : vectorSpan ℝ (verticiIcosa : Set E3) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact vectorSpan_mono ℝ range_spaceBasisPoints_subset
  rw [hspan]
  simp

/-! ## La faccetta triangolare base -/

def _root_.Tengoku.LeanEvalPlatonicClassification.faceCycleI : Fin 3 → E3 := ![a3I, b3I, c3I]

def _root_.Tengoku.LeanEvalPlatonicClassification.F₀I : Set E3 := convexHull ℝ (Set.range faceCycleI)

def _root_.Tengoku.LeanEvalPlatonicClassification.lato : ℝ := 2

theorem _root_.Tengoku.LeanEvalPlatonicClassification.lato_pos : 0 < lato := by norm_num [lato]

def _root_.Tengoku.LeanEvalPlatonicClassification.supportLI : E3 →L[ℝ] ℝ :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 0 : E3 →L[ℝ] ℝ) +
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 1 : E3 →L[ℝ] ℝ) +
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2 : E3 →L[ℝ] ℝ)

@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_applyI (z : E3) : supportLI z = z 0 + z 1 + z 2 := by
  rfl

theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_faceCycleI (i : Fin 3) :
    supportLI (faceCycleI i) = φ + 1 := by
  fin_cases i <;> simp [faceCycleI, a3I, b3I, c3I, supportLI] <;> ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_mem_verticesI (i : Fin 3) :
    faceCycleI i ∈ (verticiIcosa : Set E3) := by
  fin_cases i <;> simp [faceCycleI, verticiIcosa]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_injectiveI : Function.Injective faceCycleI := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp [faceCycleI, a3I, b3I, c3I] at hij ⊢
  all_goals have h0 := congrArg (fun z : E3 => z 0) hij
  all_goals have h1 := congrArg (fun z : E3 => z 1) hij
  all_goals norm_num [faceCycleI, a3I, b3I, c3I] at h0 h1
  all_goals nlinarith [Real.goldenRatio_pos, Real.one_lt_goldenRatio]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_vertices_leI (v : E3) (hv : v ∈ verticiIcosa) :
    supportLI v ≤ φ + 1 := by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [supportLI, a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I,
    c0I, c1I, c2I, c3I]
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals nlinarith [Real.goldenRatio_sq]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_eq_imp_faceCycleI (v : E3) (hv : v ∈ verticiIcosa)
    (heq : supportLI v = φ + 1) : v ∈ Set.range faceCycleI := by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | skip
  all_goals exfalso
  all_goals norm_num [supportLI, a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I,
    c0I, c1I, c2I, c3I] at heq
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at heq
  all_goals nlinarith [Real.goldenRatio_sq]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_nonemptyI : F₀I.Nonempty := by
  exact ⟨a3I, subset_convexHull ℝ (Set.range faceCycleI) ⟨0, rfl⟩⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_subset_icosaedro : F₀I ⊆ icosaedro.toSet := by
  apply convexHull_mono
  rintro z ⟨i, rfl⟩
  exact faceCycle_mem_verticesI i

theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_polytope_leI (z : E3) (hz : z ∈ icosaedro.toSet) :
    supportLI z ≤ φ + 1 := by
  have hc : ConvexOn ℝ Set.univ supportLI :=
    supportLI.toLinearMap.convexOn convex_univ
  obtain ⟨v, hv, hzv⟩ := hc.exists_ge_of_mem_convexHull
    (Set.subset_univ (s := (verticiIcosa : Set E3))) hz
  exact hzv.trans (supportL_vertices_leI v hv)

theorem _root_.Tengoku.LeanEvalPlatonicClassification.supportL_eq_on_F₀I (z : E3) (hz : z ∈ F₀I) :
    supportLI z = φ + 1 := by
  have hc : ConvexOn ℝ Set.univ supportLI :=
    supportLI.toLinearMap.convexOn convex_univ
  have hcc : ConcaveOn ℝ Set.univ supportLI :=
    supportLI.toLinearMap.concaveOn convex_univ
  obtain ⟨u, ⟨i, rfl⟩, hzu⟩ := hc.exists_ge_of_mem_convexHull
    (Set.subset_univ (s := Set.range faceCycleI)) hz
  obtain ⟨v, ⟨j, rfl⟩, hvz⟩ := hcc.exists_le_of_mem_convexHull
    (Set.subset_univ (s := Set.range faceCycleI)) hz
  rw [supportL_faceCycleI i] at hzu
  rw [supportL_faceCycleI j] at hvz
  exact le_antisymm hzu hvz

theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_F₀_of_mem_polytope_support_eqI (z : E3) (hz : z ∈ icosaedro.toSet)
    (hzeq : supportLI z = φ + 1) : z ∈ F₀I := by
  classical
  change z ∈ convexHull ℝ (Set.range faceCycleI)
  change z ∈ convexHull ℝ (verticiIcosa : Set E3) at hz
  obtain ⟨w, hw0, hw1, hsum⟩ := (Finset.mem_convexHull').mp hz
  have hLsum : ∑ y ∈ verticiIcosa, w y * supportLI y = supportLI z := by
    have h := congrArg supportLI hsum
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  have hdef : ∑ y ∈ verticiIcosa, w y * ((φ + 1) - supportLI y) = 0 := by
    calc
      ∑ y ∈ verticiIcosa, w y * ((φ + 1) - supportLI y) =
          ∑ y ∈ verticiIcosa,
            (w y * (φ + 1) - w y * supportLI y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ y ∈ verticiIcosa, w y * (φ + 1)) -
            ∑ y ∈ verticiIcosa, w y * supportLI y := by
              rw [Finset.sum_sub_distrib]
      _ = (φ + 1) * (∑ y ∈ verticiIcosa, w y) -
            ∑ y ∈ verticiIcosa, w y * supportLI y := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (φ + 1) - supportLI z := by rw [hw1, hLsum]; ring
      _ = 0 := by rw [hzeq]; ring
  have hterm (y : E3) (hy : y ∈ verticiIcosa) :
      w y * ((φ + 1) - supportLI y) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef y hy
    intro u hu
    exact mul_nonneg (hw0 u hu)
      (sub_nonneg.mpr (supportL_vertices_leI u hu))
  have hwzero (y : E3) (hy : y ∈ verticiIcosa)
      (hyface : y ∉ Set.range faceCycleI) : w y = 0 := by
    have hne : (φ + 1) - supportLI y ≠ 0 := by
      intro h
      apply hyface
      apply supportL_eq_imp_faceCycleI y hy
      linarith
    exact (mul_eq_zero.mp (hterm y hy)).resolve_right hne
  let I := {y // y ∈ verticiIcosa}
  let z' : I → E3 := fun y =>
    if y.1 ∈ Set.range faceCycleI then y.1 else a3I
  refine mem_convexHull_of_exists_fintype
    (fun y : I => w y.1) z' ?_ ?_ ?_ ?_
  · intro y
    exact hw0 y.1 y.2
  · change (∑ y : {y // y ∈ verticiIcosa}, w y.1) = 1
    rw [← Finset.sum_subtype verticiIcosa (by simp) w]
    exact hw1
  · intro y
    dsimp [z']
    split_ifs with h
    · exact h
    · exact ⟨0, rfl⟩
  · have hzterm (y : I) : w y.1 • z' y = w y.1 • y.1 := by
      by_cases hface : y.1 ∈ Set.range faceCycleI
      · change w y.1 • (if y.1 ∈ Set.range faceCycleI then y.1 else a3I) = _
        rw [ite_eq_left hface]
      · change w y.1 • (if y.1 ∈ Set.range faceCycleI then y.1 else a3I) = _
        rw [ite_eq_right hface, hwzero y.1 y.2 hface]
        simp
    calc
      ∑ y : I, w y.1 • z' y = ∑ y : I, w y.1 • y.1 := by
        apply Fintype.sum_congr
        exact hzterm
      _ = ∑ y ∈ verticiIcosa, w y • y := by
        change (∑ y : {y // y ∈ verticiIcosa}, w y.1 • y.1) = _
        rw [← Finset.sum_subtype verticiIcosa (by simp) (fun y => w y • y)]
      _ = z := hsum

theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_isExposedI : IsExposed ℝ icosaedro.toSet F₀I := by
  intro _hne
  refine ⟨supportLI, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨F₀_subset_icosaedro hz, ?_⟩
    intro y hy
    rw [supportL_eq_on_F₀I z hz]
    exact supportL_polytope_leI y hy
  · rintro ⟨hzP, hzmax⟩
    have ha3P : a3I ∈ icosaedro.toSet :=
      F₀_subset_icosaedro (subset_convexHull ℝ (Set.range faceCycleI) ⟨0, rfl⟩)
    have hlo : φ + 1 ≤ supportLI z := by
      simpa [show supportLI a3I = φ + 1 from supportL_faceCycleI 0] using
        hzmax a3I ha3P
    have hhi := supportL_polytope_leI z hzP
    exact mem_F₀_of_mem_polytope_support_eqI z hzP (le_antisymm hhi hlo)

theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceCycle_affineIndependent : AffineIndependent ℝ faceCycleI := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun x : E3 => x j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [faceCycleI, a3I, b3I, c3I, Fin.sum_univ_three] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at h0 h1
  norm_num at h0 h1
  ring_nf at h0 h1
  rw [Fin.sum_univ_three] at hu hv
  have hp : 0 < φ := Real.goldenRatio_pos
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e0 : u 0 = v 0 := by nlinarith [hsq]
  have e1 : u 1 = v 1 := by nlinarith [hsq]
  have e2 : u 2 = v 2 := by linarith
  fin_cases i <;> assumption

theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_finrankI : Module.finrank ℝ (vectorSpan ℝ F₀I) = 2 := by
  rw [F₀I, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  exact faceCycle_affineIndependent.finrank_vectorSpan (n := 2) (by simp)

theorem _root_.Tengoku.LeanEvalPlatonicClassification.F₀_isFacetI : icosaedro.IsFacet F₀I :=
  ⟨⟨F₀_isExposedI, F₀_nonemptyI⟩, F₀_finrankI⟩

/-! ## La rotazione della faccetta: il 3-ciclo delle coordinate -/

def _root_.Tengoku.LeanEvalPlatonicClassification.coordinateLinear : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 3)

def _root_.Tengoku.LeanEvalPlatonicClassification.κ : E3 ≃ᵃⁱ[ℝ] E3 := coordinateLinear.toAffineIsometryEquiv

@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_apply_zero (z : E3) : κ z 0 = z 2 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_apply_one (z : E3) : κ z 1 = z 0 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_apply_two (z : E3) : κ z 2 = z 1 := rfl

/-! ## Rotazione aurea di ordine cinque attorno ad `a3` -/

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoFormulaI (z : E3) : E3 := WithLp.toLp 2 ![
  (z 0 - φ * z 1 + φ⁻¹ * z 2) / 2,
  (φ * z 0 + φ⁻¹ * z 1 - z 2) / 2,
  (φ⁻¹ * z 0 + z 1 + φ * z 2) / 2]

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinearMapI : E3 →ₗ[ℝ] E3 where
  toFun := rhoFormulaI
  map_add' u v := by
    apply E3_extI <;> simp [rhoFormulaI] <;> ring
  map_smul' c u := by
    apply E3_extI <;> simp [rhoFormulaI] <;> ring

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinearIsometryI : E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := rhoLinearMapI
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
    rw [golden_invI]
    ring_nf
    have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [hs]
    ring

def _root_.Tengoku.LeanEvalPlatonicClassification.rhoLinearI : E3 ≃ₗᵢ[ℝ] E3 :=
  rhoLinearIsometryI.toLinearIsometryEquiv rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.ρI : E3 ≃ᵃⁱ[ℝ] E3 := rhoLinearI.toAffineIsometryEquiv

@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_applyI (z : E3) : ρI z = rhoFormulaI z := rfl

set_option maxHeartbeats 1000000 in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_vertex_actionsI :
    ρI a0I = a0I ∧ ρI a1I = c1I ∧ ρI a2I = c2I ∧ ρI a3I = a3I ∧
    ρI b0I = c0I ∧ ρI b1I = b0I ∧ ρI b2I = b3I ∧ ρI b3I = c3I ∧
    ρI c0I = a2I ∧ ρI c1I = b2I ∧ ρI c2I = b1I ∧ ρI c3I = a1I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply E3_extI
  all_goals simp only [rho_applyI, rhoFormulaI, a0I, a1I, a2I, a3I,
    b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I]
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals rw [golden_invI]
  all_goals norm_num
  all_goals try rw [golden_sqrt_fiveI] at *
  all_goals nlinarith [Real.goldenRatio_sq]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_a3 : ρI a3I = a3I := rho_vertex_actionsI.2.2.2.1

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_verticesI (v : E3) (hv : v ∈ verticiIcosa) :
    ρI v ∈ verticiIcosa := by
  rcases rho_vertex_actionsI with
    ⟨ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
    hc0, hc1, hc2, hc3]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.image_verticiIcosa_eq_of_maps (g : E3 ≃ᵃⁱ[ℝ] E3)
    (hmap : ∀ v ∈ verticiIcosa, g v ∈ verticiIcosa) :
    (⇑g) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3) := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨v, hv, rfl⟩
    exact hmap v hv
  · rw [Set.ncard_image_of_injective _ g.injective]
  · exact verticiIcosa.finite_toSet

theorem _root_.Tengoku.LeanEvalPlatonicClassification.preserves_icosaedro_of_image_vertices (g : E3 ≃ᵃⁱ[ℝ] E3)
    (hv : (⇑g) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3)) :
    (⇑g) '' icosaedro.toSet = icosaedro.toSet := by
  show (⇑g) '' convexHull ℝ (verticiIcosa : Set E3) =
    convexHull ℝ (verticiIcosa : Set E3)
  have haff : (⇑g) '' convexHull ℝ (verticiIcosa : Set E3) =
      convexHull ℝ ((⇑g) '' (verticiIcosa : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometry.toAffineMap _
  rw [haff, hv]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_image_verticesI :
    (⇑ρI) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3) :=
  image_verticiIcosa_eq_of_maps ρI rho_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_preserves_polytopeI :
    (⇑ρI) '' icosaedro.toSet = icosaedro.toSet :=
  preserves_icosaedro_of_image_vertices ρI rho_image_verticesI

/-! ## Il fan delle cinque faccette -/

def _root_.Tengoku.LeanEvalPlatonicClassification.neighbor : Fin 5 → E3 := ![b3I, c3I, a1I, c1I, b2I]

@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotate5_zero : finRotate 5 (0 : Fin 5) = 1 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotate5_one : finRotate 5 (1 : Fin 5) = 2 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotate5_two : finRotate 5 (2 : Fin 5) = 3 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotate5_three : finRotate 5 (3 : Fin 5) = 4 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.rotate5_four : finRotate 5 (4 : Fin 5) = 0 := rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.fanCycle (i : Fin 5) : Fin 3 → E3 :=
  ![a3I, neighbor i, neighbor (finRotate 5 i)]

def _root_.Tengoku.LeanEvalPlatonicClassification.fanFaceI (i : Fin 5) : Set E3 :=
  convexHull ℝ (Set.range (fanCycle i))

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_zero : fanFaceI 0 = F₀I := by
  have h : fanCycle 0 = faceCycleI := by
    funext j
    fin_cases j <;> rfl
  rw [fanFaceI, F₀I, h]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_neighbor (i : Fin 5) :
    ρI (neighbor i) = neighbor (finRotate 5 i) := by
  rcases rho_vertex_actionsI with
    ⟨_, ha1, _, _, _, _, hb2, hb3, _, hc1, _, hc3⟩
  fin_cases i
  · exact hb3
  · exact hc3
  · exact ha1
  · exact hc1
  · exact hb2

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_fanCycle (i : Fin 5) (j : Fin 3) :
    ρI (fanCycle i j) = fanCycle (finRotate 5 i) j := by
  fin_cases j
  · exact rho_a3
  · exact rho_neighbor i
  · change ρI (neighbor (finRotate 5 i)) =
      neighbor (finRotate 5 (finRotate 5 i))
    exact rho_neighbor _

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_image_fanCycle (i : Fin 5) :
    (⇑ρI) '' Set.range (fanCycle i) =
      Set.range (fanCycle (finRotate 5 i)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [rho_fanCycle]
    exact Set.mem_range_self _
  · rintro ⟨j, rfl⟩
    refine ⟨fanCycle i j, Set.mem_range_self _, rho_fanCycle i j⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.rho_image_fanFace (i : Fin 5) :
    (⇑ρI) '' fanFaceI i = fanFaceI (finRotate 5 i) := by
  change (⇑ρI) '' convexHull ℝ (Set.range (fanCycle i)) =
    convexHull ℝ (Set.range (fanCycle (finRotate 5 i)))
  calc
    (⇑ρI) '' convexHull ℝ (Set.range (fanCycle i)) =
        convexHull ℝ ((⇑ρI) '' Set.range (fanCycle i)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        (ρI.toAffineEquiv.toAffineMap.image_convexHull (Set.range (fanCycle i)))
    _ = convexHull ℝ (Set.range (fanCycle (finRotate 5 i))) := by
      rw [rho_image_fanCycle]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_isFacet (i : Fin 5) : icosaedro.IsFacet (fanFaceI i) := by
  fin_cases i
  · simpa [fanFace_zero] using F₀_isFacetI
  · have h := FiniteConvexPolytope.isFacet_image icosaedro ρI
      rho_preserves_polytopeI (fanFace_isFacet 0)
    rw [rho_image_fanFace] at h
    exact h
  · have h := FiniteConvexPolytope.isFacet_image icosaedro ρI
      rho_preserves_polytopeI (fanFace_isFacet 1)
    rw [rho_image_fanFace] at h
    exact h
  · have h := FiniteConvexPolytope.isFacet_image icosaedro ρI
      rho_preserves_polytopeI (fanFace_isFacet 2)
    rw [rho_image_fanFace] at h
    exact h
  · have h := FiniteConvexPolytope.isFacet_image icosaedro ρI
      rho_preserves_polytopeI (fanFace_isFacet 3)
    rw [rho_image_fanFace] at h
    exact h

def _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport0 : E3 →L[ℝ] ℝ := supportLI

def _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport1 : E3 →L[ℝ] ℝ :=
  φ⁻¹ • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 1 : E3 →L[ℝ] ℝ) +
  φ • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2 : E3 →L[ℝ] ℝ)

def _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport2 : E3 →L[ℝ] ℝ :=
  (-φ⁻¹) • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 1 : E3 →L[ℝ] ℝ) +
  φ • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2 : E3 →L[ℝ] ℝ)

def _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport3 : E3 →L[ℝ] ℝ :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 0 : E3 →L[ℝ] ℝ) -
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 1 : E3 →L[ℝ] ℝ) +
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2 : E3 →L[ℝ] ℝ)

def _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport4 : E3 →L[ℝ] ℝ :=
  φ • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 0 : E3 →L[ℝ] ℝ) +
  φ⁻¹ • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2 : E3 →L[ℝ] ℝ)

def _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport : Fin 5 → (E3 →L[ℝ] ℝ) :=
  ![fanSupport0, fanSupport1, fanSupport2, fanSupport3, fanSupport4]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport_fanCycle (i : Fin 5) (j : Fin 3) :
    fanSupport i (fanCycle i j) = φ + 1 := by
  fin_cases i <;> fin_cases j
  all_goals simp only [rotate5_zero, rotate5_one, rotate5_two,
    rotate5_three, rotate5_four] at *
  all_goals norm_num [Fin.add_def, fanSupport, fanSupport0,
    fanSupport1, fanSupport2,
    fanSupport3, fanSupport4, supportLI, fanCycle, neighbor,
    a3I, b3I, c3I, a1I, c1I, b2I]
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals try simp only [golden_inv_nfI, golden_den_selfI] at *
  all_goals nlinarith [Real.goldenRatio_sq]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_support (i : Fin 5) (z : E3) (hz : z ∈ fanFaceI i) :
    fanSupport i z = φ + 1 := by
  have hc : ConvexOn ℝ Set.univ (fanSupport i) :=
    (fanSupport i).toLinearMap.convexOn convex_univ
  have hcc : ConcaveOn ℝ Set.univ (fanSupport i) :=
    (fanSupport i).toLinearMap.concaveOn convex_univ
  obtain ⟨u, ⟨j, rfl⟩, hzu⟩ := hc.exists_ge_of_mem_convexHull
    (Set.subset_univ (s := Set.range (fanCycle i))) hz
  obtain ⟨v, ⟨k, rfl⟩, hvz⟩ := hcc.exists_le_of_mem_convexHull
    (Set.subset_univ (s := Set.range (fanCycle i))) hz
  rw [fanSupport_fanCycle i j] at hzu
  rw [fanSupport_fanCycle i k] at hvz
  exact le_antisymm hzu hvz

theorem _root_.Tengoku.LeanEvalPlatonicClassification.a3_mem_fanFace (i : Fin 5) : a3I ∈ fanFaceI i := by
  exact subset_convexHull ℝ (Set.range (fanCycle i)) ⟨0, rfl⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.neighbor_mem_fanFace (i : Fin 5) : neighbor i ∈ fanFaceI i := by
  exact subset_convexHull ℝ (Set.range (fanCycle i)) ⟨1, rfl⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.next_neighbor_mem_fanFace (i : Fin 5) :
    neighbor (finRotate 5 i) ∈ fanFaceI i := by
  exact subset_convexHull ℝ (Set.range (fanCycle i)) ⟨2, rfl⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.neighbor_ne_a3 (i : Fin 5) : neighbor i ≠ a3I := by
  intro h
  fin_cases i
  · have h1 := congrArg (fun z : E3 => z 1) h
    norm_num [neighbor, a3I, b3I] at h1
  · have h1 := congrArg (fun z : E3 => z 1) h
    norm_num [neighbor, a3I, c3I] at h1
    nlinarith [Real.sqrt_nonneg 5]
  · have h0 := congrArg (fun z : E3 => z 0) h
    norm_num [neighbor, a3I, a1I] at h0
  · have h1 := congrArg (fun z : E3 => z 1) h
    norm_num [neighbor, a3I, c1I] at h1
    nlinarith [Real.sqrt_nonneg 5]
  · have h1 := congrArg (fun z : E3 => z 1) h
    norm_num [neighbor, a3I, b2I] at h1

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_spigoloI (i : Fin 5) :
    ∃ x, x ≠ a3I ∧ x ∈ fanFaceI i ∩ fanFaceI (finRotate 5 i) := by
  refine ⟨neighbor (finRotate 5 i), neighbor_ne_a3 _,
    next_neighbor_mem_fanFace i, neighbor_mem_fanFace _⟩

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_injectiveI : Function.Injective fanFaceI := by
  intro i j hij
  have hm0 : neighbor i ∈ fanFaceI j := hij ▸ neighbor_mem_fanFace i
  have hm1 : neighbor (finRotate 5 i) ∈ fanFaceI j :=
    hij ▸ next_neighbor_mem_fanFace i
  have e0 := fanFace_support j (neighbor i) hm0
  have e1 := fanFace_support j (neighbor (finRotate 5 i)) hm1
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals exfalso
  all_goals simp only [rotate5_zero, rotate5_one, rotate5_two,
    rotate5_three, rotate5_four] at e0 e1
  all_goals norm_num [Fin.add_def, fanSupport, fanSupport0,
    fanSupport1, fanSupport2,
    fanSupport3, fanSupport4, supportLI, neighbor,
    a3I, b3I, c3I, a1I, c1I, b2I] at e0 e1
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at e0 e1
  all_goals try simp only [golden_inv_nfI, golden_den_selfI] at e0 e1
  all_goals nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]

set_option maxHeartbeats 1000000 in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanFace_spigolo_dueI (i j : Fin 5) (z : E3)
    (hz : z ∈ fanFaceI i ∩ fanFaceI (finRotate 5 i)) (hz_ne : z ≠ a3I)
    (hzj : z ∈ fanFaceI j) : j = i ∨ j = finRotate 5 i := by
  by_cases hji : j = i
  · exact Or.inl hji
  by_cases hjr : j = finRotate 5 i
  · exact Or.inr hjr
  exfalso
  apply hz_ne
  have e0 := fanFace_support i z hz.1
  have e1 := fanFace_support (finRotate 5 i) z hz.2
  have ej := fanFace_support j z hzj
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals apply E3_extI
  all_goals simp only [rotate5_zero, rotate5_one, rotate5_two,
    rotate5_three, rotate5_four] at e0 e1 ej
  all_goals norm_num [Fin.add_def, fanSupport, fanSupport0,
    fanSupport1, fanSupport2,
    fanSupport3, fanSupport4, supportLI, a3I] at e0 e1 ej ⊢
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at e0 e1 ej ⊢
  all_goals try simp only [golden_inv_nfI, golden_den_selfI] at e0 e1 ej
  all_goals nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]

/-! ## Completezza locale del fan -/

open Classical in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.icosa_exposedFace_eq_convexHull_vertices {F : Set E3}
    (hF : icosaedro.IsFace F) :
    F = convexHull ℝ
      ((icosaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := icosaedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact icosaedro.toSet := by
    exact icosaedro.vertices.finite_toSet.isCompact_convexHull ℝ
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ icosaedro.toSet.extremePoints ℝ) ↔
      x ∈ icosaedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← icosaedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((icosaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.e₀I : E3 := WithLp.toLp 2 ![1, 0, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.e₁I : E3 := WithLp.toLp 2 ![0, 1, 0]
def _root_.Tengoku.LeanEvalPlatonicClassification.e₂I : E3 := WithLp.toLp 2 ![0, 0, 1]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.E3_decompI (z : E3) :
    z = z 0 • e₀I + z 1 • e₁I + z 2 • e₂I := by
  apply E3_extI <;> simp [e₀I, e₁I, e₂I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_apply_coordsI (l : E3 →L[ℝ] ℝ) (z : E3) :
    l z = z 0 * l e₀I + z 1 * l e₁I + z 2 * l e₂I := by
  conv_lhs => rw [E3_decompI z]
  simp only [map_add, map_smul, smul_eq_mul]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_a0 (l : E3 →L[ℝ] ℝ) :
    l a0I = -l e₀I - φ * l e₂I := by
  rw [functional_apply_coordsI]
  simp [a0I]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_a1 (l : E3 →L[ℝ] ℝ) :
    l a1I = -l e₀I + φ * l e₂I := by
  rw [functional_apply_coordsI]
  simp [a1I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_a2 (l : E3 →L[ℝ] ℝ) :
    l a2I = l e₀I - φ * l e₂I := by
  rw [functional_apply_coordsI]
  simp [a2I]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_a3 (l : E3 →L[ℝ] ℝ) :
    l a3I = l e₀I + φ * l e₂I := by
  rw [functional_apply_coordsI]
  simp [a3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b0I (l : E3 →L[ℝ] ℝ) :
    l b0I = -φ * l e₀I - l e₁I := by
  rw [functional_apply_coordsI]
  simp [b0I]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b1I (l : E3 →L[ℝ] ℝ) :
    l b1I = -φ * l e₀I + l e₁I := by
  rw [functional_apply_coordsI]
  simp [b1I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b2I (l : E3 →L[ℝ] ℝ) :
    l b2I = φ * l e₀I - l e₁I := by
  rw [functional_apply_coordsI]
  simp [b2I]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_b3I (l : E3 →L[ℝ] ℝ) :
    l b3I = φ * l e₀I + l e₁I := by
  rw [functional_apply_coordsI]
  simp [b3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c0I (l : E3 →L[ℝ] ℝ) :
    l c0I = -φ * l e₁I - l e₂I := by
  rw [functional_apply_coordsI]
  simp [c0I]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c1I (l : E3 →L[ℝ] ℝ) :
    l c1I = -φ * l e₁I + l e₂I := by
  rw [functional_apply_coordsI]
  simp [c1I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c2I (l : E3 →L[ℝ] ℝ) :
    l c2I = φ * l e₁I - l e₂I := by
  rw [functional_apply_coordsI]
  simp [c2I]
  ring

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_c3I (l : E3 →L[ℝ] ℝ) :
    l c3I = φ * l e₁I + l e₂I := by
  rw [functional_apply_coordsI]
  simp [c3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanCycle_mem_vertices (i : Fin 5) (j : Fin 3) :
    fanCycle i j ∈ (verticiIcosa : Set E3) := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [Fin.add_def, fanCycle, neighbor, verticiIcosa]

set_option maxHeartbeats 1000000 in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fanSupport_eq_imp_fanCycle (i : Fin 5) (v : E3)
    (hv : v ∈ verticiIcosa) (heq : fanSupport i v = φ + 1) :
    v ∈ Set.range (fanCycle i) := by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  fin_cases i
  all_goals simp only [verticiIcosa, Finset.mem_insert,
    Finset.mem_singleton] at hv
  all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | skip
  all_goals exfalso
  all_goals norm_num [Fin.add_def, fanSupport, fanSupport0, fanSupport1,
    fanSupport2, fanSupport3, fanSupport4, supportLI, fanCycle, neighbor,
    a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I] at heq
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at heq
  all_goals try simp only [golden_inv_nfI, golden_den_selfI] at heq
  all_goals nlinarith [Real.goldenRatio_sq]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.functional_shape (i : Fin 5) (l : E3 →L[ℝ] ℝ)
    (hi : l (neighbor i) = l a3I)
    (hin : l (neighbor (finRotate 5 i)) = l a3I) :
    ∃ t : ℝ, ∀ z : E3, l z = t * fanSupport i z := by
  fin_cases i
  · refine ⟨l e₀I, ?_⟩
    intro z
    have e0 := hi
    have e1 := hin
    change l b3I = l a3I at e0
    change l c3I = l a3I at e1
    rw [functional_b3I, functional_a3] at e0
    rw [functional_c3I, functional_a3] at e1
    have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
    have ec : l e₂I = l e₀I := by
      linear_combination (1 / 2) * e1 - (φ / 2) * e0 -
        ((l e₂I - l e₀I) / 2) * hs
    have eb : l e₁I = l e₀I := by
      rw [ec] at e0
      linarith
    rw [functional_apply_coordsI]
    change z 0 * l e₀I + z 1 * l e₁I + z 2 * l e₂I =
      l e₀I * (z 0 + z 1 + z 2)
    rw [eb, ec]
    ring
  · refine ⟨φ * l e₁I, ?_⟩
    intro z
    have e0 := hi
    have e1 := hin
    change l c3I = l a3I at e0
    change l a1I = l a3I at e1
    rw [functional_c3I, functional_a3] at e0
    rw [functional_a1, functional_a3] at e1
    have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
    have ea : l e₀I = 0 := by linarith [e1]
    have ec : l e₂I = φ ^ 2 * l e₁I := by
      linear_combination -φ * e0 - l e₂I * hs - φ * ea
    rw [functional_apply_coordsI]
    change z 0 * l e₀I + z 1 * l e₁I + z 2 * l e₂I =
      (φ * l e₁I) * (φ⁻¹ * z 1 + φ * z 2)
    rw [golden_invI]
    rw [ea, ec]
    linear_combination (-z 1 * l e₁I) * hs
  · refine ⟨-φ * l e₁I, ?_⟩
    intro z
    have e0 := hi
    have e1 := hin
    change l a1I = l a3I at e0
    change l c1I = l a3I at e1
    rw [functional_a1, functional_a3] at e0
    rw [functional_c1I, functional_a3] at e1
    have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
    have ea : l e₀I = 0 := by linarith [e0]
    have ec : l e₂I = -(φ ^ 2 * l e₁I) := by
      linear_combination -φ * e1 - l e₂I * hs - φ * ea
    rw [functional_apply_coordsI]
    change z 0 * l e₀I + z 1 * l e₁I + z 2 * l e₂I =
      (-φ * l e₁I) * (-φ⁻¹ * z 1 + φ * z 2)
    rw [golden_invI]
    rw [ea, ec]
    linear_combination (-z 1 * l e₁I) * hs
  · refine ⟨l e₀I, ?_⟩
    intro z
    have e0 := hi
    have e1 := hin
    change l c1I = l a3I at e0
    change l b2I = l a3I at e1
    rw [functional_c1I, functional_a3] at e0
    rw [functional_b2I, functional_a3] at e1
    have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
    have ec : l e₂I = l e₀I := by
      linear_combination (1 / 2) * e0 - (φ / 2) * e1 +
        ((l e₀I - l e₂I) / 2) * hs
    have eb : l e₁I = -l e₀I := by
      linear_combination (-φ / 2) * e0 + ((φ - 1) / 2) * e1 -
        ((l e₀I + l e₁I) / 2) * hs
    rw [functional_apply_coordsI]
    change z 0 * l e₀I + z 1 * l e₁I + z 2 * l e₂I =
      l e₀I * (z 0 - z 1 + z 2)
    rw [eb, ec]
    ring
  · refine ⟨(φ - 1) * l e₀I, ?_⟩
    intro z
    have e0 := hi
    have e1 := hin
    change l b2I = l a3I at e0
    change l b3I = l a3I at e1
    rw [functional_b2I, functional_a3] at e0
    rw [functional_b3I, functional_a3] at e1
    have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
    have eb : l e₁I = 0 := by linarith [e0, e1]
    have ec : l e₂I = (φ - 1) ^ 2 * l e₀I := by
      linear_combination ((1 - φ) / 2) * e0 + ((1 - φ) / 2) * e1 -
        l e₂I * hs
    rw [functional_apply_coordsI]
    change z 0 * l e₀I + z 1 * l e₁I + z 2 * l e₂I =
      ((φ - 1) * l e₀I) * (φ * z 0 + φ⁻¹ * z 2)
    rw [golden_invI]
    rw [eb, ec]
    linear_combination (-z 0 * l e₀I) * hs

theorem _root_.Tengoku.LeanEvalPlatonicClassification.nonadjacent_neighbor_relations (l : E3 →L[ℝ] ℝ)
    (hmax : ∀ v ∈ verticiIcosa, l v ≤ l a3I) :
    (l b3I = l a3I → l a1I = l a3I → l c3I = l a3I) ∧
    (l b3I = l a3I → l c1I = l a3I → l b2I = l a3I) ∧
    (l c3I = l a3I → l c1I = l a3I → l b3I = l a3I) ∧
    (l c3I = l a3I → l b2I = l a3I → l b3I = l a3I) ∧
    (l a1I = l a3I → l b2I = l a3I → l c1I = l a3I) := by
  let g0 : ℝ := l a3I - l b3I
  let g1 : ℝ := l a3I - l c3I
  let g2 : ℝ := l a3I - l a1I
  let g3 : ℝ := l a3I - l c1I
  let g4 : ℝ := l a3I - l b2I
  have hg0 : 0 ≤ g0 := sub_nonneg.mpr (hmax b3I (by simp [verticiIcosa]))
  have hg1 : 0 ≤ g1 := sub_nonneg.mpr (hmax c3I (by simp [verticiIcosa]))
  have hg2 : 0 ≤ g2 := sub_nonneg.mpr (hmax a1I (by simp [verticiIcosa]))
  have hg3 : 0 ≤ g3 := sub_nonneg.mpr (hmax c1I (by simp [verticiIcosa]))
  have hg4 : 0 ≤ g4 := sub_nonneg.mpr (hmax b2I (by simp [verticiIcosa]))
  have hp : 0 < φ := Real.goldenRatio_pos
  have hp1 : 0 < φ - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
  have r02 : g3 + φ * g1 = g0 + φ * g2 := by
    dsimp [g0, g1, g2, g3]
    rw [functional_a3, functional_b3I, functional_c3I, functional_a1,
      functional_c1I]
    linear_combination (-l e₁I + l e₂I) * hs
  have r03 : g1 + φ * g4 = φ * g0 + g3 := by
    dsimp [g0, g1, g3, g4]
    rw [functional_a3, functional_b3I, functional_c3I, functional_c1I,
      functional_b2I]
    ring
  have r13 : g2 + (φ - 1) * g0 = g1 + (φ - 1) * g3 := by
    dsimp [g0, g1, g2, g3]
    rw [functional_a3, functional_b3I, functional_c3I, functional_a1,
      functional_c1I]
    linear_combination (-l e₀I - l e₁I) * hs
  have r14 : g0 + (φ - 1) * g2 = g1 + (φ - 1) * g4 := by
    dsimp [g0, g1, g2, g4]
    rw [functional_a3, functional_b3I, functional_c3I, functional_a1,
      functional_b2I]
    linear_combination (l e₀I - l e₂I) * hs
  have r24 : g3 + (φ - 1) * g0 = (φ - 1) * g2 + g4 := by
    dsimp [g0, g2, g3, g4]
    rw [functional_a3, functional_b3I, functional_a1, functional_c1I,
      functional_b2I]
    linear_combination (-l e₀I + l e₂I) * hs
  constructor
  · intro h0 h2
    have z0 : g0 = 0 := by dsimp [g0]; linarith
    have z2 : g2 = 0 := by dsimp [g2]; linarith
    have hm := mul_nonneg hp.le hg1
    have z1 : g1 = 0 := by nlinarith [r02]
    dsimp [g1] at z1
    linarith
  constructor
  · intro h0 h3
    have z0 : g0 = 0 := by dsimp [g0]; linarith
    have z3 : g3 = 0 := by dsimp [g3]; linarith
    have hm := mul_nonneg hp.le hg4
    have z4 : g4 = 0 := by nlinarith [r03]
    dsimp [g4] at z4
    linarith
  constructor
  · intro h1 h3
    have z1 : g1 = 0 := by dsimp [g1]; linarith
    have z3 : g3 = 0 := by dsimp [g3]; linarith
    have hm := mul_nonneg hp1.le hg0
    have z0 : g0 = 0 := by nlinarith [r13]
    dsimp [g0] at z0
    linarith
  constructor
  · intro h1 h4
    have z1 : g1 = 0 := by dsimp [g1]; linarith
    have z4 : g4 = 0 := by dsimp [g4]; linarith
    have hm := mul_nonneg hp1.le hg2
    have z0 : g0 = 0 := by nlinarith [r14]
    dsimp [g0] at z0
    linarith
  · intro h2 h4
    have z2 : g2 = 0 := by dsimp [g2]; linarith
    have z4 : g4 = 0 := by dsimp [g4]; linarith
    have hm := mul_nonneg hp1.le hg0
    have z3 : g3 = 0 := by nlinarith [r24]
    dsimp [g3] at z3
    linarith

set_option maxHeartbeats 1000000 in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.local_maximizer_dichotomyI (l : E3 →L[ℝ] ℝ)
    (hmax : ∀ v ∈ verticiIcosa, l v ≤ l a3I)
    (v : E3) (hv : v ∈ verticiIcosa) (heq : l v = l a3I) :
    v = a3I ∨
    (v = b3I ∧ l b3I = l a3I) ∨
    (v = c3I ∧ l c3I = l a3I) ∨
    (v = a1I ∧ l a1I = l a3I) ∨
    (v = c1I ∧ l c1I = l a3I) ∨
    (v = b2I ∧ l b2I = l a3I) ∨
    (l b3I = l a3I ∧ l c3I = l a3I) ∨
    (l c3I = l a3I ∧ l a1I = l a3I) ∨
    (l a1I = l a3I ∧ l c1I = l a3I) ∨
    (l c1I = l a3I ∧ l b2I = l a3I) ∨
    (l b2I = l a3I ∧ l b3I = l a3I) := by
  let g0 : ℝ := l a3I - l b3I
  let g1 : ℝ := l a3I - l c3I
  let g2 : ℝ := l a3I - l a1I
  let g3 : ℝ := l a3I - l c1I
  let g4 : ℝ := l a3I - l b2I
  have hg0 : 0 ≤ g0 := sub_nonneg.mpr (hmax b3I (by simp [verticiIcosa]))
  have hg1 : 0 ≤ g1 := sub_nonneg.mpr (hmax c3I (by simp [verticiIcosa]))
  have hg2 : 0 ≤ g2 := sub_nonneg.mpr (hmax a1I (by simp [verticiIcosa]))
  have hg3 : 0 ≤ g3 := sub_nonneg.mpr (hmax c1I (by simp [verticiIcosa]))
  have hg4 : 0 ≤ g4 := sub_nonneg.mpr (hmax b2I (by simp [verticiIcosa]))
  have hp : 0 < φ := Real.goldenRatio_pos
  have hp1 : 0 < φ - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hs : φ ^ 2 - φ - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
  have rel_a0 : l a3I - l a0I = g0 + g1 + φ * g3 := by
    dsimp [g0, g1, g3]
    rw [functional_a3, functional_a0, functional_b3I, functional_c3I,
      functional_c1I]
    linear_combination (-l e₁I - l e₂I) * hs
  have rel_a2 : l a3I - l a2I = g0 + (φ - 1) * g2 + g4 := by
    dsimp [g0, g2, g4]
    rw [functional_a3, functional_a2, functional_b3I, functional_a1,
      functional_b2I]
    ring
  have rel_b0 : l a3I - l b0I = (φ - 1) * g0 + g2 + g3 := by
    dsimp [g0, g2, g3]
    rw [functional_a3, functional_b0I, functional_b3I, functional_a1,
      functional_c1I]
    linear_combination (l e₀I - l e₂I) * hs
  have rel_b1 : l a3I - l b1I = g1 + g2 + (φ - 1) * g4 := by
    dsimp [g1, g2, g4]
    rw [functional_a3, functional_b1I, functional_c3I, functional_a1,
      functional_b2I]
    linear_combination (l e₀I - l e₂I) * hs
  have rel_c0 : l a3I - l c0I = (φ - 1) * g1 + g3 + g4 := by
    dsimp [g1, g3, g4]
    rw [functional_a3, functional_c0I, functional_c3I, functional_c1I,
      functional_b2I]
    linear_combination (l e₁I - l e₂I) * hs
  have rel_c2 : l a3I - l c2I = g0 + g1 + (φ - 1) * g3 := by
    dsimp [g0, g1, g3]
    rw [functional_a3, functional_c2I, functional_b3I, functional_c3I,
      functional_c1I]
    linear_combination (-l e₁I - l e₂I) * hs
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · have hz0 : g0 = 0 := by
      have hm := mul_nonneg hp.le hg3
      nlinarith [rel_a0]
    have hz1 : g1 = 0 := by
      have hm := mul_nonneg hp.le hg3
      nlinarith [rel_a0]
    have e0 : l b3I = l a3I := by dsimp [g0] at hz0; linarith
    have e1 : l c3I = l a3I := by dsimp [g1] at hz1; linarith
    aesop
  · aesop
  · have hz0 : g0 = 0 := by
      have hm := mul_nonneg hp1.le hg2
      nlinarith [rel_a2]
    have hz4 : g4 = 0 := by
      have hm := mul_nonneg hp1.le hg2
      nlinarith [rel_a2]
    have e0 : l b3I = l a3I := by dsimp [g0] at hz0; linarith
    have e4 : l b2I = l a3I := by dsimp [g4] at hz4; linarith
    aesop
  · aesop
  · have hz2 : g2 = 0 := by
      have hm := mul_nonneg hp1.le hg0
      nlinarith [rel_b0]
    have hz3 : g3 = 0 := by
      have hm := mul_nonneg hp1.le hg0
      nlinarith [rel_b0]
    have e2 : l a1I = l a3I := by dsimp [g2] at hz2; linarith
    have e3 : l c1I = l a3I := by dsimp [g3] at hz3; linarith
    aesop
  · have hz1 : g1 = 0 := by
      have hm := mul_nonneg hp1.le hg4
      nlinarith [rel_b1]
    have hz2 : g2 = 0 := by
      have hm := mul_nonneg hp1.le hg4
      nlinarith [rel_b1]
    have e1 : l c3I = l a3I := by dsimp [g1] at hz1; linarith
    have e2 : l a1I = l a3I := by dsimp [g2] at hz2; linarith
    aesop
  · aesop
  · aesop
  · have hz3 : g3 = 0 := by
      have hm := mul_nonneg hp1.le hg1
      nlinarith [rel_c0]
    have hz4 : g4 = 0 := by
      have hm := mul_nonneg hp1.le hg1
      nlinarith [rel_c0]
    have e3 : l c1I = l a3I := by dsimp [g3] at hz3; linarith
    have e4 : l b2I = l a3I := by dsimp [g4] at hz4; linarith
    aesop
  · aesop
  · have hz0 : g0 = 0 := by
      have hm := mul_nonneg hp1.le hg3
      nlinarith [rel_c2]
    have hz1 : g1 = 0 := by
      have hm := mul_nonneg hp1.le hg3
      nlinarith [rel_c2]
    have e0 : l b3I = l a3I := by dsimp [g0] at hz0; linarith
    have e1 : l c3I = l a3I := by dsimp [g1] at hz1; linarith
    aesop
  · aesop

theorem _root_.Tengoku.LeanEvalPlatonicClassification.icosaedro_toSet_finrank :
    Module.finrank ℝ (vectorSpan ℝ icosaedro.toSet) = 3 := by
  rw [FiniteConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact icosaedro_finrank

open Classical in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.facet_eq_fanFace_of_shape {F : Set E3} {l : E3 →L[ℝ] ℝ}
    (hFS : F = convexHull ℝ
      (((icosaedro.vertices.filter (· ∈ F)) : Finset E3) : Set E3))
    (vertex_mem_iff : ∀ y : E3, y ∈ verticiIcosa →
      (y ∈ F ↔ l y = l a3I))
    (i : Fin 5) (t : ℝ) (ht : t ≠ 0)
    (shape : ∀ z : E3, l z = t * fanSupport i z) :
    F = fanFaceI i := by
  classical
  have ha : fanSupport i a3I = φ + 1 := by
    simpa [fanCycle] using fanSupport_fanCycle i 0
  have hset :
      (((icosaedro.vertices.filter (· ∈ F)) : Finset E3) : Set E3) =
        Set.range (fanCycle i) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ icosaedro.vertices ∧ y ∈ F :=
        Finset.mem_filter.mp hy
      have hly : l y = l a3I :=
        (vertex_mem_iff y hy'.1).1 hy'.2
      have hmul : t * fanSupport i y = t * (φ + 1) := by
        calc
          t * fanSupport i y = l y := (shape y).symm
          _ = l a3I := hly
          _ = t * fanSupport i a3I := shape a3I
          _ = t * (φ + 1) := by rw [ha]
      have hsupp : fanSupport i y = φ + 1 :=
        mul_left_cancel₀ ht hmul
      exact fanSupport_eq_imp_fanCycle i y hy'.1 hsupp
    · rintro ⟨j, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨fanCycle_mem_vertices i j, ?_⟩
      apply (vertex_mem_iff (fanCycle i j)
        (fanCycle_mem_vertices i j)).2
      rw [shape, shape, fanSupport_fanCycle, ha]
  rw [hFS, hset]
  rfl

set_option maxHeartbeats 2000000 in
theorem _root_.Tengoku.LeanEvalPlatonicClassification.incident_facet_classificationI {F : Set E3}
    (hF : icosaedro.IsFacet F) (ha3 : a3I ∈ F) :
    ∃ i : Fin 5, F = fanFaceI i := by
  classical
  obtain ⟨l, hFl⟩ := hF.1.1 hF.1.2
  have haChar : a3I ∈ {x ∈ icosaedro.toSet |
      ∀ y ∈ icosaedro.toSet, l y ≤ l x} := by
    rw [← hFl]
    exact ha3
  have hmaxP : ∀ y ∈ icosaedro.toSet, l y ≤ l a3I := haChar.2
  have hmaxV : ∀ y ∈ verticiIcosa, l y ≤ l a3I := by
    intro y hy
    apply hmaxP y
    exact subset_convexHull ℝ (verticiIcosa : Set E3) hy
  have vertex_mem_iff (y : E3) (hy : y ∈ verticiIcosa) :
      y ∈ F ↔ l y = l a3I := by
    rw [hFl]
    constructor
    · intro h
      apply le_antisymm (hmaxV y hy)
      exact h.2 a3I haChar.1
    · intro heq
      refine ⟨subset_convexHull ℝ (verticiIcosa : Set E3) hy, ?_⟩
      intro z hz
      rw [heq]
      exact hmaxP z hz
  have hlne : l ≠ 0 := by
    intro hl
    have hFP : F = icosaedro.toSet := by
      apply Set.Subset.antisymm hF.1.1.subset
      intro z hz
      rw [hFl]
      refine ⟨hz, ?_⟩
      intro y hy
      simp [hl]
    have hd := hF.2
    rw [hFP, icosaedro_toSet_finrank] at hd
    omega
  let S : Finset E3 := icosaedro.vertices.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S : Set E3) :=
    icosa_exposedFace_eq_convexHull_vertices hF.1
  have hdS : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hd := hF.2
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull,
      direction_affineSpan] at hd
    exact hd
  have rank_small (u : E3)
      (hu : ∀ y ∈ verticiIcosa, l y = l a3I → y = a3I ∨ y = u) : False := by
    let pair : Fin 2 → E3 := ![a3I, u]
    have hsub : (S : Set E3) ⊆ Set.range pair := by
      intro y hy
      have hy' : y ∈ icosaedro.vertices ∧ y ∈ F :=
        Finset.mem_filter.mp hy
      rcases hu y hy'.1 ((vertex_mem_iff y hy'.1).1 hy'.2) with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    have hmono : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) ≤
        Module.finrank ℝ (vectorSpan ℝ (Set.range pair)) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    have hp : Module.finrank ℝ (vectorSpan ℝ (Set.range pair)) ≤ 1 :=
      finrank_vectorSpan_range_le ℝ pair (by simp)
    omega
  let h0 : Prop := l b3I = l a3I
  let h1 : Prop := l c3I = l a3I
  let h2 : Prop := l a1I = l a3I
  let h3 : Prop := l c1I = l a3I
  let h4 : Prop := l b2I = l a3I
  by_cases h01 : h0 ∧ h1
  · obtain ⟨t, shape⟩ := functional_shape 0 l h01.1 h01.2
    have ht : t ≠ 0 := by
      intro htz
      apply hlne
      ext z
      rw [shape z, htz]
      simp
    exact ⟨0, facet_eq_fanFace_of_shape hFS vertex_mem_iff 0 t ht shape⟩
  by_cases h12 : h1 ∧ h2
  · obtain ⟨t, shape⟩ := functional_shape 1 l h12.1 h12.2
    have ht : t ≠ 0 := by
      intro htz
      apply hlne
      ext z
      rw [shape z, htz]
      simp
    exact ⟨1, facet_eq_fanFace_of_shape hFS vertex_mem_iff 1 t ht shape⟩
  by_cases h23 : h2 ∧ h3
  · obtain ⟨t, shape⟩ := functional_shape 2 l h23.1 h23.2
    have ht : t ≠ 0 := by
      intro htz
      apply hlne
      ext z
      rw [shape z, htz]
      simp
    exact ⟨2, facet_eq_fanFace_of_shape hFS vertex_mem_iff 2 t ht shape⟩
  by_cases h34 : h3 ∧ h4
  · obtain ⟨t, shape⟩ := functional_shape 3 l h34.1 h34.2
    have ht : t ≠ 0 := by
      intro htz
      apply hlne
      ext z
      rw [shape z, htz]
      simp
    exact ⟨3, facet_eq_fanFace_of_shape hFS vertex_mem_iff 3 t ht shape⟩
  by_cases h40 : h4 ∧ h0
  · obtain ⟨t, shape⟩ := functional_shape 4 l h40.1 h40.2
    have ht : t ≠ 0 := by
      intro htz
      apply hlne
      ext z
      rw [shape z, htz]
      simp
    exact ⟨4, facet_eq_fanFace_of_shape hFS vertex_mem_iff 4 t ht shape⟩
  exfalso
  rcases nonadjacent_neighbor_relations l hmaxV with
    ⟨r02, r03, r13, r14, r24⟩
  by_cases hb : h0
  · apply rank_small b3I
    intro y hy hyeq
    rcases local_maximizer_dichotomyI l hmaxV y hy hyeq with
      h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h.1
    · exact (h01 ⟨hb, h.2⟩).elim
    · exact (h01 ⟨hb, r02 hb h.2⟩).elim
    · exact (h40 ⟨r03 hb h.2, hb⟩).elim
    · exact (h40 ⟨h.2, hb⟩).elim
    · exact (h01 h).elim
    · exact (h12 h).elim
    · exact (h23 h).elim
    · exact (h34 h).elim
    · exact (h40 h).elim
  by_cases hc : h1
  · apply rank_small c3I
    intro y hy hyeq
    rcases local_maximizer_dichotomyI l hmaxV y hy hyeq with
      h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hb h.2).elim
    · exact Or.inr h.1
    · exact (h12 ⟨hc, h.2⟩).elim
    · exact (hb (r13 hc h.2)).elim
    · exact (hb (r14 hc h.2)).elim
    · exact (h01 h).elim
    · exact (h12 h).elim
    · exact (h23 h).elim
    · exact (h34 h).elim
    · exact (h40 h).elim
  by_cases ha : h2
  · apply rank_small a1I
    intro y hy hyeq
    rcases local_maximizer_dichotomyI l hmaxV y hy hyeq with
      h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hb h.2).elim
    · exact (hc h.2).elim
    · exact Or.inr h.1
    · exact (h23 ⟨ha, h.2⟩).elim
    · exact (h23 ⟨ha, r24 ha h.2⟩).elim
    · exact (h01 h).elim
    · exact (h12 h).elim
    · exact (h23 h).elim
    · exact (h34 h).elim
    · exact (h40 h).elim
  by_cases hc' : h3
  · apply rank_small c1I
    intro y hy hyeq
    rcases local_maximizer_dichotomyI l hmaxV y hy hyeq with
      h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hb h.2).elim
    · exact (hc h.2).elim
    · exact (ha h.2).elim
    · exact Or.inr h.1
    · exact (h34 ⟨hc', h.2⟩).elim
    · exact (h01 h).elim
    · exact (h12 h).elim
    · exact (h23 h).elim
    · exact (h34 h).elim
    · exact (h40 h).elim
  by_cases hb' : h4
  · apply rank_small b2I
    intro y hy hyeq
    rcases local_maximizer_dichotomyI l hmaxV y hy hyeq with
      h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hb h.2).elim
    · exact (hc h.2).elim
    · exact (ha h.2).elim
    · exact (hc' h.2).elim
    · exact Or.inr h.1
    · exact (h01 h).elim
    · exact (h12 h).elim
    · exact (h23 h).elim
    · exact (h34 h).elim
    · exact (h40 h).elim
  · apply rank_small a3I
    intro y hy hyeq
    rcases local_maximizer_dichotomyI l hmaxV y hy hyeq with
      h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hb h.2).elim
    · exact (hc h.2).elim
    · exact (ha h.2).elim
    · exact (hc' h.2).elim
    · exact (hb' h.2).elim
    · exact (h01 h).elim
    · exact (h12 h).elim
    · exact (h23 h).elim
    · exact (h34 h).elim
    · exact (h40 h).elim

/-! ## Il vertice base è 5-ciclico -/

def _root_.Tengoku.LeanEvalPlatonicClassification.icosaCyclicData : icosaedro.CyclicVertexData a3I 5 where
  faccetta := fanFaceI
  isFacet := fanFace_isFacet
  mem_v := a3_mem_fanFace
  distinte := fanFace_injectiveI
  complete := by
    intro F hF ha
    exact incident_facet_classificationI hF ha
  σ := ρI
  fissa_v := rho_a3
  preserva := rho_preserves_polytopeI
  ruota := rho_image_fanFace
  spigolo := fanFace_spigoloI
  spigolo_due := fanFace_spigolo_dueI

/-! ## Simmetrie globali e transitività sui dodici vertici -/

def _root_.Tengoku.LeanEvalPlatonicClassification.segnoXI : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.segnoYI : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.segnoZI : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.τxI : E3 ≃ᵃⁱ[ℝ] E3 := segnoXI.toAffineIsometryEquiv
def _root_.Tengoku.LeanEvalPlatonicClassification.τyI : E3 ≃ᵃⁱ[ℝ] E3 := segnoYI.toAffineIsometryEquiv
def _root_.Tengoku.LeanEvalPlatonicClassification.τzI : E3 ≃ᵃⁱ[ℝ] E3 := segnoZI.toAffineIsometryEquiv

@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_zeroI (z : E3) : τxI z 0 = -z 0 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_oneI (z : E3) : τxI z 1 = z 1 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_twoI (z : E3) : τxI z 2 = z 2 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_zeroI (z : E3) : τyI z 0 = z 0 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_oneI (z : E3) : τyI z 1 = -z 1 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_twoI (z : E3) : τyI z 2 = z 2 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_zeroI (z : E3) : τzI z 0 = z 0 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_oneI (z : E3) : τzI z 1 = z 1 := rfl
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_twoI (z : E3) : τzI z 2 = -z 2 := rfl

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_formulaI (z : E3) :
    τxI z = WithLp.toLp 2 ![-z 0, z 1, z 2] := by
  apply E3_extI <;> rfl

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_formulaI (z : E3) :
    τyI z = WithLp.toLp 2 ![z 0, -z 1, z 2] := by
  apply E3_extI <;> rfl

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_formulaI (z : E3) :
    τzI z = WithLp.toLp 2 ![z 0, z 1, -z 2] := by
  apply E3_extI <;> rfl

theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_vertex_actions :
    κ a0I = b0I ∧ κ a1I = b2I ∧ κ a2I = b1I ∧ κ a3I = b3I ∧
    κ b0I = c0I ∧ κ b1I = c1I ∧ κ b2I = c2I ∧ κ b3I = c3I ∧
    κ c0I = a0I ∧ κ c1I = a2I ∧ κ c2I = a1I ∧ κ c3I = a3I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply E3_extI
  all_goals simp [a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I, c0I, c1I, c2I, c3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_vertices (v : E3) (hv : v ∈ verticiIcosa) :
    κ v ∈ verticiIcosa := by
  rcases kappa_vertex_actions with
    ⟨ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
    hc0, hc1, hc2, hc3]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_verticesI (v : E3) (hv : v ∈ verticiIcosa) :
    τxI v ∈ verticiIcosa := by
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauX_formulaI, a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I,
    c0I, c1I, c2I, c3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_verticesI (v : E3) (hv : v ∈ verticiIcosa) :
    τyI v ∈ verticiIcosa := by
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauY_formulaI, a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I,
    c0I, c1I, c2I, c3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_verticesI (v : E3) (hv : v ∈ verticiIcosa) :
    τzI v ∈ verticiIcosa := by
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauZ_formulaI, a0I, a1I, a2I, a3I, b0I, b1I, b2I, b3I,
    c0I, c1I, c2I, c3I]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_image_vertices :
    (⇑κ) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3) :=
  image_verticiIcosa_eq_of_maps κ kappa_vertices

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_image_verticesI :
    (⇑τxI) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3) :=
  image_verticiIcosa_eq_of_maps τxI tauX_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_image_verticesI :
    (⇑τyI) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3) :=
  image_verticiIcosa_eq_of_maps τyI tauY_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_image_verticesI :
    (⇑τzI) '' (verticiIcosa : Set E3) = (verticiIcosa : Set E3) :=
  image_verticiIcosa_eq_of_maps τzI tauZ_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.kappa_preserves_polytope :
    (⇑κ) '' icosaedro.toSet = icosaedro.toSet :=
  preserves_icosaedro_of_image_vertices κ kappa_image_vertices

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauX_preserves_polytopeI :
    (⇑τxI) '' icosaedro.toSet = icosaedro.toSet :=
  preserves_icosaedro_of_image_vertices τxI tauX_image_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauY_preserves_polytopeI :
    (⇑τyI) '' icosaedro.toSet = icosaedro.toSet :=
  preserves_icosaedro_of_image_vertices τyI tauY_image_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.tauZ_preserves_polytopeI :
    (⇑τzI) '' icosaedro.toSet = icosaedro.toSet :=
  preserves_icosaedro_of_image_vertices τzI tauZ_image_verticesI

theorem _root_.Tengoku.LeanEvalPlatonicClassification.preserves_transI (f g : E3 ≃ᵃⁱ[ℝ] E3)
    (hf : (⇑f) '' icosaedro.toSet = icosaedro.toSet)
    (hg : (⇑g) '' icosaedro.toSet = icosaedro.toSet) :
    (⇑(f.trans g)) '' icosaedro.toSet = icosaedro.toSet := by
  rw [show (⇑(f.trans g)) '' icosaedro.toSet =
      (⇑g) '' ((⇑f) '' icosaedro.toSet) by
        rw [← Set.image_comp]
        rfl,
    hf, hg]

theorem _root_.Tengoku.LeanEvalPlatonicClassification.icosaedro_vertex_transitive (v : E3) (hv : v ∈ icosaedro.vertices) :
    ∃ g : E3 ≃ᵃⁱ[ℝ] E3,
      (⇑g) '' icosaedro.toSet = icosaedro.toSet ∧ g a3I = v := by
  have hxy := preserves_transI τxI τyI tauX_preserves_polytopeI tauY_preserves_polytopeI
  have hxz := preserves_transI τxI τzI tauX_preserves_polytopeI tauZ_preserves_polytopeI
  have hky := preserves_transI κ τyI kappa_preserves_polytope tauY_preserves_polytopeI
  have hkx := preserves_transI κ τxI kappa_preserves_polytope tauX_preserves_polytopeI
  have hkxy := preserves_transI (κ.trans τxI) τyI hkx tauY_preserves_polytopeI
  have hkk := preserves_transI κ κ kappa_preserves_polytope kappa_preserves_polytope
  have hkky := preserves_transI (κ.trans κ) τyI hkk tauY_preserves_polytopeI
  have hkkz := preserves_transI (κ.trans κ) τzI hkk tauZ_preserves_polytopeI
  have hkkyz := preserves_transI ((κ.trans κ).trans τyI) τzI hkky
    tauZ_preserves_polytopeI
  change v ∈ verticiIcosa at hv
  simp only [verticiIcosa, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨τxI.trans τzI, hxz, by
      apply E3_extI <;>
        simp [a0I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τxI, tauX_preserves_polytopeI, by
      apply E3_extI <;> simp [a1I, a3I]⟩
  · exact ⟨τzI, tauZ_preserves_polytopeI, by
      apply E3_extI <;> simp [a2I, a3I]⟩
  · exact ⟨ρI, rho_preserves_polytopeI, rho_a3⟩
  · exact ⟨(κ.trans τxI).trans τyI, hkxy, by
      apply E3_extI <;>
        simp [b0I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨κ.trans τxI, hkx, by
      apply E3_extI <;>
        simp [b1I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨κ.trans τyI, hky, by
      apply E3_extI <;>
        simp [b2I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨κ, kappa_preserves_polytope, by
      apply E3_extI <;> simp [b3I, a3I]⟩
  · exact ⟨((κ.trans κ).trans τyI).trans τzI, hkkyz, by
      apply E3_extI <;>
        simp [c0I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨(κ.trans κ).trans τyI, hkky, by
      apply E3_extI <;>
        simp [c1I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨(κ.trans κ).trans τzI, hkkz, by
      apply E3_extI <;>
        simp [c2I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨κ.trans κ, hkk, by
      apply E3_extI <;>
        simp [c3I, a3I, AffineIsometryEquiv.coe_trans, Function.comp]⟩

/-! ## Assemblaggio globale -/

/-! L'icosaedro è ciclicamente regolare di tipo `(3,5)`. -/

/-! CONSEGNA

Sono certificati il politopo sui dodici vertici cosferici, la faccetta
triangolare regolare di lato `2` ruotata dal 3-ciclo delle coordinate, il fan
aureo completo di cinque faccette attorno ad `a3`, la transitività sui dodici
vertici e l'assemblaggio globale nel teorema
`icosaedro_cyclicallyRegular : icosaedro.IsCyclicallyRegularOfType 3 5`.

SHA-256 canonico (tutto il contenuto precedente a questo blocco):
`cf580088ac75fc5f1aeb80e724ece7747a8bcffb0d84192682d8a93535a30584`
Compilazione: `lake +leanprover/lean4:v4.32.0-rc1 env lean Icosaedro.lean`
— exit 0, zero errori.
-/
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
