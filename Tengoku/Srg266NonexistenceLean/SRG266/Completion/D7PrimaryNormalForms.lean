/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.D7Discriminant
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.PrimaryNormalForms
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimaryTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

open SRG266.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
@isnad1 id=eq.4h7v.s14.aa279b032498 from=translated src=- shape=635eeeb5 vocab=bf1e562e
-/
theorem lorentzD7_torsionPart_eq_sup_map (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P) (B : SecondSubconstituent G x) (p : ℕ) :
    torsionPart (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) p =
      lorentzD7Glue G hG x c hc P B ⊔
        (torsionPart (lorentzGramForm G x c) P p).map
          ((lorentzD7OddLift G x c B).restrictScalars ℤ) :=
  torsionPart_eq_sup_map_of_dual_transport ((lorentzD7OddLift G x c B).restrictScalars ℤ)
    (lorentzD7Glue_isIntegral G hG x c hc hle hint B)
    (lorentzD7_dual_eq_sup_map G hG x c hc hle hint B)
    (fun _ hv => lorentzD7OddLift_mem_iff G hG x c hc hle hint B hv) p

/--
@isnad1 id=mem.6h8v.s14.ad1d3ce7c639 from=translated src=- shape=43779010 vocab=be11a067
-/
theorem lorentzD7OddLift_pair_integral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) {u v : ratGramSpace G x}
    (hu : u ∈ (lorentzGramForm G x c).dualSubmodule P)
    (hv : v ∈ (lorentzGramForm G x c).dualSubmodule P)
    (huv : lorentzGramForm G x c u v ∈ (1 : Submodule ℤ ℚ)) :
    lorentzD7Form G x c (lorentzD7OddLift G x c B u) (lorentzD7OddLift G x c B v) ∈
      (1 : Submodule ℤ ℚ) := by
  change lorentzPerpForm G x c (lorentzIntegralProjection G x c B u)
    (lorentzIntegralProjection G x c B v) + standardRatForm 7 0 0 ∈ (1 : Submodule ℤ ℚ)
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using
    lorentzIntegralProjection_pair_integral G hG x c hc hle B hu hv huv

/--
@isnad1 id=hasprima.5h8v.s11.bd645b153188 from=translated src=- shape=02378a62 vocab=b83c10ea
-/
theorem lorentzD7_hasPrimaryNormalForm (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P) (B : SecondSubconstituent G x)
    {p : ℕ} {r : ℤ} (h : HasPrimaryNormalForm (lorentzGramForm G x c) P p r) :
    HasPrimaryNormalForm (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) p r := by
  have hmap : P.map ((lorentzD7OddLift G x c B).restrictScalars ℤ) ≤
      lorentzD7Glue G hG x c hc P B := by
    rintro _ ⟨v, hv, rfl⟩
    exact (lorentzD7OddLift_mem_iff G hG x c hc hle hint B (hint hv)).mpr hv
  exact h.map ((lorentzD7OddLift G x c B).restrictScalars ℤ) hmap
    (lorentzD7_torsionPart_eq_sup_map G hG x c hc hle hint B p)
    (fun _ hu => lorentzD7OddLift_norm_mod_even G hG x c hc hle B (mem_torsionPart.mp hu).1)
    (fun _ hu _ hv huv => lorentzD7OddLift_pair_integral G hG x c hc hle B
      (mem_torsionPart.mp hu).1 (mem_torsionPart.mp hv).1 huv)

/--
@isnad1 id=ex.1h4v.s16.961bfe9e4a4c from=translated src=- shape=f149f69a vocab=16337383
-/
theorem exists_lorentzD7_normal_forms_from_graph (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∃ (c : IntegralGramLattice G x)
      (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
      (P : Submodule ℤ (ratGramSpace G x)),
      lorentzMarkedLattice G x c ≤ P ∧ IsMaximalIntegral (lorentzGramForm G x c) P ∧
      IsLattice ℚ (lorentzD7Glue G hG x c hc P B) ∧
      IsEven (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) ∧
      Module.finrank ℚ (lorentzPerpSpace G x c × (Fin 7 → ℚ)) = 18 ∧
      (∀ z, z ≠ 0 → 0 < lorentzD7Form G x c z z) ∧
      (∀ D, lorentzD7FrameVector G hG x c hc D ∈ lorentzD7Glue G hG x c hc P B ∧
        lorentzD7Form G x c (lorentzD7FrameVector G hG x c hc D)
          (lorentzD7FrameVector G hG x c hc D) = 4) ∧
      (∀ y, (y, (0 : Fin 7 → ℚ)) ∈ lorentzD7Glue G hG x c hc P B ↔
        y ∈ lorentzPerpLattice G x c P) ∧
      (∀ z, ((0 : lorentzPerpSpace G x c), z) ∈ lorentzD7Glue G hG x c hc P B ↔
        z ∈ evenCoordinateLattice 7) ∧
      (lorentzD7Form G x c).dualSubmodule (lorentzD7Glue G hG x c hc P B) =
        torsionPart (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) 3 ⊔
          torsionPart (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) 5 ∧
      HasPrimaryNormalForm (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) 3 2 ∧
      HasPrimaryNormalForm (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) 5 4 := by
  obtain ⟨c, P, hc, hle, hlat, hmax, heven, hsplit, hthree, hfive⟩ :=
    exists_lorentzMarked_normal_forms_from_graph G hG x
  refine ⟨c, hc, P, hle, hmax,
    cyclicGlueLattice_isLattice
      (lorentzPerpLattice_isLattice G hG x c hc hle hlat hmax.integral)
      (evenCoordinateLattice_isLattice 7),
    lorentzD7Glue_isEven G hG x c hc hle hmax.integral (lorentzPerpLattice_isEven G x c heven) B,
    finrank_lorentzD7Space G hG x c hc,
    prodForm_posDef (lorentzPerpForm_posDef G hG x c) (standardRatForm_posDef 7),
    fun D => ⟨lorentzD7FrameVector_mem G hG x c hc hle B D,
      lorentzD7FrameVector_norm G hG x c hc D⟩,
    lorentzD7Glue_mem_left_iff G hG x c hc hle B,
    lorentzD7Glue_mem_right_iff G hG x c hc hle (lorentzPerpLattice_isEven G x c heven) B, ?_,
    lorentzD7_hasPrimaryNormalForm G hG x c hc hle hmax.integral B hthree,
    lorentzD7_hasPrimaryNormalForm G hG x c hc hle hmax.integral B hfive⟩
  rw [lorentzD7_torsionPart_eq_sup_map G hG x c hc hle hmax.integral B 3,
    lorentzD7_torsionPart_eq_sup_map G hG x c hc hle hmax.integral B 5,
    lorentzD7_dual_eq_sup_map G hG x c hc hle hmax.integral B, hsplit, Submodule.map_sup]
  exact sup_sup_distrib_left _ _ _

end SRG266
