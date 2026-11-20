import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.GlobalShelfCover
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenGraphBall
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transfer parity-triangle square covers to two-token graph covers

This module converts parity-triangle square covers into two-token graph covers.
-/

namespace BurningPath

/-- The integer-square and centered coordinate-square formulations agree.
@isnad1 id=iff.0h3v.s5.ddf55a7da25a from=translated src=- shape=6a7b3c0d vocab=dbdac2e6
-/
theorem mem_integerSquare_iff_centeredCoordinateSquare
    {c p : ℤ × ℤ} {r : ℕ} :
    p ∈ integerSquare c r ↔ p ∈ centeredCoordinateSquare c r := by
  simp only [integerSquare, intLinfDist, centeredCoordinateSquare,
    Set.mem_ofPred_eq]
  rw [max_le_iff, max_le_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · have h :
          (((p.1 - c.1).natAbs : ℕ) : ℤ) ≤ (r : ℤ) := by
          simpa only [Int.natCast_natAbs] using h₁
      exact_mod_cast h
    · have h :
          (((p.2 - c.2).natAbs : ℕ) : ℤ) ≤ (r : ℤ) := by
          simpa only [Int.natCast_natAbs] using h₂
      exact_mod_cast h
  · rintro ⟨h₁, h₂⟩
    constructor
    · have h :
          (((p.1 - c.1).natAbs : ℕ) : ℤ) ≤ (r : ℤ) := by
          exact_mod_cast h₁
      simpa only [Int.natCast_natAbs] using h
    · have h :
          (((p.2 - c.2).natAbs : ℕ) : ℤ) ≤ (r : ℤ) := by
          exact_mod_cast h₂
      simpa only [Int.natCast_natAbs] using h

/--
A legal parity-triangle ranked square cover is exactly a ranked cover of the
two-token path graph.
@isnad1 id=ex.3h4v.s6.c710952f1cdb from=translated src=- shape=f1e48670 vocab=5f68a3c1
-/
theorem IsParityCapRankedCover.toPathTokenRankedCover
    {n t : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2])
    {squareCenters : Fin t → ℤ × ℤ}
    (hcover : IsParityCapRankedCover 0 (n - 2) t σ squareCenters) :
    ∃ centers : Fin t → Configuration (Fin n) 2,
      (pathTokenGraph n 2).IsRankedCover centers := by
  have htriangle (r : Fin t) :
      squareCenters r ∈ parityTriangle (n - 2) σ := by
    rw [← parityCap_zero]
    exact hcover.1 r
  let centers : Fin t → Configuration (Fin n) 2 :=
    fun r ↦
      (twoConfigurationPhiEquiv hn σ hσ).symm
        ⟨squareCenters r, htriangle r⟩
  refine ⟨centers, ?_⟩
  intro A
  have hAtriangle :
      twoConfigurationPhi A ∈ parityTriangle (n - 2) σ :=
    twoTokenPhi_mem_parityTriangle hn σ hσ
      (twoConfigurationEquivTwoPathPoint n A)
  have hAcap :
      twoConfigurationPhi A ∈ parityCap 0 (n - 2) σ := by
    rwa [parityCap_zero]
  obtain ⟨r, hr⟩ := hcover.2 (twoConfigurationPhi A) hAcap
  refine ⟨r, ?_⟩
  apply
    (mem_twoToken_closedBall_iff_phi_mem_centeredCoordinateSquare
      A (centers r)).mpr
  have hcenterPhi :
      twoConfigurationPhi (centers r) = squareCenters r := by
    exact congrArg Subtype.val
      ((twoConfigurationPhiEquiv hn σ hσ).apply_symm_apply
        ⟨squareCenters r, htriangle r⟩)
  rw [hcenterPhi]
  exact mem_integerSquare_iff_centeredCoordinateSquare.mp hr

/-- A parity-triangle cover of length `t` gives a finite two-token burning bound.
@isnad1 id=le.3h3v.s6.63b8008e8875 from=translated src=- shape=7bd80e7b vocab=4bbedea0
-/
theorem pathTokenBurningNumber_le_of_parityTriangleCover
    {n t : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2])
    (hcover :
      ∃ squareCenters : Fin t → ℤ × ℤ,
        IsParityCapRankedCover 0 (n - 2) t σ squareCenters) :
    pathTokenBurningNumber n 2 hn ≤ t := by
  obtain ⟨squareCenters, hsquare⟩ := hcover
  obtain ⟨centers, hcenters⟩ :=
    hsquare.toPathTokenRankedCover hn σ hσ
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hn)
  change (pathTokenGraph n 2).burningNumber ≤ t
  apply (pathTokenGraph n 2).burningNumber_min
  have ht : 0 < t := by
    obtain ⟨r, _⟩ :=
      hcenters
        (Classical.choice
          (inferInstance : Nonempty (Configuration (Fin n) 2)))
    exact lt_of_le_of_lt (Nat.zero_le r.val) r.isLt
  exact ⟨ht, centers, hcenters⟩

/-- Finite two-token bound under the two explicit large-`N` shelf conditions.
@isnad1 id=le.4h2v.s7.ecaf12ffe751 from=translated src=- shape=d5fb155c vocab=fbfff773
-/
theorem pathTokenBurningNumber_le_shelfInitialWidth_of_large_conditions
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n)
    (hloss :
      30 * (shelfInitialWidth ε (n - 2) : ℝ) * ((n - 2 : ℕ) : ℝ) ≤
        shelfDelta ε / 2 * ((n - 2 : ℕ) : ℝ) ^ 2)
    (hwidth :
      (144 : ℝ) ≤ shelfBeta ε * shelfWidthScale (n - 2)) :
    pathTokenBurningNumber n 2 hn ≤ shelfInitialWidth ε (n - 2) := by
  let σ : ℤ := n
  have hσn : (n : ℤ) ≡ σ [ZMOD 2] := Int.ModEq.rfl
  have hσN : ((n - 2 : ℕ) : ℤ) ≡ σ [ZMOD 2] := by
    apply Int.ModEq.trans _ hσn
    rw [Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    omega
  have hcover :=
    exists_parityTriangleCover_of_large_conditions hε hσN hloss hwidth
  exact
    pathTokenBurningNumber_le_of_parityTriangleCover
      hn σ hσn hcover

end BurningPath
