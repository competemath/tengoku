import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ParitySquare
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricGraphUpper
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenConfiguration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed balls in the two-token path graph

This file identifies a closed ball in the two-token graph of a path with the intersection of the
parity triangle and an axis-parallel square in the shifted `twoTokenPhi` coordinates.  The
intersection records the boundary truncation explicitly.
-/

namespace BurningPath

/-- The shifted parity-triangle coordinates of a two-token configuration.-/
noncomputable def twoConfigurationPhi {n : ℕ} (A : Configuration (Fin n) 2) : ℤ × ℤ :=
  twoTokenPhi (twoConfigurationEquivTwoPathPoint n A)

/-- The axis-parallel integer square of radius `r` centered at `c`.-/
def centeredCoordinateSquare (c : ℤ × ℤ) (r : ℕ) : Set (ℤ × ℤ) :=
  {p | max (p.1 - c.1).natAbs (p.2 - c.2).natAbs ≤ r}

/--
@isnad1 id=iff.0h3v.s6.e9dd4c065cf3 from=translated src=- shape=c44c175c vocab=d58f142e
-/
@[simp]
theorem mem_centeredCoordinateSquare {c p : ℤ × ℤ} {r : ℕ} :
    p ∈ centeredCoordinateSquare c r ↔
      max (p.1 - c.1).natAbs (p.2 - c.2).natAbs ≤ r :=
  Iff.rfl

/-- The parity-triangle region cut out by the coordinate square around `c`.-/
def twoTokenBallRegion (N : ℕ) (σ : ℤ) (c : ℤ × ℤ) (r : ℕ) : Set (ℤ × ℤ) :=
  parityTriangle N σ ∩ centeredCoordinateSquare c r

/--
@isnad1 id=iff.0h5v.s6.81cec37cbef0 from=translated src=- shape=4ae34a57 vocab=9cb9f320
-/
@[simp]
theorem mem_twoTokenBallRegion {N r : ℕ} {σ : ℤ} {c p : ℤ × ℤ} :
    p ∈ twoTokenBallRegion N σ c r ↔
      p ∈ parityTriangle N σ ∧ p ∈ centeredCoordinateSquare c r :=
  Iff.rfl

/-- Graph-ball membership is exactly the centered-square inequality in `twoTokenPhi` coordinates.
@isnad1 id=iff.0h4v.s6.9a3bb3ae3116 from=translated src=- shape=b4cb3145 vocab=646e4454
-/
theorem mem_twoToken_closedBall_iff_phi_mem_centeredCoordinateSquare {n r : ℕ}
    (A C : Configuration (Fin n) 2) :
    A ∈ (pathTokenGraph n 2).closedBall C r ↔
      twoConfigurationPhi A ∈ centeredCoordinateSquare (twoConfigurationPhi C) r := by
  rw [SimpleGraph.mem_closedBall, pathTokenGraph_edist_eq_pathConfigurationDist,
    ENat.natCast_le_natCast, ← twoTokenPhi_configuration_isometry]
  rfl

/--
Including the path boundary, graph-ball membership is exactly membership in the parity-triangle
intersection with the centered coordinate square.
@isnad1 id=iff.2h5v.s6.17f62a03d644 from=translated src=- shape=ee7ca713 vocab=7101fa5c
-/
theorem mem_twoToken_closedBall_iff_phi_mem_ballRegion {n r : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (A C : Configuration (Fin n) 2) :
    A ∈ (pathTokenGraph n 2).closedBall C r ↔
      twoConfigurationPhi A ∈
        twoTokenBallRegion (n - 2) σ (twoConfigurationPhi C) r := by
  constructor
  · intro hA
    exact
      ⟨twoTokenPhi_mem_parityTriangle hn σ hσ
          (twoConfigurationEquivTwoPathPoint n A),
        (mem_twoToken_closedBall_iff_phi_mem_centeredCoordinateSquare A C).mp hA⟩
  · intro hA
    exact
      (mem_twoToken_closedBall_iff_phi_mem_centeredCoordinateSquare A C).mpr hA.2

/-- The coordinate bijection from two-token configurations to their parity triangle.-/
noncomputable def twoConfigurationPhiEquiv {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) :
    Configuration (Fin n) 2 ≃ {p // p ∈ parityTriangle (n - 2) σ} :=
  (twoConfigurationEquivTwoPathPoint n).trans (twoTokenPhiEquiv hn σ hσ)

/--
@isnad1 id=eq.2h3v.s8.0ef715523be9 from=translated src=- shape=4a74b6e9 vocab=13e4f50c
-/
@[simp]
theorem twoConfigurationPhiEquiv_apply_val {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (A : Configuration (Fin n) 2) :
    (twoConfigurationPhiEquiv hn σ hσ A).1 = twoConfigurationPhi A :=
  rfl

/--
A closed ball in the two-token path graph is equivalent to the intersection of the parity triangle
with its centered coordinate square.-/
noncomputable def twoTokenClosedBallEquivBallRegion {n r : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (C : Configuration (Fin n) 2) :
    (pathTokenGraph n 2).closedBall C r ≃
      twoTokenBallRegion (n - 2) σ (twoConfigurationPhi C) r :=
  ((twoConfigurationPhiEquiv hn σ hσ).subtypeEquiv fun A ↦ by
      simpa using mem_twoToken_closedBall_iff_phi_mem_centeredCoordinateSquare A C).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun p : ℤ × ℤ ↦ p ∈ parityTriangle (n - 2) σ)
      (fun p : ℤ × ℤ ↦ p ∈ centeredCoordinateSquare (twoConfigurationPhi C) r))

/-- Exact boundary-aware cardinality identity for a two-token graph ball.
@isnad1 id=eq.2h4v.s6.6f1510e0f9c0 from=translated src=- shape=ded71b35 vocab=d1a5c5fb
-/
theorem twoToken_closedBall_ncard_eq_ballRegion_ncard {n r : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (C : Configuration (Fin n) 2) :
    ((pathTokenGraph n 2).closedBall C r).ncard =
      (twoTokenBallRegion (n - 2) σ (twoConfigurationPhi C) r).ncard :=
  Set.ncard_congr' (twoTokenClosedBallEquivBallRegion hn σ hσ C)

/-- Offset from a chosen center in the shifted coordinate plane.-/
def coordinateOffset (c p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 - c.1, p.2 - c.2)

/-- Translation by a chosen center in the shifted coordinate plane.-/
def coordinateTranslate (c d : ℤ × ℤ) : ℤ × ℤ :=
  (c.1 + d.1, c.2 + d.2)

/--
@isnad1 id=eq.0h2v.s4.a11ffd65c315 from=translated src=- shape=da7bfcb3 vocab=8f837b28
-/
@[simp]
theorem coordinateOffset_coordinateTranslate (c d : ℤ × ℤ) :
    coordinateOffset c (coordinateTranslate c d) = d := by
  ext <;> simp [coordinateOffset, coordinateTranslate]

/--
@isnad1 id=eq.0h2v.s4.17220e955fcb from=translated src=- shape=da7bfcb3 vocab=8f837b28
-/
@[simp]
theorem coordinateTranslate_coordinateOffset (c p : ℤ × ℤ) :
    coordinateTranslate c (coordinateOffset c p) = p := by
  ext <;> simp [coordinateOffset, coordinateTranslate]

/--
@isnad1 id=injectiv.0h1v.s3.491fb6d93b3a from=translated src=- shape=07b783c8 vocab=7ff1351a
-/
theorem coordinateOffset_injective (c : ℤ × ℤ) :
    Function.Injective (coordinateOffset c) := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
  simp only [coordinateOffset, Prod.mk.injEq] at hpq ⊢
  omega

/--
Offsets of points in the same parity triangle lie in the parity-offset square whenever the points
lie in the corresponding centered coordinate square.
@isnad1 id=mem.3h5v.s6.d478e0b81dd3 from=translated src=- shape=3a0d50b6 vocab=65ec491d
-/
theorem coordinateOffset_mem_parityOffsetSquare {N r : ℕ} {σ : ℤ} {c p : ℤ × ℤ}
    (hc : c ∈ parityTriangle N σ) (hp : p ∈ parityTriangle N σ)
    (hsquare : p ∈ centeredCoordinateSquare c r) :
    coordinateOffset c p ∈ parityOffsetSquare r := by
  constructor
  · exact hsquare
  · have hpar : p.1 - p.2 ≡ c.1 - c.2 [ZMOD 2] :=
      hp.2.2.2.trans hc.2.2.2.symm
    change p.1 - c.1 ≡ p.2 - c.2 [ZMOD 2]
    rw [Int.modEq_iff_dvd] at hpar ⊢
    obtain ⟨a, ha⟩ := hpar
    refine ⟨a, ?_⟩
    omega

/-- The parity-offset square is finite.
@isnad1 id=finite.0h1v.s3.453a7ba3380d from=translated src=- shape=74894836 vocab=b2ba89a7
-/
theorem parityOffsetSquare_finite (r : ℕ) : (parityOffsetSquare r).Finite := by
  letI : Fintype (latticeBall 2 r) := (latticeBall_finite 2 r).fintype
  letI : Fintype (parityOffsetSquare r) :=
    Fintype.ofEquiv (latticeBall 2 r) (latticeBallTwoEquivParityOffsetSquare r)
  exact Set.toFinite _

/-- Any boundary-truncated parity square has cardinality at most the full parity square.
@isnad1 id=le.1h4v.s5.38fb7b473899 from=translated src=- shape=601c9a6a vocab=c44dc82a
-/
theorem twoTokenBallRegion_ncard_le {N r : ℕ} {σ : ℤ} {c : ℤ × ℤ}
    (hc : c ∈ parityTriangle N σ) :
    (twoTokenBallRegion N σ c r).ncard ≤ (parityOffsetSquare r).ncard := by
  refine Set.ncard_le_ncard_of_injOn (coordinateOffset c) ?_ ?_
    (parityOffsetSquare_finite r)
  · intro p hp
    exact coordinateOffset_mem_parityOffsetSquare hc hp.1 hp.2
  · exact (coordinateOffset_injective c).injOn

/-- Boundary-safe quadratic upper bound for the exact parity-triangle intersection.
@isnad1 id=le.1h4v.s6.64745f0fc09e from=translated src=- shape=6267e040 vocab=26b0bdcc
-/
theorem twoTokenBallRegion_ncard_le_quadratic {N r : ℕ} {σ : ℤ} {c : ℤ × ℤ}
    (hc : c ∈ parityTriangle N σ) :
    (twoTokenBallRegion N σ c r).ncard ≤ 2 * r ^ 2 + 2 * r + 1 := by
  rw [← parityOffsetSquare_ncard r]
  exact twoTokenBallRegion_ncard_le hc

/-- The graph-ball quadratic bound, obtained from the exact boundary-truncated region.
@isnad1 id=le.2h4v.s7.96aaf404a207 from=translated src=- shape=2b8bb2b2 vocab=feeb1041
-/
theorem twoToken_closedBall_ncard_le_quadratic_via_phi {n r : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (C : Configuration (Fin n) 2) :
    ((pathTokenGraph n 2).closedBall C r).ncard ≤ 2 * r ^ 2 + 2 * r + 1 := by
  rw [twoToken_closedBall_ncard_eq_ballRegion_ncard hn σ hσ C]
  apply twoTokenBallRegion_ncard_le_quadratic
  exact
    twoTokenPhi_mem_parityTriangle hn σ hσ
      (twoConfigurationEquivTwoPathPoint n C)

/--
The full parity-offset square fits around `c` when translating every one of its offsets by `c`
stays inside the parity triangle.-/
def ParityOffsetSquareFits (N : ℕ) (σ : ℤ) (c : ℤ × ℤ) (r : ℕ) : Prop :=
  ∀ d ∈ parityOffsetSquare r, coordinateTranslate c d ∈ parityTriangle N σ

/-- If the full parity square fits in the triangle, the intersection has the full quadratic size.
@isnad1 id=eq.2h4v.s6.2b16733c8010 from=translated src=- shape=c11a1877 vocab=d9428c0e
-/
theorem twoTokenBallRegion_ncard_eq_quadratic_of_fits {N r : ℕ} {σ : ℤ} {c : ℤ × ℤ}
    (hc : c ∈ parityTriangle N σ) (hfits : ParityOffsetSquareFits N σ c r) :
    (twoTokenBallRegion N σ c r).ncard = 2 * r ^ 2 + 2 * r + 1 := by
  have hbij :
      Set.BijOn (coordinateOffset c) (twoTokenBallRegion N σ c r)
        (parityOffsetSquare r) := by
    refine ⟨?_, (coordinateOffset_injective c).injOn, ?_⟩
    · intro p hp
      exact coordinateOffset_mem_parityOffsetSquare hc hp.1 hp.2
    · intro d hd
      refine ⟨coordinateTranslate c d, ?_, coordinateOffset_coordinateTranslate c d⟩
      constructor
      · exact hfits d hd
      · simpa [centeredCoordinateSquare, coordinateTranslate] using hd.1
  rw [hbij.ncard_eq, parityOffsetSquare_ncard]

/--
Consequently, a two-token graph ball has the full quadratic cardinality whenever its translated
parity-offset square is not truncated by the parity triangle.
@isnad1 id=eq.3h4v.s7.3cbeff02bcbb from=translated src=- shape=8e853aed vocab=23a8ab27
-/
theorem twoToken_closedBall_ncard_eq_quadratic_of_fits {n r : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (C : Configuration (Fin n) 2)
    (hfits :
      ParityOffsetSquareFits (n - 2) σ (twoConfigurationPhi C) r) :
    ((pathTokenGraph n 2).closedBall C r).ncard = 2 * r ^ 2 + 2 * r + 1 := by
  rw [twoToken_closedBall_ncard_eq_ballRegion_ncard hn σ hσ C]
  apply twoTokenBallRegion_ncard_eq_quadratic_of_fits
  · exact
      twoTokenPhi_mem_parityTriangle hn σ hσ
        (twoConfigurationEquivTwoPathPoint n C)
  · exact hfits

end BurningPath
