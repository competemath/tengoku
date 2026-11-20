import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ContinuousCover
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.DiscreteChamber
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricGraphUpper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact discrete-continuum comparisons

This file transfers ranked covers between the discrete token chamber and the
normalized real ordered simplex. The two final theorems give the forward and
reverse comparisons.
-/

open scoped BigOperators

namespace BurningPath

/-- A ranked cover of the discrete ordered chamber by its restricted `ℓ₁` balls.-/
def IsGammaRankedCover {N k t : ℕ} (centers : Fin t → Gamma N k) : Prop :=
  ∀ z, ∃ r : Fin t, gammaL1Dist z (centers r) ≤ r.1

private instance gammaFinite (N k : ℕ) : Finite (Gamma N k) := by
  let f : Gamma N k → (Fin k → Fin (N + 1)) := fun z i ↦
    ⟨z.1 i, lt_of_le_of_lt (z.2.2 i) (Nat.lt_succ_self N)⟩
  exact Finite.of_injective f (by
    intro z w h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i))

private instance gammaNonempty (N k : ℕ) : Nonempty (Gamma N k) :=
  ⟨⟨0, monotone_const, by simp⟩⟩

/-- Shift rank `r` to rank `r + k`.-/
private def shiftRankEmbedding (t k : ℕ) : Fin t ↪ Fin (t + k) where
  toFun r := ⟨r.1 + k, by omega⟩
  inj' := by
    intro r s hrs
    apply Fin.ext
    exact Nat.add_right_cancel (congrArg Fin.val hrs)

@[simp]
private theorem shiftRankEmbedding_val (t k : ℕ) (r : Fin t) :
    (shiftRankEmbedding t k r).1 = r.1 + k :=
  rfl

/-- Coordinatewise natural floor after scaling a nonnegative real point.-/
private noncomputable def floorScaledPoint {k : ℕ} (a : ℝ)
    (x : Fin k → ℝ) : Fin k → ℕ :=
  fun i ↦ ⌊a * x i⌋₊

/-- Scale a discrete chamber point into a real ordered simplex.-/
private noncomputable def gammaScale {N k : ℕ} (q : ℕ)
    (z : Gamma N k) : Fin k → ℝ :=
  fun i ↦ (z.1 i : ℝ) / q

private theorem gammaScale_mem_orderedSimplex {N k q : ℕ} (hq : 1 ≤ q)
    (z : Gamma N k) :
    gammaScale q z ∈ orderedSimplex k ((N : ℝ) / q) := by
  have hqR : 0 ≤ (q : ℝ) := by positivity
  constructor
  · intro i
    constructor
    · exact div_nonneg (by positivity) hqR
    · exact div_le_div_of_nonneg_right (by exact_mod_cast z.2.2 i) hqR
  · intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast z.2.1 hij) hqR

/-- Flooring `q x` preserves the chamber inequalities and the endpoint `N`.-/
private noncomputable def simplexFloorToGamma {N k q : ℕ} (hq : 1 ≤ q)
    (x : Fin k → ℝ) (hx : x ∈ orderedSimplex k ((N : ℝ) / q)) :
    Gamma N k := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  refine ⟨floorScaledPoint q x, ?_, ?_⟩
  · intro i j hij
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (hx.2 hij) hqR.le
  · intro i
    have hnonneg : 0 ≤ (q : ℝ) * x i := mul_nonneg hqR.le (hx.1 i).1
    have hfloor : (floorScaledPoint q x i : ℝ) ≤ (q : ℝ) * x i :=
      Nat.floor_le hnonneg
    have hxbound : x i * q ≤ (N : ℝ) := (le_div_iff₀ hqR).mp (hx.1 i).2
    apply (Nat.cast_le (α := ℝ)).mp
    exact hfloor.trans (by simpa [mul_comm] using hxbound)

private theorem realL1Dist_scale {k : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (x y : Fin k → ℝ) :
    realL1Dist (fun i ↦ a * x i) (fun i ↦ a * y i) =
      a * realL1Dist x y := by
  rw [realL1Dist, realL1Dist, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub, abs_mul, abs_of_nonneg ha]

private theorem natDist_cast_eq_abs_sub (a b : ℕ) :
    ((Nat.dist a b : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · have habR : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, abs_of_nonpos (sub_nonpos.mpr habR)]
    norm_num [Nat.cast_sub h]
  · have hbaR : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, abs_of_nonneg (sub_nonneg.mpr hbaR)]
    norm_num [Nat.cast_sub h]

private theorem realL1Dist_natCast_eq_gammaL1Dist {N k : ℕ}
    (z w : Gamma N k) :
    realL1Dist (fun i ↦ (z.1 i : ℝ)) (fun i ↦ (w.1 i : ℝ)) =
      gammaL1Dist z w := by
  rw [realL1Dist, gammaL1Dist, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (natDist_cast_eq_abs_sub (z.1 i) (w.1 i)).symm

/-- Coordinatewise flooring changes a scaled nonnegative point by `ℓ₁` distance at most `k`.-/
private theorem realL1Dist_floorScaledPoint_le {k : ℕ} {a : ℝ}
    {x : Fin k → ℝ} (ha : 0 ≤ a) (hx : ∀ i, 0 ≤ x i) :
    realL1Dist (fun i ↦ a * x i)
      (fun i ↦ (floorScaledPoint a x i : ℝ)) ≤ k := by
  rw [realL1Dist]
  calc
    (∑ i, |a * x i - (floorScaledPoint a x i : ℝ)|) ≤
        ∑ _i : Fin k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hnonneg : 0 ≤ a * x i := mul_nonneg ha (hx i)
      have hfloor : (floorScaledPoint a x i : ℝ) ≤ a * x i :=
        Nat.floor_le hnonneg
      rw [abs_of_nonneg (sub_nonneg.mpr hfloor)]
      have hlt := Nat.lt_floor_add_one (a * x i)
      change a * x i < (floorScaledPoint a x i : ℝ) + 1 at hlt
      linarith
    _ = k := by simp

private theorem simplexFloor_error_le {N k q : ℕ} (hq : 1 ≤ q)
    (x : Fin k → ℝ) (hx : x ∈ orderedSimplex k ((N : ℝ) / q)) :
    realL1Dist (fun i ↦ (q : ℝ) * x i)
      (fun i ↦ ((simplexFloorToGamma hq x hx).1 i : ℝ)) ≤ k := by
  exact realL1Dist_floorScaledPoint_le (by positivity) fun i ↦ (hx.1 i).1

/-- Floor a scaled point of `Δ_L` into the finite grid chamber below `D L`.-/
private noncomputable def simplexFloorToGridGamma {k D : ℕ} {L : ℝ}
    (x : Fin k → ℝ) (hx : x ∈ orderedSimplex k L) :
    Gamma ⌊(D : ℝ) * L⌋₊ k := by
  refine ⟨floorScaledPoint D x, ?_, ?_⟩
  · intro i j hij
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (hx.2 hij) (by positivity)
  · intro i
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (hx.1 i).2 (by positivity)

@[simp]
private theorem simplexFloorToGridGamma_apply {k D : ℕ} {L : ℝ}
    (x : Fin k → ℝ) (hx : x ∈ orderedSimplex k L) (i : Fin k) :
    (simplexFloorToGridGamma (D := D) x hx).1 i = floorScaledPoint D x i :=
  rfl

private theorem gridGammaScale_mem_orderedSimplex {k D : ℕ} {L : ℝ}
    (hD : 1 ≤ D) (hL : 0 ≤ L) (z : Gamma ⌊(D : ℝ) * L⌋₊ k) :
    gammaScale D z ∈ orderedSimplex k L := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  constructor
  · intro i
    constructor
    · exact div_nonneg (by positivity) hDR.le
    · have hfloor : (⌊(D : ℝ) * L⌋₊ : ℝ) ≤ (D : ℝ) * L :=
        Nat.floor_le (mul_nonneg hDR.le hL)
      have hz : (z.1 i : ℝ) ≤ (D : ℝ) * L :=
        (by exact_mod_cast z.2.2 i : (z.1 i : ℝ) ≤ ⌊(D : ℝ) * L⌋₊).trans hfloor
      apply (div_le_iff₀ hDR).2
      simpa [mul_comm] using hz
  · intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast z.2.1 hij) hDR.le

private theorem gridFloor_error_le {k D : ℕ} {L : ℝ}
    (hD : 1 ≤ D) (x : Fin k → ℝ) (hx : x ∈ orderedSimplex k L) :
    realL1Dist x (gammaScale D (simplexFloorToGridGamma (D := D) x hx)) ≤
      (k : ℝ) / D := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  apply (le_div_iff₀ hDR).2
  calc
    realL1Dist x (gammaScale D (simplexFloorToGridGamma (D := D) x hx)) * D =
        D * realL1Dist x (gammaScale D (simplexFloorToGridGamma (D := D) x hx)) := by
      ring
    _ = realL1Dist (fun i ↦ (D : ℝ) * x i)
        (fun i ↦
          (D : ℝ) * gammaScale D (simplexFloorToGridGamma (D := D) x hx) i) :=
      (realL1Dist_scale D hDR.le _ _).symm
    _ = realL1Dist (fun i ↦ (D : ℝ) * x i)
        (fun i ↦ (floorScaledPoint D x i : ℝ)) := by
      congr 1
      funext i
      simp only [gammaScale, simplexFloorToGridGamma_apply]
      field_simp
    _ ≤ k :=
      realL1Dist_floorScaledPoint_le hDR.le fun i ↦ (hx.1 i).1

/--
Every nonnegative bounded ordered simplex has some finite normalized ranked cover. This supplies
the nonemptiness required for `simplexCoverNumber` to have its intended least-cover semantics.-/
theorem exists_simplexRankedCover {k : ℕ} {L : ℝ} (hk : 1 ≤ k) (hL : 0 ≤ L) :
    ∃ q, 1 ≤ q ∧ HasSimplexRankedCover k L q := by
  classical
  let D := 2 * k
  let gridN := ⌊(D : ℝ) * L⌋₊
  letI : Fintype (Gamma gridN k) := Fintype.ofFinite _
  let M := Fintype.card (Gamma gridN k)
  have hM : 1 ≤ M := Fintype.card_pos
  have hD : 1 ≤ D := by
    dsimp [D]
    omega
  let enumerate : Gamma gridN k ≃ Fin M := Fintype.equivFin _
  let e : Fin M ↪ Fin (M + M) := Fin.natAddEmb M
  let gridCenters : Fin M → (Fin k → ℝ) :=
    fun i ↦ gammaScale D (enumerate.symm i)
  let fullCenters : Fin (M + M) → (Fin k → ℝ) :=
    Function.extend e gridCenters (fun _ ↦ 0)
  have hfull : ∀ i, fullCenters (e i) = gridCenters i := by
    intro i
    exact e.injective.extend_apply gridCenters (fun _ ↦ 0) i
  refine ⟨M + M, by omega, fullCenters, ?_⟩
  constructor
  · intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [hfull]
      exact gridGammaScale_mem_orderedSimplex hD hL (enumerate.symm j)
    · change Function.extend e gridCenters (fun _ ↦ 0) i ∈ orderedSimplex k L
      rw [Function.extend_apply' gridCenters (fun _ ↦ 0) i]
      · exact zero_mem_orderedSimplex hL
      · simpa only [Set.mem_range] using hi
  · intro x hx
    let z : Gamma gridN k := simplexFloorToGridGamma x hx
    let i : Fin M := enumerate z
    refine ⟨e i, ?_⟩
    rw [hfull]
    have hcenter : gridCenters i = gammaScale D z := by
      simp [gridCenters, i, z]
    rw [hcenter]
    have hhalf :
        realL1Dist x (gammaScale D z) ≤ (1 : ℝ) / 2 := by
      calc
        realL1Dist x (gammaScale D z) ≤ (k : ℝ) / D :=
          gridFloor_error_le hD x hx
        _ = (1 : ℝ) / 2 := by
          have hkR : (k : ℝ) ≠ 0 := by positivity
          simp only [D, Nat.cast_mul, Nat.cast_ofNat]
          field_simp
    exact hhalf.trans (by
      have he : (e i).1 = M + i.1 := rfl
      rw [he]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      norm_num
      exact_mod_cast (show M + M ≤ (M + i.1) * 2 by omega))

/-- A path-token graph ranked cover becomes a ranked cover of the isometric chamber.-/
theorem SimpleGraph.IsRankedCover.toGammaRankedCover {n k t : ℕ}
    (hk : k ≤ n) {centers : Fin t → Configuration (Fin n) k}
    (hcover : (pathTokenGraph n k).IsRankedCover centers) :
    IsGammaRankedCover (fun r ↦ configurationEquivGamma hk (centers r)) := by
  intro z
  obtain ⟨r, hr⟩ := hcover ((configurationEquivGamma hk).symm z)
  refine ⟨r, ?_⟩
  have hdist :
      pathConfigurationDist ((configurationEquivGamma hk).symm z) (centers r) ≤ r.1 := by
    simp only [SimpleGraph.mem_closedBall,
      pathTokenGraph_edist_eq_pathConfigurationDist] at hr
    exact_mod_cast hr
  rw [gammaL1Dist_eq_pathConfigurationDist hk]
  simpa using hdist

/-- A chamber ranked cover becomes a path-token graph ranked cover through the exact isometry.-/
theorem IsGammaRankedCover.toPathTokenRankedCover {n k t : ℕ}
    (hk : k ≤ n) {centers : Fin t → Gamma (n - k) k}
    (hcover : IsGammaRankedCover centers) :
    (pathTokenGraph n k).IsRankedCover
      (fun r ↦ (configurationEquivGamma hk).symm (centers r)) := by
  intro A
  obtain ⟨r, hr⟩ := hcover (configurationEquivGamma hk A)
  refine ⟨r, ?_⟩
  simp only [SimpleGraph.mem_closedBall,
    pathTokenGraph_edist_eq_pathConfigurationDist]
  have hdist :
      pathConfigurationDist A ((configurationEquivGamma hk).symm (centers r)) ≤ r.1 := by
    rw [pathConfigurationDist_eq_gammaL1Dist hk]
    simpa using hr
  exact_mod_cast hdist

/--
Shift the ranks of a discrete chamber cover by `k`; after scaling by `t + k`, the resulting
centers cover the normalized real ordered simplex.-/
theorem IsGammaRankedCover.toSimplexRankedCover_add {N k t : ℕ}
    {centers : Fin t → Gamma N k} (hcover : IsGammaRankedCover centers)
    (hq : 1 ≤ t + k) :
    HasSimplexRankedCover k
      ((N : ℝ) / ((t + k : ℕ) : ℝ)) (t + k) := by
  classical
  let e := shiftRankEmbedding t k
  let scaledCenters : Fin t → (Fin k → ℝ) :=
    fun r ↦ gammaScale (t + k) (centers r)
  let fullCenters : Fin (t + k) → (Fin k → ℝ) :=
    Function.extend e scaledCenters (fun _ ↦ 0)
  have hfull : ∀ r, fullCenters (e r) = scaledCenters r := by
    intro r
    exact e.injective.extend_apply scaledCenters (fun _ ↦ 0) r
  refine ⟨fullCenters, ?_⟩
  constructor
  · intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨r, rfl⟩ := hi
      rw [hfull]
      simpa [scaledCenters, Nat.cast_add] using
        gammaScale_mem_orderedSimplex hq (centers r)
    · change Function.extend e scaledCenters (fun _ ↦ 0) i ∈
        orderedSimplex k ((N : ℝ) / ((t + k : ℕ) : ℝ))
      rw [Function.extend_apply' scaledCenters (fun _ ↦ 0) i]
      · exact zero_mem_orderedSimplex (div_nonneg (by positivity) (by positivity))
      · simpa only [Set.mem_range] using hi
  · intro x hx
    let z := simplexFloorToGamma hq x hx
    obtain ⟨r, hr⟩ := hcover z
    refine ⟨e r, ?_⟩
    rw [hfull]
    have hqR : 0 < ((t + k : ℕ) : ℝ) := by exact_mod_cast hq
    have hscaled :
        realL1Dist (fun i ↦ ((t + k : ℕ) : ℝ) * x i)
            (fun i ↦ (centers r).1 i) ≤ ((k + r.1 : ℕ) : ℝ) := by
      calc
        realL1Dist (fun i ↦ ((t + k : ℕ) : ℝ) * x i)
            (fun i ↦ ((centers r).1 i : ℝ)) ≤
            realL1Dist (fun i ↦ ((t + k : ℕ) : ℝ) * x i)
              (fun i ↦ ((z.1 i : ℕ) : ℝ)) +
                realL1Dist (fun i ↦ ((z.1 i : ℕ) : ℝ))
                  (fun i ↦ ((centers r).1 i : ℝ)) :=
          realL1Dist_triangle _ _ _
        _ ≤ (k : ℝ) + (r.1 : ℝ) := by
          apply add_le_add
          · exact simplexFloor_error_le hq x hx
          · rw [realL1Dist_natCast_eq_gammaL1Dist]
            exact_mod_cast hr
        _ = ((k + r.1 : ℕ) : ℝ) := by norm_num
    change realL1Dist x (gammaScale (t + k) (centers r)) ≤
      (((e r).1 : ℕ) : ℝ) / ((t + k : ℕ) : ℝ)
    rw [shiftRankEmbedding_val]
    apply (le_div_iff₀ hqR).2
    calc
      realL1Dist x (gammaScale (t + k) (centers r)) * ((t + k : ℕ) : ℝ) =
          ((t + k : ℕ) : ℝ) *
            realL1Dist x (gammaScale (t + k) (centers r)) := by ring
      _ = realL1Dist (fun i ↦ ((t + k : ℕ) : ℝ) * x i)
          (fun i ↦ ((t + k : ℕ) : ℝ) * gammaScale (t + k) (centers r) i) :=
        (realL1Dist_scale ((t + k : ℕ) : ℝ) hqR.le _ _).symm
      _ = realL1Dist (fun i ↦ ((t + k : ℕ) : ℝ) * x i)
          (fun i ↦ ((centers r).1 i : ℝ)) := by
        congr 1
        funext i
        dsimp [gammaScale]
        field_simp
      _ ≤ ((k + r.1 : ℕ) : ℝ) := hscaled
      _ = ((r.1 + k : ℕ) : ℝ) := by rw [Nat.add_comm]

/--
Floor the centers of a normalized simplex cover after scaling by `q`; shifting every old rank by
`k` gives a ranked cover of the discrete chamber of length `q + k`.-/
theorem IsL1NormalizedRankedCover.toGammaRankedCover_add {N k q : ℕ}
    {centers : Fin q → (Fin k → ℝ)}
    (hcover :
      IsL1NormalizedRankedCover (orderedSimplex k ((N : ℝ) / q)) centers)
    (hq : 1 ≤ q) :
    ∃ discreteCenters : Fin (q + k) → Gamma N k,
      IsGammaRankedCover discreteCenters := by
  classical
  let e := shiftRankEmbedding q k
  let oldCenters : Fin q → Gamma N k := fun i ↦
    simplexFloorToGamma hq (centers i) (hcover.1 i)
  let discreteCenters : Fin (q + k) → Gamma N k :=
    Function.extend e oldCenters (fun _ ↦ Classical.choice (gammaNonempty N k))
  have hfull : ∀ i, discreteCenters (e i) = oldCenters i := by
    intro i
    exact e.injective.extend_apply oldCenters
      (fun _ ↦ Classical.choice (gammaNonempty N k)) i
  refine ⟨discreteCenters, ?_⟩
  intro z
  have hz : gammaScale q z ∈ orderedSimplex k ((N : ℝ) / q) :=
    gammaScale_mem_orderedSimplex hq z
  obtain ⟨i, hi⟩ := hcover.2 (gammaScale q z) hz
  refine ⟨e i, ?_⟩
  rw [hfull]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscaledCover :
      realL1Dist (fun j ↦ (z.1 j : ℝ))
          (fun j ↦ (q : ℝ) * centers i j) ≤ (i.1 : ℝ) := by
    calc
      realL1Dist (fun j ↦ (z.1 j : ℝ))
          (fun j ↦ (q : ℝ) * centers i j) =
          realL1Dist (fun j ↦ (q : ℝ) * gammaScale q z j)
            (fun j ↦ (q : ℝ) * centers i j) := by
        congr 1
        funext j
        dsimp [gammaScale]
        field_simp
      _ = (q : ℝ) * realL1Dist (gammaScale q z) (centers i) :=
        realL1Dist_scale q hqR.le _ _
      _ ≤ (i.1 : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hi hqR.le
        calc
          (q : ℝ) * realL1Dist (gammaScale q z) (centers i) ≤
              (q : ℝ) * ((i.1 : ℝ) / q) := hmul
          _ = (i.1 : ℝ) := by field_simp
  have hfloor :
      realL1Dist (fun j ↦ (q : ℝ) * centers i j)
          (fun j ↦ ((oldCenters i).1 j : ℝ)) ≤ k := by
    exact realL1Dist_floorScaledPoint_le hqR.le fun j ↦ (hcover.1 i).1 j |>.1
  have htotal :
      realL1Dist (fun j ↦ (z.1 j : ℝ))
          (fun j ↦ ((oldCenters i).1 j : ℝ)) ≤ (i.1 : ℝ) + k := by
    calc
      realL1Dist (fun j ↦ (z.1 j : ℝ))
          (fun j ↦ ((oldCenters i).1 j : ℝ)) ≤
          realL1Dist (fun j ↦ (z.1 j : ℝ))
            (fun j ↦ (q : ℝ) * centers i j) +
              realL1Dist (fun j ↦ (q : ℝ) * centers i j)
                (fun j ↦ ((oldCenters i).1 j : ℝ)) :=
        realL1Dist_triangle _ _ _
      _ ≤ (i.1 : ℝ) + k := add_le_add hscaledCover hfloor
  rw [realL1Dist_natCast_eq_gammaL1Dist] at htotal
  rw [shiftRankEmbedding_val]
  exact_mod_cast htotal

/--
A path-token burning cover of length at most `t` gives a normalized
ordered-simplex cover of length `t + k`.-/
theorem simplexCoverNumber_le_add_of_pathTokenBurningNumber_le
    {n k t : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) (hkt : k < t)
    (hburn : pathTokenBurningNumber n k hkn ≤ t) :
    simplexCoverNumber k
      (((n - k : ℕ) : ℝ) / ((t + k : ℕ) : ℝ)) ≤ t + k := by
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hkn)
  change (pathTokenGraph n k).burningNumber ≤ t at hburn
  have hlength := (pathTokenGraph n k).burningNumber_spec.mono hburn
  obtain ⟨centers, hcover⟩ := hlength.2
  have hgamma :
      IsGammaRankedCover
        (fun r ↦ configurationEquivGamma hkn (centers r)) :=
    SimpleGraph.IsRankedCover.toGammaRankedCover hkn hcover
  have hk : 1 ≤ k := (by omega : 1 ≤ 2).trans hk2
  have ht : 1 ≤ t := hk.trans hkt.le
  have hq : 1 ≤ t + k := ht.trans (Nat.le_add_right t k)
  apply simplexCoverNumber_min
  exact ⟨hq, hgamma.toSimplexRankedCover_add hq⟩

/--
A normalized ordered-simplex cover number at most `t - k` gives a path-token
burning cover of length at most `t`.-/
theorem pathTokenBurningNumber_le_of_simplexCoverNumber_le_sub
    {n k t : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) (hkt : k < t)
    (hcoverNumber :
      simplexCoverNumber k
        (((n - k : ℕ) : ℝ) / ((t - k : ℕ) : ℝ)) ≤ t - k) :
    pathTokenBurningNumber n k hkn ≤ t := by
  have hk : 1 ≤ k := hk2.trans' (by omega)
  have hq : 1 ≤ t - k := by omega
  have hL : 0 ≤ (((n - k : ℕ) : ℝ) / ((t - k : ℕ) : ℝ)) := by positivity
  have hexists :
      ∃ q, 1 ≤ q ∧
        HasSimplexRankedCover k
          (((n - k : ℕ) : ℝ) / ((t - k : ℕ) : ℝ)) q :=
    exists_simplexRankedCover hk hL
  have hspec := simplexCoverNumber_spec hexists
  have hcover :
      HasSimplexRankedCover k
        (((n - k : ℕ) : ℝ) / ((t - k : ℕ) : ℝ)) (t - k) :=
    hspec.2.mono hL hspec.1 hcoverNumber
  obtain ⟨centers, hcenters⟩ := hcover
  obtain ⟨discreteCenters, hdiscrete⟩ :=
    hcenters.toGammaRankedCover_add hq
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hkn)
  change (pathTokenGraph n k).burningNumber ≤ t
  have hlength :
      (pathTokenGraph n k).IsBurningLength ((t - k) + k) := by
    refine ⟨by omega, ?_⟩
    exact ⟨_, hdiscrete.toPathTokenRankedCover hkn⟩
  exact ((pathTokenGraph n k).burningNumber_min hlength).trans (by omega)

end BurningPath
