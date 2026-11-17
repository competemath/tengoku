import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Analytic.CPolynomialDef

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multilinear lifts of analytic homogeneous maps

A map that is analytic at `0` and homogeneous of degree `k` is the diagonal of a
continuous `k`-linear map, namely its degree-`k` Taylor coefficient. The proof restricts
to lines and uses uniqueness of one-variable power series (Lemma A.1).
-/

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Y] [NormedSpace K Y]

/-- The one-variable series supported only in degree `k`, with coefficient `v`.-/
private noncomputable def monomialSeries (k : ℕ) (v : Y) :
    FormalMultilinearSeries K K Y :=
  fun n => ContinuousMultilinearMap.mkPiRing K (Fin n) (if n = k then v else 0)

private lemma hasFPowerSeriesAt_monomialSeries (k : ℕ) (v : Y) :
    HasFPowerSeriesAt (fun t : K => t ^ k • v) (monomialSeries k v) 0 := by
  have h : HasFiniteFPowerSeriesOnBall (fun t : K => t ^ k • v)
      (monomialSeries k v) 0 (k + 1) ⊤ := by
    refine HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
    · intro n hn
      have hne : n ≠ k := by omega
      simp [monomialSeries, hne, ContinuousMultilinearMap.mkPiRing_zero]
    · intro t _
      simp [monomialSeries, ContinuousMultilinearMap.mkPiRing_apply, smul_ite]
  exact h.hasFiniteFPowerSeriesAt.hasFPowerSeriesAt

/-- A map analytic at `0` and homogeneous of degree `k` is the diagonal of a continuous
`k`-linear map.
@isnad1 id=ex.2h5v.s9.f87e989d5ba9 from=translated src=- shape=5bec3c6f vocab=91141521
-/
theorem AnalyticAt.exists_multilinearMap_eq_of_homogeneous
    (k : ℕ) (f : X → Y) (hf : AnalyticAt K f 0)
    (hhom : ∀ (c : K) (x : X), f (c • x) = c ^ k • f x) :
    ∃ P : ContinuousMultilinearMap K (fun _ : Fin k => X) Y,
      ∀ x, P (fun _ => x) = f x := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p k, fun x => ?_⟩
  let u : K →L[K] X := (ContinuousLinearMap.id K K).smulRight x
  have hu : ∀ t : K, u t = t • x := fun _ => rfl
  have hp0 : HasFPowerSeriesAt f p (u 0) := by
    simpa only [hu, zero_smul] using hp
  have h1 : HasFPowerSeriesAt (f ∘ u) (p.compContinuousLinearMap u) 0 :=
    hp0.compContinuousLinearMap
  have h2 : (f ∘ u) = fun t : K => t ^ k • f x := by
    funext t
    exact hhom t x
  rw [h2] at h1
  have heq := h1.eq_formalMultilinearSeries (hasFPowerSeriesAt_monomialSeries k (f x))
  have key := congrArg (fun q : FormalMultilinearSeries K K Y => q k (fun _ => 1)) heq
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply] at key
  simpa [monomialSeries,
    ContinuousMultilinearMap.mkPiRing_apply, Function.comp_def, hu] using key

end AlternatingAnalytic
