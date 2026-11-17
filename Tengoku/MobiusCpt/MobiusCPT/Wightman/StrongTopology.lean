import Tengoku.MobiusCpt.MobiusCPT.Wightman.Basic
import Tengoku.Seed.Analysis.LocallyConvex.SeparatingDual
import Tengoku.Seed.Analysis.LocallyConvex.Separation
import Tengoku.Seed.LinearAlgebra.Complex.Module
import Tengoku.Seed.Topology.Algebra.Group.Basic
import Tengoku.Seed.Topology.Algebra.Module.Basic
import Tengoku.Seed.Topology.Algebra.Module.LocallyConvex
import Tengoku.Seed.Topology.Algebra.MulAction
import Tengoku.Seed.Topology.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MobiusCPT

open scoped Topology

variable {TF 𝓓 𝓕 : Type*}
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF] [TestFunctions TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanStruct

/-- [T26], §2 / [CRTT25], Definition 2.5: a topology on `𝓓` is admissible for the `𝓕`-strong
topology when it makes `𝓓` a locally convex topological `ℂ`-vector space and makes every
`S_{φ₁,…,φ_k,Φ}` continuous.-/
def IsFStrongAdmissible (W : WightmanStruct TF 𝓓 𝓕) (t : TopologicalSpace 𝓓) : Prop :=
  @IsTopologicalAddGroup 𝓓 t _ ∧
    @ContinuousSMul ℂ 𝓓 _ _ t ∧
      @LocallyConvexSpace ℝ 𝓓 _ _ _ _ t ∧
        ∀ (k : ℕ) (φs : Fin k → 𝓕) (Φ : 𝓓),
          @Continuous (Fin k → TF) 𝓓 Pi.topologicalSpace t (W.multiSmear φs Φ)

/-- [T26], §2: the `𝓕`-strong topology, the finest locally convex topology making every
`S_{φ₁,…,φ_k,Φ}` continuous. It is Lean's `sInf` because mathlib orders topologies by reverse
inclusion of opens, so `sInf` IS the classical finest common refinement.-/
@[instance_reducible] def fStrongTopology (W : WightmanStruct TF 𝓓 𝓕) : TopologicalSpace 𝓓 :=
  sInf {t | W.IsFStrongAdmissible t}

/-- [T26], §2: the `𝓕`-strong topology has continuous addition and negation.
@isnad1 id=istopolo.0h4v.s6.28306e2f001c from=translated src=- shape=97b179f9 vocab=7306ebeb
-/
theorem fStrongTopology_isTopologicalAddGroup (W : WightmanStruct TF 𝓓 𝓕) :
    @IsTopologicalAddGroup 𝓓 (fStrongTopology W) _ := by
  exact topologicalAddGroup_sInf fun t ht =>
    (show W.IsFStrongAdmissible t from ht).1

/-- [T26], §2: scalar multiplication on the `𝓕`-strong topology is continuous.
@isnad1 id=continuo.0h4v.s6.81338bc7b452 from=translated src=- shape=04d8e31e vocab=5893b9f2
-/
theorem fStrongTopology_continuousSMul (W : WightmanStruct TF 𝓓 𝓕) :
    @ContinuousSMul ℂ 𝓓 _ _ (fStrongTopology W) := by
  exact continuousSMul_sInf fun t ht =>
    (show W.IsFStrongAdmissible t from ht).2.1

/-- [T26], §2: the `𝓕`-strong topology is locally convex over `ℝ`.
@isnad1 id=locallyc.0h4v.s6.d2ade57d3ae8 from=translated src=- shape=1e2e2e34 vocab=7f1cd0be
-/
theorem fStrongTopology_locallyConvex (W : WightmanStruct TF 𝓓 𝓕) :
    @LocallyConvexSpace ℝ 𝓓 _ _ _ _ (fStrongTopology W) := by
  exact LocallyConvexSpace.sInf (𝕜 := ℝ) (E := 𝓓) fun t ht =>
    (show W.IsFStrongAdmissible t from ht).2.2.1

/-- [T26], §2 / [CRTT25], Definition 2.5: every defining multilinear smearing map is
continuous for the `𝓕`-strong topology.
@isnad1 id=continuo.0h7v.s6.42f8c4b21391 from=translated src=- shape=fcc2d976 vocab=6aeba704
-/
theorem fStrongTopology_continuous_multiSmear (W : WightmanStruct TF 𝓓 𝓕)
    (k : ℕ) (φs : Fin k → 𝓕) (Φ : 𝓓) :
    @Continuous (Fin k → TF) 𝓓 Pi.topologicalSpace (fStrongTopology W)
      (W.multiSmear φs Φ) := by
  apply continuous_sInf_rng.2
  intro t ht
  exact (show W.IsFStrongAdmissible t from ht).2.2.2 k φs Φ

/-- [T26], §2 / [CRTT25], Definition 2.5: the `𝓕`-strong topology is admissible.
@isnad1 id=isfstron.0h4v.s6.9966b3b65e8a from=translated src=- shape=8ef1e82d vocab=64800381
-/
theorem fStrongTopology_isFStrongAdmissible (W : WightmanStruct TF 𝓓 𝓕) :
    W.IsFStrongAdmissible (fStrongTopology W) := by
  refine ⟨fStrongTopology_isTopologicalAddGroup W,
    fStrongTopology_continuousSMul W, fStrongTopology_locallyConvex W, ?_⟩
  exact fStrongTopology_continuous_multiSmear W

/-- [T26], §2 / [CRTT25], Definition 2.5: in mathlib's topology order, `≤` means finer
topology, so this is the "finest such topology" statement and not its opposite.
@isnad1 id=le.1h5v.s6.24146f2881a0 from=translated src=- shape=554a876f vocab=7c138549
-/
theorem fStrongTopology_le (W : WightmanStruct TF 𝓓 𝓕) (t : TopologicalSpace 𝓓) :
    W.IsFStrongAdmissible t → fStrongTopology W ≤ t := by
  intro ht
  exact sInf_le ht

/-- [T26], Definition 2.4 / [CRTT25], Definition 2.5: continuity of a complex-linear
functional for the `𝓕`-strong topology implies compatibility.
@isnad1 id=iscompat.1h5v.s7.63a6f54c9ecb from=translated src=- shape=abd257b6 vocab=02f83899
-/
theorem isCompatible_of_continuous (W : WightmanStruct TF 𝓓 𝓕)
    (lam : 𝓓 →ₗ[ℂ] ℂ)
    (h : Continuous[fStrongTopology W, inferInstance] lam) : W.IsCompatible lam := by
  let : TopologicalSpace 𝓓 := fStrongTopology W
  intro k φs Φ
  simpa only [Function.comp_def] using
    h.comp (fStrongTopology_continuous_multiSmear W k φs Φ)

/-- [T26], Definition 2.4 / [CRTT25], Definition 2.5: compatibility implies continuity for
the `𝓕`-strong topology. This uses the finest-ness property through `fStrongTopology_le`.
@isnad1 id=continuo.1h5v.s7.9a6514e8aa39 from=translated src=- shape=4ad2d32a vocab=02f83899
-/
theorem continuous_of_isCompatible (W : WightmanStruct TF 𝓓 𝓕)
    (lam : 𝓓 →ₗ[ℂ] ℂ) (h : W.IsCompatible lam) :
    Continuous[fStrongTopology W, inferInstance] lam := by
  let tlam : TopologicalSpace 𝓓 := TopologicalSpace.induced lam inferInstance
  have hgroup : @IsTopologicalAddGroup 𝓓 tlam _ := by
    change @IsTopologicalAddGroup 𝓓
      (TopologicalSpace.induced lam inferInstance) _
    exact topologicalAddGroup_induced lam
  have hsmul : @ContinuousSMul ℂ 𝓓 _ _ tlam := by
    change @ContinuousSMul ℂ 𝓓 _ _
      (TopologicalSpace.induced lam inferInstance)
    exact continuousSMul_induced lam
  have hconvex : @LocallyConvexSpace ℝ 𝓓 _ _ _ _ tlam := by
    change @LocallyConvexSpace ℝ 𝓓 _ _ _ _
      (TopologicalSpace.induced (lam.restrictScalars ℝ) inferInstance)
    exact LocallyConvexSpace.induced (lam.restrictScalars ℝ)
  have hmulti : ∀ (k : ℕ) (φs : Fin k → 𝓕) (Φ : 𝓓),
      @Continuous (Fin k → TF) 𝓓 Pi.topologicalSpace tlam (W.multiSmear φs Φ) := by
    intro k φs Φ
    change @Continuous (Fin k → TF) 𝓓 Pi.topologicalSpace
      (TopologicalSpace.induced lam inferInstance) (W.multiSmear φs Φ)
    apply continuous_induced_rng.2
    simpa only [Function.comp_def] using h k φs Φ
  have hadm : W.IsFStrongAdmissible tlam :=
    ⟨hgroup, hsmul, hconvex, hmulti⟩
  have hle : fStrongTopology W ≤ tlam := fStrongTopology_le W tlam hadm
  have hind : Continuous[tlam, inferInstance] lam := by
    change @Continuous 𝓓 ℂ
      (TopologicalSpace.induced lam inferInstance) inferInstance lam
    exact continuous_induced_dom
  exact continuous_le_dom hle hind

/-- [T26], Definition 2.4 / [CRTT25], Definition 2.5: the continuous dual for the
`𝓕`-strong topology is exactly the space of compatible functionals.
@isnad1 id=iff.0h5v.s7.3ad87cd75799 from=translated src=- shape=bccc4048 vocab=02f83899
-/
theorem continuous_iff_isCompatible (W : WightmanStruct TF 𝓓 𝓕)
    (lam : 𝓓 →ₗ[ℂ] ℂ) :
    Continuous[fStrongTopology W, inferInstance] lam ↔ W.IsCompatible lam := by
  constructor
  · exact isCompatible_of_continuous W lam
  · exact continuous_of_isCompatible W lam

/-- [CRTT25], Lemma 2.7: regularity of `𝓕` separates points in the `𝓕`-strong topology.
@isnad1 id=t2space.1h4v.s6.c04ca9a4844d from=translated src=- shape=4f24d1f9 vocab=2198caeb
-/
theorem t2Space_of_actsRegularly (W : WightmanStruct TF 𝓓 𝓕)
    (h : W.ActsRegularly) : @T2Space 𝓓 (fStrongTopology W) := by
  let : TopologicalSpace 𝓓 := fStrongTopology W
  let : SeparatingDual ℂ 𝓓 :=
    { exists_ne_zero' := by
        intro Φ hΦ
        obtain ⟨lam, hlam⟩ := h Φ hΦ
        have hlam' : @Continuous 𝓓 ℂ (fStrongTopology W) inferInstance lam.1 :=
          (continuous_iff_isCompatible W lam.1).2 lam.property
        let f : StrongDual ℂ 𝓓 := ⟨lam.1, hlam'⟩
        refine ⟨f, ?_⟩
        simpa [f, compatApply] using hlam }
  exact SeparatingDual.t2Space (R := ℂ) (V := 𝓓)

/-- [CRTT25], Lemma 2.7: Hausdorffness of the `𝓕`-strong topology yields a compatible
functional separating every non-zero domain vector. This uses only continuity, not
the finest-ness argument.
@isnad1 id=actsregu.1h4v.s6.850f5f698d0a from=translated src=- shape=a54045c5 vocab=2198caeb
-/
theorem actsRegularly_of_t2Space (W : WightmanStruct TF 𝓓 𝓕)
    (h : @T2Space 𝓓 (fStrongTopology W)) : W.ActsRegularly := by
  let : TopologicalSpace 𝓓 := fStrongTopology W
  let : IsTopologicalAddGroup 𝓓 := fStrongTopology_isTopologicalAddGroup W
  let : ContinuousSMul ℂ 𝓓 := fStrongTopology_continuousSMul W
  let : LocallyConvexSpace ℝ 𝓓 := fStrongTopology_locallyConvex W
  let : T2Space 𝓓 := h
  intro Φ hΦ
  obtain ⟨f, hf⟩ :=
    RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) (E := 𝓓) hΦ
  have hfne : f Φ ≠ 0 := by
    intro hzero
    apply (ne_of_lt hf)
    simp [hzero]
  have hfcont : @Continuous 𝓓 ℂ (fStrongTopology W) inferInstance f.toLinearMap :=
    f.continuous
  have hcompat : W.IsCompatible f.toLinearMap :=
    (continuous_iff_isCompatible W f.toLinearMap).1 hfcont
  refine ⟨⟨f.toLinearMap, hcompat⟩, ?_⟩
  simpa [compatApply] using hfne

/-- [CRTT25], Lemma 2.7: `𝓕` acts regularly if and only if the `𝓕`-strong topology is
Hausdorff.
@isnad1 id=iff.0h4v.s6.d34f14d12aac from=translated src=- shape=ca03ef7f vocab=2198caeb
-/
theorem actsRegularly_iff_t2Space (W : WightmanStruct TF 𝓓 𝓕) :
    W.ActsRegularly ↔ @T2Space 𝓓 (fStrongTopology W) := by
  constructor
  · exact t2Space_of_actsRegularly W
  · exact actsRegularly_of_t2Space W

end WightmanStruct

end MobiusCPT
