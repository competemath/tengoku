import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.NormalizeMoves

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ambient isotopies as signed framed cobordisms

The normalization argument must move embedded fiber circles, not only rescale
or translate a whole presentation.  This file supplies the general geometric
bridge: a smooth one-parameter family of ambient diffeomorphisms transports a
framed level set and its sign label through an actual signed framed
cobordism.

The inverse family is stored explicitly.  Surjectivity of its spatial
differential is the only differential datum used below; for a concrete
diffeomorphism path it follows by differentiating the two inverse identities.
Spatial boundedness is not an extra field: it follows from compactness of the
original fiber and continuity of the forward track on `[0,1]`.
-/

noncomputable section

open Set Function Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- A smooth ambient isotopy, presented together with its smooth inverse.

Only the interval `[0,1]` is geometrically relevant.  The maps are total on
`ℝ` so that they compose directly with the collar-flat switch `normRamp`.-/
structure SmoothAmbientIsotopy (n : ℕ) where
  forward : ℝ → EuclideanSpace ℝ (Fin (n + 1)) →
    EuclideanSpace ℝ (Fin (n + 1))
  inverse : ℝ → EuclideanSpace ℝ (Fin (n + 1)) →
    EuclideanSpace ℝ (Fin (n + 1))
  forward_smooth : ContDiff ℝ ∞
    (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => forward p.1 p.2)
  inverse_smooth : ContDiff ℝ ∞
    (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => inverse p.1 p.2)
  forward_zero : forward 0 = id
  left_inv : ∀ s ∈ Icc (0 : ℝ) 1, LeftInverse (inverse s) (forward s)
  right_inv : ∀ s ∈ Icc (0 : ℝ) 1, RightInverse (inverse s) (forward s)
  inverse_fderiv_surjective : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
    Surjective (fderiv ℝ (inverse s) x)

namespace SmoothAmbientIsotopy

variable (A : SmoothAmbientIsotopy n)

/--
@isnad1 id=eq.0h3v.s5.5c2a2a931e20 from=translated src=- shape=b78e8d5a vocab=86dac23c
-/
lemma inverse_zero (x : E) : A.inverse 0 x = x := by
  have h := A.right_inv 0 ⟨le_rfl, zero_le_one⟩ x
  rw [A.forward_zero] at h
  exact h

/--
@isnad1 id=contdiff.0h3v.s8.a680ea161273 from=translated src=- shape=0841a5a2 vocab=4d789bc3
-/
lemma contDiff_forward_slice (s : ℝ) : ContDiff ℝ ∞ (A.forward s) := by
  exact A.forward_smooth.comp (contDiff_const.prodMk contDiff_id)

/--
@isnad1 id=contdiff.0h3v.s8.7d8363c25246 from=translated src=- shape=0841a5a2 vocab=c250d486
-/
lemma contDiff_inverse_slice (s : ℝ) : ContDiff ℝ ∞ (A.inverse s) := by
  exact A.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)

/-- The endpoint presentation obtained by pulling the defining equations back
through the inverse ambient diffeomorphism.-/
def pullback (X : FramedLevelSet n) : FramedLevelSet n where
  g x := X.g (A.inverse 1 x)
  smooth := X.smooth.comp (A.contDiff_inverse_slice 1)
  fiber_bounded := by
    have hcompact : IsCompact (A.forward 1 '' X.fiber) :=
      X.isCompact_fiber.image (A.contDiff_forward_slice 1).continuous
    apply hcompact.isBounded.subset
    intro x hx
    have hxin : A.inverse 1 x ∈ X.fiber := hx
    have hright := A.right_inv 1 ⟨zero_le_one, le_rfl⟩ x
    refine ⟨A.inverse 1 x, hxin, ?_⟩
    exact hright
  regular := by
    intro x hx
    have hX : Surjective (fderiv ℝ X.g (A.inverse 1 x)) := X.regular _ hx
    have hA : Surjective (fderiv ℝ (A.inverse 1) x) :=
      A.inverse_fderiv_surjective 1 ⟨zero_le_one, le_rfl⟩ x
    have hchain : fderiv ℝ (fun y => X.g (A.inverse 1 y)) x =
        (fderiv ℝ X.g (A.inverse 1 x)).comp
          (fderiv ℝ (A.inverse 1) x) := by
      exact ((X.smooth.differentiable (by simp) _).hasFDerivAt.comp x
        ((A.contDiff_inverse_slice 1).differentiable (by simp) x).hasFDerivAt).fderiv
    rw [hchain]
    exact hX.comp hA

/--
@isnad1 id=eq.0h4v.s5.c67251493584 from=translated src=- shape=05224a7b vocab=a3131136
-/
@[simp] theorem pullback_g (X : FramedLevelSet n) (x : E) :
    (A.pullback X).g x = X.g (A.inverse 1 x) := rfl

/-- The endpoint fiber is the forward image of the source fiber.
@isnad1 id=eq.0h3v.s6.a154fe179f7f from=translated src=- shape=f9a8da81 vocab=30536238
-/
theorem pullback_fiber (X : FramedLevelSet n) :
    (A.pullback X).fiber = A.forward 1 '' X.fiber := by
  ext x
  constructor
  · intro hx
    refine ⟨A.inverse 1 x, hx, ?_⟩
    exact A.right_inv 1 ⟨zero_le_one, le_rfl⟩ x
  · rintro ⟨y, hy, rfl⟩
    change X.g (A.inverse 1 (A.forward 1 y)) = 0
    rw [A.left_inv 1 ⟨zero_le_one, le_rfl⟩ y]
    exact hy

/-- Transport a sign label through the endpoint ambient diffeomorphism.-/
def pullbackSign {X : FramedLevelSet n} (S : FiberSign X) :
    FiberSign (A.pullback X) where
  toFun x := S (A.inverse 1 x)
  continuous := S.continuous.comp (A.contDiff_inverse_slice 1).continuous
  nonzero _ hx := S.nonzero _ hx

/--
@isnad1 id=eq.0h5v.s5.b027306a0aaa from=translated src=- shape=bacdc11a vocab=21088930
-/
@[simp] theorem pullbackSign_apply {X : FramedLevelSet n}
    (S : FiberSign X) (x : E) :
    A.pullbackSign S x = S (A.inverse 1 x) := rfl

/-- The inverse ambient track, run along the collar-flat time switch.-/
def inverseTrack
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : E :=
  A.inverse (normRamp (vertC v)) (initCLM (n + 1) v)

/--
@isnad1 id=eq.0h4v.s5.bdc746c28a97 from=translated src=- shape=370451c2 vocab=549914ed
-/
lemma inverseTrack_spaceTime (x : E) (t : ℝ) :
    A.inverseTrack (spaceTime x t) = A.inverse (normRamp t) x := by
  rw [inverseTrack, vertC_spaceTime, initCLM_spaceTime]

/--
@isnad1 id=contdiff.0h2v.s9.04fd0143ecc7 from=translated src=- shape=ef99916a vocab=f53c9a8c
-/
lemma contDiff_inverseTrack : ContDiff ℝ ∞ A.inverseTrack := by
  exact A.inverse_smooth.comp
    ((contDiff_normRamp.comp contDiff_vertC).prodMk (initCLM (n + 1)).contDiff)

/--
@isnad1 id=eq.1h4v.s6.58fb32f6f422 from=translated src=- shape=6df301ce vocab=702e8bc7
-/
lemma inverseTrack_of_le_quarter (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    A.inverseTrack (spaceTime x t) = x := by
  rw [A.inverseTrack_spaceTime, normRamp_of_le_quarter ht, A.inverse_zero]

/--
@isnad1 id=eq.1h4v.s6.b9e194d10172 from=translated src=- shape=5cb8eb3f vocab=9984f093
-/
lemma inverseTrack_of_three_quarter_le (x : E) {t : ℝ}
    (ht : 3 / 4 ≤ t) :
    A.inverseTrack (spaceTime x t) = A.inverse 1 x := by
  rw [A.inverseTrack_spaceTime, normRamp_of_three_quarter_le ht]

/-- The framed cobordism swept out by the ambient isotopy.-/
def cobordism (X : FramedLevelSet n) : FramedLevelCobordism n where
  X₀ := X
  X₁ := A.pullback X
  G v := X.g (A.inverseTrack v)
  smooth := X.smooth.comp A.contDiff_inverseTrack
  spatial_bounded := by
    let K : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ X.fiber
    have hK : IsCompact K := isCompact_Icc.prod X.isCompact_fiber
    let F : ℝ × E → E := fun p => A.forward p.1 p.2
    have hF : Continuous F := A.forward_smooth.continuous
    have hImage : IsCompact (F '' K) := hK.image hF
    obtain ⟨R, hR⟩ := hImage.isBounded.subset_closedBall (0 : E)
    refine ⟨R, ?_⟩
    intro v hv
    let s : ℝ := normRamp (vertC v)
    let y : E := A.inverseTrack v
    have hs : s ∈ Icc (0 : ℝ) 1 := ⟨normRamp_nonneg _, normRamp_le_one _⟩
    have hy : y ∈ X.fiber := hv
    have hxy : A.forward s y = initCLM (n + 1) v := by
      exact A.right_inv s hs (initCLM (n + 1) v)
    have himage : initCLM (n + 1) v ∈ F '' K := by
      refine ⟨(s, y), ⟨hs, hy⟩, ?_⟩
      exact hxy
    have hball := hR himage
    rwa [mem_closedBall, dist_zero_right] at hball
  regular := by
    intro v hv
    apply surjective_fderiv_of_slice (X.smooth.comp A.contDiff_inverseTrack)
    let s : ℝ := normRamp (vertC v)
    let x : E := initCLM (n + 1) v
    have hs : s ∈ Icc (0 : ℝ) 1 := ⟨normRamp_nonneg _, normRamp_le_one _⟩
    change Surjective
      (fderiv ℝ (fun x' : E => X.g
        (A.inverseTrack (spaceTime x' (vertC v)))) x)
    have hfun : (fun x' : E => X.g (A.inverseTrack (spaceTime x' (vertC v)))) =
        fun x' => X.g (A.inverse s x') := by
      funext x'
      rw [A.inverseTrack_spaceTime]
    rw [hfun]
    have hchain : fderiv ℝ (fun x' : E => X.g (A.inverse s x')) x =
        (fderiv ℝ X.g (A.inverse s x)).comp
          (fderiv ℝ (A.inverse s) x) := by
      exact ((X.smooth.differentiable (by simp) _).hasFDerivAt.comp x
        ((A.contDiff_inverse_slice s).differentiable (by simp) x).hasFDerivAt).fderiv
    rw [hchain]
    exact (X.regular _ hv).comp (A.inverse_fderiv_surjective s hs x)
  collar_zero := by
    intro x t ht
    rw [A.inverseTrack_of_le_quarter x ht]
  collar_one := by
    intro x t ht
    rw [A.inverseTrack_of_three_quarter_le x ht]
    rfl

/-- The signed cobordism swept out by a labeled fiber under the ambient
isotopy.-/
def signedCobordism {X : FramedLevelSet n} (S : FiberSign X) :
    SignedFramedLevelCobordism S (A.pullbackSign S) where
  cobordism := A.cobordism X
  source_eq := rfl
  target_eq := rfl
  toFun v := S (A.inverseTrack v)
  continuous := S.continuous.comp A.contDiff_inverseTrack.continuous
  nonzero v hv := S.nonzero _ hv
  collar_zero := by
    intro x t ht
    rw [A.inverseTrack_of_le_quarter x ht]
  collar_one := by
    intro x t ht
    rw [A.inverseTrack_of_three_quarter_le x ht]
    rfl

/-- Every smooth ambient isotopy therefore gives an actual signed framed
cobordism to the transported endpoint presentation.
@isnad1 id=nonempty.0h4v.s4.52b60195463c from=translated src=- shape=cb880272 vocab=d6f8271e
-/
theorem nonempty_signedCobordism {X : FramedLevelSet n} (S : FiberSign X) :
    Nonempty (SignedFramedLevelCobordism S (A.pullbackSign S)) :=
  ⟨A.signedCobordism S⟩

end SmoothAmbientIsotopy

end Submission
