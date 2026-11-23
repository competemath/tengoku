import Tengoku.NavierStokesEuler.Euler.PacketCylinderKnownJets
import Tengoku.NavierStokesEuler.Euler.PacketCylinderJetOperations
import Tengoku.NavierStokesEuler.Euler.PacketCylinderTimeParity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual spatial derivatives and nonlinear jet terms preserve joint odd velocity parity. -/

noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

abbrev JointOdd (T : ℝ) (raw : VectorField) : Prop :=
  ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ))

namespace JointOdd

variable {T : ℝ} {f g : VectorField}

/--
@isnad1 id=jointodd.0h1v.s6.b5b63bccae46 from=translated src=- shape=8ba9e24c vocab=8d577416
-/
theorem zero (T : ℝ) : JointOdd T (0 : VectorField) := by
  intro t x θ
  simp only [Pi.zero_apply,neg_zero]

/--
@isnad1 id=jointodd.2h3v.s6.f2109eafb24d from=translated src=- shape=d203bb48 vocab=4f7b0988
-/
theorem add (hf : JointOdd T f) (hg : JointOdd T g) : JointOdd T (f+g) := by
  intro t x θ
  simp only [Pi.add_apply,hf t x θ,hg t x θ,neg_add]

/--
@isnad1 id=jointodd.1h2v.s6.eb0357aeaa5e from=translated src=- shape=d086edac vocab=62092ecb
-/
theorem neg (hf : JointOdd T f) : JointOdd T (-f) := by
  intro t x θ
  simp only [Pi.neg_apply,hf t x θ]

/--
@isnad1 id=jointodd.2h3v.s6.976de1aa6470 from=translated src=- shape=d203bb48 vocab=082b4261
-/
theorem sub (hf : JointOdd T f) (hg : JointOdd T g) : JointOdd T (f-g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
@isnad1 id=jointodd.2h3v.s6.fc3f85e50143 from=translated src=- shape=b5498869 vocab=b6a3527e
-/
theorem congr (hf : JointOdd T f)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, g (t,(x,θ)) = f (t,(x,θ))) : JointOdd T g := by
  intro t x θ
  rw [he,he,hf]

end JointOdd

variable {P T : ℝ} [Fact (0 < P)]

/--
@isnad1 id=eq.1h7v.s10.c954be98352e from=translated src=- shape=800f4221 vocab=87cb835d
-/
theorem Field.raw_fderiv_even_of_odd {raw : VectorField} (G : Field P T raw)
    (hodd : JointOdd T raw) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    fderiv ℝ (fun y : LiftTangent => raw (t,y)) (-x,-θ) =
      fderiv ℝ (fun y : LiftTangent => raw (t,y)) (x,θ) := by
  have hf := G.raw_smooth t
  have he : (fun y : LiftTangent => raw (t,-y)) =
      fun y : LiftTangent => -raw (t,y) := funext (fun y => hodd t y.1 y.2)
  have h₁ := ((hf.differentiable (by simp) (-(x,θ))).hasFDerivAt).comp (x,θ)
    ((hasFDerivAt_id (𝕜 := ℝ) (x,θ)).neg)
  have h₂ := ((hf.differentiable (by simp) (x,θ)).hasFDerivAt).neg
  have hfd : fderiv ℝ (fun y : LiftTangent => -raw (t,y)) (x,θ) =
      -fderiv ℝ (fun y : LiftTangent => raw (t,y)) (x,θ) := h₂.fderiv
  have hd : -fderiv ℝ (fun y : LiftTangent => raw (t,y)) (x,θ) =
      -fderiv ℝ (fun y : LiftTangent => raw (t,y)) (-(x,θ)) := by
    simpa only [Function.comp_def,he,hfd,comp_neg,comp_id] using h₁.fderiv
  exact neg_injective hd.symm

namespace SpatialJetField

variable {J K : Domain → VectorJet} (H : SpatialJetField P T K)

include H

/--
@isnad1 id=eq.1h8v.s12.cb1dc42fe53f from=translated src=- shape=7d1d67ff vocab=f3890645
-/
theorem spatial_even_of_value_odd (hK : JointOdd T (fun z => (K z).1))
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) (v : SpatialDomain) :
    (K (t,(-x,-θ))).2 (0,v) = (K (t,(x,θ))).2 (0,v) := by
  have hr : JointOdd T H.raw := by
    intro s y η
    rw [← H.value_eq,← H.value_eq]
    exact hK s y η
  rw [H.spatial_eq,H.spatial_eq,H.field.raw_fderiv_even_of_odd hr t x θ]

/--
@isnad1 id=jointodd.3h6v.s15.211455e026ac from=translated src=- shape=ea1ffff4 vocab=af9e014c
-/
theorem slowAdvection_odd (inverse : Domain → Space →L[ℝ] Space)
    (hI : ∀ (t : Icc (0 : ℝ) T) x θ, inverse (t,(-x,-θ)) = inverse (t,(x,θ)))
    (hJ : JointOdd T (fun z => (J z).1)) (hK : JointOdd T (fun z => (K z).1)) :
    JointOdd T (fun z => EulerPacketPointJets.slowAdvection (inverse z) (J z) (K z)) := by
  intro t x θ
  have hD : (K (t,(-x,-θ))).2.comp spatialInjection =
      (K (t,(x,θ))).2.comp spatialInjection := by
    apply ContinuousLinearMap.ext
    intro v
    exact H.spatial_even_of_value_odd hK t x θ (v,0)
  change ((K (t,(-x,-θ))).2.comp spatialInjection) (inverse (t,(-x,-θ)) (J (t,(-x,-θ))).1) =
    -((K (t,(x,θ))).2.comp spatialInjection) (inverse (t,(x,θ)) (J (t,(x,θ))).1)
  have hj : (J (t,(-x,-θ))).1 = -(J (t,(x,θ))).1 := hJ t x θ
  rw [hD,hI t x θ,hj,map_neg,map_neg]

/--
@isnad1 id=jointodd.3h6v.s15.2491a49151e7 from=translated src=- shape=684ce4ea vocab=d23d0ab6
-/
theorem fastAdvection_odd (normal : VectorField)
    (hN : ∀ (t : Icc (0 : ℝ) T) x θ, normal (t,(-x,-θ)) = normal (t,(x,θ)))
    (hJ : JointOdd T (fun z => (J z).1)) (hK : JointOdd T (fun z => (K z).1)) :
    JointOdd T (fun z => EulerPacketPointJets.fastAdvection (normal z) (J z) (K z)) := by
  intro t x θ
  change inner ℝ (normal (t,(-x,-θ))) (J (t,(-x,-θ))).1 • (K (t,(-x,-θ))).2 (0,(0,1)) =
    -(inner ℝ (normal (t,(x,θ))) (J (t,(x,θ))).1 • (K (t,(x,θ))).2 (0,(0,1)))
  have hj : (J (t,(-x,-θ))).1 = -(J (t,(x,θ))).1 := hJ t x θ
  rw [hN t x θ,hj,H.spatial_even_of_value_odd hK t x θ (0,1),inner_neg_right,neg_smul]

end SpatialJetField

end EulerPacketCylinderField
