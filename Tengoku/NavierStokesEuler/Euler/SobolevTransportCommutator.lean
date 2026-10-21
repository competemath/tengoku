import Tengoku.NavierStokesEuler.Euler.FunctionalVelocity
import Tengoku.NavierStokesEuler.Euler.SobolevWordLevel
import Tengoku.NavierStokesEuler.Euler.GevreyCorrectionSplit

/-! Tengoku repair: `externalCommutator` ran out of heartbeats in the tree; `synthInstance.maxHeartbeats` is 160000 for it (was 20000). -/

namespace EulerSobolevTransportCommutator
end EulerSobolevTransportCommutator
namespace MeasureTheory
end MeasureTheory
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerCylinderSobolev
end EulerCylinderSobolev
namespace EulerSpatialSobolevInverse
end EulerSpatialSobolevInverse
namespace EulerMetricTransport
end EulerMetricTransport
namespace EulerSobolevWordBlocks
end EulerSobolevWordBlocks
namespace EulerH6Pressure
end EulerH6Pressure
namespace EulerStrongSmoothJet
end EulerStrongSmoothJet
namespace EulerSobolevGevreyOperators
end EulerSobolevGevreyOperators
namespace EulerSobolevWordLevel
end EulerSobolevWordLevel
namespace EulerSobolevTransport
end EulerSobolevTransport
namespace EulerSobolevL2Product
end EulerSobolevL2Product
namespace EulerFunctionalVelocity
end EulerFunctionalVelocity
namespace EulerH6Nonlinear
end EulerH6Nonlinear
namespace EulerVectorCylinder
end EulerVectorCylinder
namespace EulerExternalTransportCommutator
end EulerExternalTransportCommutator
namespace EulerTransportDerivatives
end EulerTransportDerivatives
namespace ContDiff
end ContDiff
namespace ENNReal
end ENNReal
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The genuine external transport commutator as a bounded bilinear Sobolev operator. -/

noncomputable section

namespace EulerSobolevTransportCommutator
open _root_.EulerSobolevTransportCommutator

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerSobolevWordBlocks EulerH6Pressure EulerStrongSmoothJet
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator EulerTransportDerivatives
open _root_.MeasureTheory _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerCylinderSobolev _root_.EulerSpatialSobolevInverse _root_.EulerMetricTransport _root_.EulerSobolevWordBlocks _root_.EulerH6Pressure _root_.EulerStrongSmoothJet _root_.EulerSobolevGevreyOperators _root_.EulerSobolevWordLevel _root_.EulerSobolevTransport _root_.EulerSobolevL2Product _root_.EulerFunctionalVelocity _root_.EulerH6Nonlinear _root_.EulerVectorCylinder _root_.EulerExternalTransportCommutator _root_.EulerTransportDerivatives
open scoped ContDiff _root_.ContDiff ENNReal _root_.ENNReal Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

local instance commutatorGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance commutatorSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
local instance commutatorBilinearGroup (q r : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period q →L[ℝ] SobolevSpace period q →L[ℝ] SobolevSpace period r) := inferInstance

set_option synthInstance.maxHeartbeats 160000 in
/-- The actual difference D^w(z·D e)−z·D(D^w e), with all operands on their genuine Sobolev domains. -/
def externalCommutator {s : ℕ} (hs : 6 ≤ s) (n : ℕ) (w : Fin n → Fin 4) (hn : n+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    SobolevSpace period (s+1) →L[ℝ] SobolevSpace period (s+1) →L[ℝ] SobolevSpace period 6 :=
  ((ContinuousLinearMap.compL ℝ (SobolevSpace period (s+1)) (SobolevSpace period s) (SobolevSpace period 6)
    (wordAtLevel period 6 n w hn)).comp (transportBilinear period hs L hL)) -
  (transportBilinear period (by norm_num : 6 ≤ 6) L hL).bilinearComp
    (restrictOperator period (by omega : 7 ≤ s+1)) (wordAtLevel period 7 n w (by omega : n+7 ≤ s+1))

/-- Explicit actual Sobolev operands of the transport commutator. -/
theorem externalCommutator_apply {s : ℕ} (hs : 6 ≤ s) (n : ℕ) (w : Fin n → Fin 4) (hn : n+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    externalCommutator period hs n w hn L hL u v =
      wordAtLevel period 6 n w hn (transportBilinear period hs L hL u v) -
      transportBilinear period (by norm_num : 6 ≤ 6) L hL
        (restrictOperator period (by omega : 7 ≤ s+1) u)
        (wordAtLevel period 7 n w (by omega : n+7 ≤ s+1) v) := rfl

omit [Fact (0 < period)] in
/-- Classical transport of smooth cylinder fields is smooth. -/
theorem transportField_smooth (b : LiftDomain period → EulerSobolev.Domain 4) (g : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (transportField period 3 b g) x) := by
  apply smooth_sum period Finset.univ
  intro i _ x
  exact (postcomp_smooth period (coordinate 4 i) b hb x).smul (fieldDerivative_smooth period _ g hg x)

/-- The actual Sobolev transport is the classical transport by its assembled four-dimensional velocity. -/
theorem transport_ae_velocityMap {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (value period (transportBilinear period hs L hL u v) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      transportField period 3 (velocityMap L ∘ f) g := by
  have heq : (fun x => ∑ i : Fin 4, L i (f x) • fieldDerivative period (standardDirection i) g x) =
      transportField period 3 (velocityMap L ∘ f) g := by
    funext x
    simp only [transportField, Finset.sum_apply, Function.comp_apply, velocityMap_apply]
  rw [← heq]
  exact transportBilinear_ae period hs L hL u v f g hu hv hg

/-- On genuine smooth representatives the bounded Sobolev commutator is exactly the classical derivative commutator. -/
theorem externalCommutator_ae {s : ℕ} (hs : 6 ≤ s) (n : ℕ) (w : Fin n → Fin 4) (hn : n+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (value period (externalCommutator period hs n w hn L hL u v) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      transportCommutator period w (velocityMap L ∘ f) g := by
  let b := velocityMap L ∘ f
  have hb := postcomp_smooth period (velocityMap L) f hf
  have hT := transport_ae_velocityMap period hs L hL u v f g hu hv hg
  have hfirst := wordAtLevel_ae period 6 n w hn (transportBilinear period hs L hL u v)
    (transportField period 3 b g) hT (transportField_smooth period b g hb hg)
  have hw := wordAtLevel_ae period 7 n w (by omega : n+7 ≤ s+1) v g hv hg
  have hsecond := transport_ae_velocityMap period (by norm_num : 6 ≤ 6) L hL
    (restrictOperator period (by omega : 7 ≤ s+1) u) (wordAtLevel period 7 n w (by omega) v)
    f (iteratedFieldDerivative period w g) hu hw (iteratedFieldDerivative_smooth period w g hg)
  rw [externalCommutator_apply]
  change ((valueOperator period 6) (_-_) : LiftDomain period → Vector3) =ᵐ[liftMeasure period] _
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (value period (wordAtLevel period 6 n w hn (transportBilinear period hs L hL u v)))
    (value period (transportBilinear period (by norm_num : 6 ≤ 6) L hL
      (restrictOperator period (by omega : 7 ≤ s+1) u) (wordAtLevel period 7 n w (by omega) v))), hfirst,hsecond]
    with x hx h1 h2
  simp only [Pi.sub_apply] at hx
  exact hx.trans (by rw [h1,h2]; rfl)

omit [Fact (0 < period)] in
/-- The classical external transport commutator is smooth for smooth fields. -/
theorem transportCommutator_smooth {n : ℕ} (w : Fin n → Fin 4)
    (b : LiftDomain period → EulerSobolev.Domain 4) (g : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (transportCommutator period w b g) x) := by
  intro x
  exact (iteratedFieldDerivative_smooth period w (transportField period 3 b g)
    (transportField_smooth period b g hb hg) x).sub
    (transportField_smooth period b (iteratedFieldDerivative period w g) hb (iteratedFieldDerivative_smooth period w g hg) x)

/-- The actual Sobolev commutator norm equals the source's classical H⁶ norm whenever smooth representatives are available. -/
theorem externalCommutator_sumNorm {s : ℕ} (hs : 6 ≤ s) (n : ℕ) (w : Fin n → Fin 4) (hn : n+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    sumNorm period (externalCommutator period hs n w hn L hL u v) =
      liftSobolevNorm period 6 (transportCommutator period w (velocityMap L ∘ f) g) :=
  sumNorm_eq_classical period _ _ (externalCommutator_ae period hs n w hn L hL u v f g hu hv hf hg)
    (transportCommutator_smooth period w _ g (postcomp_smooth period (velocityMap L) f hf) hg)

end EulerSobolevTransportCommutator
