import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedProjectorImageBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms scalar_compression_on_hyperbolic_image` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_actual_weighted_first_projector_coordinates` (it only prints; the queue checks the axioms of every declaration). -/

/-! Scalar compression and weighted coordinates consumed by Q1. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.SymplecticProjectorFrame
open AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- A self-adjoint compression of a self-adjoint projector to an explicitly
spanned hyperbolic projector image is scalar.  Its scalar is the displayed
symplectic overlap, so no rank theorem or assumed weighted normal form enters.
@isnad1 id=other.8h7v.s11.30d7dd30994a from=translated src=- shape=72e266db vocab=e642cb54
-/
theorem scalar_compression_on_hyperbolic_image
    (omega : BilinForm (K := K) (V := V))
    (F E : V →ₗ[K] V) (hFidem : IsIdempotent F)
    (hFself : IsSelfAdjoint omega F) (hEself : IsSelfAdjoint omega E)
    (u v : V) (hFu : F u = u) (hFv : F v = v)
    (huv : omega u v = 1) (halt : ∀ x, omega x x = 0)
    (hspan : ∀ x, F x = x → ∃ a b : K, x = a • u + b • v) :
    let p := omega (E u) v
    F (E u) = p • u ∧ F (E v) = p • v := by
  let T : V →ₗ[K] V := F.comp E
  have hTfixed (x : V) : F (T x) = T x := by
    change F (F (E x)) = F (E x)
    exact idempotent_apply F hFidem (E x)
  have hTself {x y : V} (hx : F x = x) (hy : F y = y) :
      omega (T x) y = omega x (T y) := by
    change omega (F (E x)) y = omega x (F (E y))
    calc
      omega (F (E x)) y = omega (E x) (F y) := hFself (E x) y
      _ = omega (E x) y := by rw [hy]
      _ = omega x (E y) := hEself x y
      _ = omega (F x) (E y) := by rw [hx]
      _ = omega x (F (E y)) := hFself x (E y)
  obtain ⟨a, b, hTu⟩ := hspan (T u) (hTfixed u)
  obtain ⟨c, d, hTv⟩ := hspan (T v) (hTfixed v)
  have hvuu : omega v u = -1 := by
    have hzero := halt (u + v)
    simp only [map_add, LinearMap.add_apply, huv, halt] at hzero
    linear_combination hzero
  have hb : b = 0 := by
    have hs := hTself hFu hFu
    rw [hTu] at hs
    simp only [map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, halt, huv, hvuu] at hs
    linear_combination (-1 / 2 : K) * hs
  have hc : c = 0 := by
    have hs := hTself hFv hFv
    rw [hTv] at hs
    simp only [map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, halt, huv, hvuu] at hs
    linear_combination (1 / 2 : K) * hs
  have had : a = d := by
    have hs := hTself hFu hFv
    rw [hTu, hTv, hb, hc] at hs
    simp only [map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, huv, halt, zero_smul, add_zero,
      zero_add] at hs
    simpa using hs
  have ha : a = omega (E u) v := by
    have hs : omega (T u) v = omega (E u) v := by
      change omega (F (E u)) v = omega (E u) v
      rw [hFself, hFv]
    rw [hTu, hb] at hs
    simpa [huv] using hs
  dsimp only
  constructor
  · change T u = omega (E u) v • u
    simpa [hb, ha] using hTu
  · change T v = omega (E u) v • v
    simpa [hc, ← had, ha] using hTv

/-- Q1's load-bearing actual coordinate statement after the first frame is
literal: for the first projector of `F`, every `E_i`-plane is compressed by
the overlap `p_i`, and hence its two transported columns are `p_i` times the
same image basis.  The weighted form identity is derived as well.
@isnad1 id=ex.6h3v.s13.840252c0dc04 from=translated src=- shape=60805396 vocab=db39fe5f
-/
theorem exists_actual_weighted_first_projector_coordinates
    (E F : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEtrace : ∀ i, jordanTrace (K := K) (E i : Mat6 K) = 1)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (hFidem : ∀ i, (F i : Mat6 K) * F i = F i)
    (hFtrace : ∀ i, jordanTrace (K := K) (F i : Mat6 K) = 1)
    (hFsum : (F 0 : Mat6 K) + F 1 + F 2 = 1) :
    ∃ u v : Vec6 K,
      matrixAction (F 0 : Mat6 K) u = u ∧
      matrixAction (F 0 : Mat6 K) v = v ∧ (omega (K := K)) u v = 1 ∧
      let p : Fin 3 → K := fun i => (omega (K := K)) (matrixAction (E i : Mat6 K) u)
        (matrixAction (E i : Mat6 K) v)
      (∀ i, matrixAction (F 0 : Mat6 K)
          (matrixAction (E i : Mat6 K) u) = p i • u) ∧
      (∀ i, matrixAction (F 0 : Mat6 K)
          (matrixAction (E i : Mat6 K) v) = p i • v) ∧
      (∀ i, (omega (K := K)) (matrixAction (E i : Mat6 K) u)
          (matrixAction (E i : Mat6 K) v) = p i) := by
  obtain ⟨fu, fv, hfyp, hFfu, hFfv, hFspan⟩ :=
    first_projector_image_spanned F hFidem hFtrace hFsum
  have hfu0 : matrixAction (F 0 : Mat6 K) (fu 0) = fu 0 := by
    simpa using hFfu 0 0
  have hfv0 : matrixAction (F 0 : Mat6 K) (fv 0) = fv 0 := by
    simpa using hFfv 0 0
  refine ⟨fu 0, fv 0, hfu0, hfv0, hfyp.pair 0, ?_⟩
  dsimp only
  have himage : ∀ x, matrixAction (F 0 : Mat6 K) x = x →
      ∃ a b : K, x = a • fu 0 + b • fv 0 := hFspan
  have hscalar (i : Fin 3) :=
    scalar_compression_on_hyperbolic_image (omega (K := K))
      (matrixAction (F 0 : Mat6 K)) (matrixAction (E i : Mat6 K))
      (carrier_projector_action_idempotent (F 0) (hFidem 0))
      (carrier_action_selfAdjoint (F 0)) (carrier_action_selfAdjoint (E i))
      (fu 0) (fv 0) hfu0 hfv0
      (hfyp.pair 0) omega_alternating himage
  refine ⟨?_, ?_, fun i => rfl⟩
  · intro i
    have hi := (hscalar i).1
    have hover : (omega (K := K)) (matrixAction (E i : Mat6 K) (fu 0))
        (matrixAction (E i : Mat6 K) (fv 0)) =
        (omega (K := K)) (matrixAction (E i : Mat6 K) (fu 0)) (fv 0) := by
      calc
        _ = (omega (K := K)) (matrixAction (E i : Mat6 K)
              (matrixAction (E i : Mat6 K) (fu 0))) (fv 0) :=
          (carrier_action_selfAdjoint (E i)
            (matrixAction (E i : Mat6 K) (fu 0)) (fv 0)).symm
        _ = _ := by
          rw [idempotent_apply (matrixAction (E i : Mat6 K))
            (carrier_projector_action_idempotent (E i) (hEidem i))]
    simpa only [hover] using hi
  · intro i
    have hi := (hscalar i).2
    have hover : (omega (K := K)) (matrixAction (E i : Mat6 K) (fu 0))
        (matrixAction (E i : Mat6 K) (fv 0)) =
        (omega (K := K)) (matrixAction (E i : Mat6 K) (fu 0)) (fv 0) := by
      calc
        _ = (omega (K := K)) (matrixAction (E i : Mat6 K)
              (matrixAction (E i : Mat6 K) (fu 0))) (fv 0) :=
          (carrier_action_selfAdjoint (E i)
            (matrixAction (E i : Mat6 K) (fu 0)) (fv 0)).symm
        _ = _ := by
          rw [idempotent_apply (matrixAction (E i : Mat6 K))
            (carrier_projector_action_idempotent (E i) (hEidem i))]
    simpa only [hover] using hi

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
