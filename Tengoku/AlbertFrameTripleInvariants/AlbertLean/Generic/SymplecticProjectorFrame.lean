import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticTransvection
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms comp_eq_zero_of_jordan_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reverse_comp_eq_zero_of_jordan_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalizedPartner_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalizedPartner_pairs_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms different_images_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/

/-! Root-free extraction of hyperbolic pairs from self-adjoint projectors.
The arguments are pointwise and use neither rank nor trace. -/

noncomputable section
namespace AlbertLean.Generic.SymplecticProjectorFrame

open SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def IsIdempotent (P : V →ₗ[K] V) : Prop := P.comp P = P

def IsSelfAdjoint (omega : BilinForm (K := K) (V := V))
    (P : V →ₗ[K] V) : Prop :=
  ∀ x y, omega (P x) y = omega x (P y)

def IsJordanOrthogonal (P Q : V →ₗ[K] V) : Prop :=
  P.comp Q + Q.comp P = 0

theorem idempotent_apply (P : V →ₗ[K] V) (hP : IsIdempotent P) (x : V) :
    P (P x) = P x := by
  have h := LinearMap.congr_fun hP x
  exact h

theorem jordan_orthogonal_apply (P Q : V →ₗ[K] V)
    (hPQ : IsJordanOrthogonal P Q) (x : V) :
    P (Q x) + Q (P x) = 0 := by
  have h := LinearMap.congr_fun hPQ x
  simpa [IsJordanOrthogonal] using h

/-! Associative orthogonality follows from Jordan orthogonality for two
idempotents.  This is the size-independent projector argument. -/
theorem comp_eq_zero_of_jordan_orthogonal
    (P Q : V →ₗ[K] V) (hP : IsIdempotent P) (hQ : IsIdempotent Q)
    (hPQ : IsJordanOrthogonal P Q) : P.comp Q = 0 := by
  apply LinearMap.ext
  intro x
  have h0 := jordan_orthogonal_apply P Q hPQ x
  have hleft := congrArg P h0
  have hright := jordan_orthogonal_apply P Q hPQ (P x)
  simp only [map_add, map_zero, idempotent_apply P hP] at hleft hright
  have hpqp : P (Q (P x)) = -P (Q x) := by
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hleft)
  have hqp : Q (P x) = -P (Q (P x)) := by
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hright)
  have heq : Q (P x) = P (Q x) := by rw [hqp, hpqp, neg_neg]
  change P (Q x) = 0
  rw [heq] at h0
  have htwo : (2 : K) • P (Q x) = 0 := by
    simpa [two_smul K] using h0
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem reverse_comp_eq_zero_of_jordan_orthogonal
    (P Q : V →ₗ[K] V) (hP : IsIdempotent P) (hQ : IsIdempotent Q)
    (hPQ : IsJordanOrthogonal P Q) : Q.comp P = 0 := by
  have hsym : IsJordanOrthogonal Q P := by
    unfold IsJordanOrthogonal at hPQ ⊢
    simpa [add_comm] using hPQ
  exact comp_eq_zero_of_jordan_orthogonal Q P hQ hP hsym

def normalizedPartner
    (omega : BilinForm (K := K) (V := V)) (P : V →ₗ[K] V)
    (u y : V) : V := (omega u y)⁻¹ • P y

theorem normalizedPartner_mem
    (omega : BilinForm (K := K) (V := V)) (P : V →ₗ[K] V)
    (hP : IsIdempotent P) (u y : V) :
    P (normalizedPartner omega P u y) = normalizedPartner omega P u y := by
  simp only [normalizedPartner, map_smul, idempotent_apply P hP y]

theorem normalizedPartner_pairs_one
    (omega : BilinForm (K := K) (V := V)) (P : V →ₗ[K] V)
    (hP : IsIdempotent P) (hself : IsSelfAdjoint omega P) (x y : V)
    (hpair : omega (P x) y ≠ 0) :
    omega (P x) (normalizedPartner omega P (P x) y) = 1 := by
  rw [normalizedPartner, map_smul, smul_eq_mul,
    ← hself (P x) y, idempotent_apply P hP]
  exact inv_mul_cancel₀ hpair

theorem different_images_orthogonal
    (omega : BilinForm (K := K) (V := V)) (P Q : V →ₗ[K] V)
    (hself : IsSelfAdjoint omega P) (hcomp : P.comp Q = 0)
    (x y : V) : omega (P x) (Q y) = 0 := by
  rw [hself x (Q y)]
  have h := LinearMap.congr_fun hcomp y
  have hz : P (Q y) = 0 := by simpa using h
  rw [hz, map_zero]

end AlbertLean.Generic.SymplecticProjectorFrame
