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

/--
@isnad1 id=eq.1h4v.s8.1171b37d39ae from=translated src=- shape=d03c3fc5 vocab=6fbf07b5
-/
theorem idempotent_apply (P : V →ₗ[K] V) (hP : IsIdempotent P) (x : V) :
    P (P x) = P x := by
  have h := LinearMap.congr_fun hP x
  exact h

/--
@isnad1 id=eq.1h5v.s8.6beba12c6283 from=translated src=- shape=2afa182d vocab=9d276eca
-/
theorem jordan_orthogonal_apply (P Q : V →ₗ[K] V)
    (hPQ : IsJordanOrthogonal P Q) (x : V) :
    P (Q x) + Q (P x) = 0 := by
  have h := LinearMap.congr_fun hPQ x
  simpa [IsJordanOrthogonal] using h

/-! Associative orthogonality follows from Jordan orthogonality for two
idempotents.  This is the size-independent projector argument. -/
/--
@isnad1 id=eq.3h4v.s8.e5272171bd31 from=translated src=- shape=4c137342 vocab=85d63ea0
-/
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

/--
@isnad1 id=eq.3h4v.s8.a708cdb12c5a from=translated src=- shape=28ac9ded vocab=85d63ea0
-/
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

/--
@isnad1 id=eq.1h6v.s7.5739e6615bac from=translated src=- shape=b82ade43 vocab=50e59b88
-/
theorem normalizedPartner_mem
    (omega : BilinForm (K := K) (V := V)) (P : V →ₗ[K] V)
    (hP : IsIdempotent P) (u y : V) :
    P (normalizedPartner omega P u y) = normalizedPartner omega P u y := by
  simp only [normalizedPartner, map_smul, idempotent_apply P hP y]

/--
@isnad1 id=eq.3h6v.s10.c6234a5e3896 from=translated src=- shape=cacf46bc vocab=c559be31
-/
theorem normalizedPartner_pairs_one
    (omega : BilinForm (K := K) (V := V)) (P : V →ₗ[K] V)
    (hP : IsIdempotent P) (hself : IsSelfAdjoint omega P) (x y : V)
    (hpair : omega (P x) y ≠ 0) :
    omega (P x) (normalizedPartner omega P (P x) y) = 1 := by
  rw [normalizedPartner, map_smul, smul_eq_mul,
    ← hself (P x) y, idempotent_apply P hP]
  exact inv_mul_cancel₀ hpair

/--
@isnad1 id=eq.2h7v.s9.5425eb73ac65 from=translated src=- shape=f6f1b183 vocab=45d9f1f2
-/
theorem different_images_orthogonal
    (omega : BilinForm (K := K) (V := V)) (P Q : V →ₗ[K] V)
    (hself : IsSelfAdjoint omega P) (hcomp : P.comp Q = 0)
    (x y : V) : omega (P x) (Q y) = 0 := by
  rw [hself x (Q y)]
  have h := LinearMap.congr_fun hcomp y
  have hz : P (Q y) = 0 := by simpa using h
  rw [hz, map_zero]

end AlbertLean.Generic.SymplecticProjectorFrame
