import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms DetOneMatrix.det_gInv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms moment_act` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms delta_act` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deltaStar_act` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms related_preserves_invariants` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Explicit determinant-one action on residual matrix pairs

This module defines a neutral action on a pair of `4 x 4` matrices.  The
vector-coordinate matrix transforms on the left by `g`, and the
covector-coordinate matrix transforms on the right by a specified two-sided
inverse of `g`:

`X |-> g * X`, `A |-> A * gInv`.

The product `M = A * X` and both determinant coordinates are invariant when
`det g = 1`.  This is only an explicit matrix action.  It is not identified
with `Spin(6)`, an invariant-theory quotient, or a deck action.
-/

namespace AlbertLean.Residual.SL4PairAction

open Matrix

universe u

variable {K : Type u} [Field K]

/-- the neutral `4 x 4` matrix carrier
used for the frozen residual row/column convention.-/
abbrev Mat4 (K : Type u) [Field K] := Matrix (Fin 4) (Fin 4) K

/-- a covector-row matrix `A` together
with a vector-column matrix `X`.-/
@[ext]
structure ResidualPair (K : Type u) [Field K] where
  A : Mat4 K
  X : Mat4 K

/-- the pairing matrix `M = A * X`.-/
def moment (P : ResidualPair K) : Mat4 K :=
  P.A * P.X

/-- the determinant of the vector-column
matrix.-/
def delta (P : ResidualPair K) : K :=
  Matrix.det P.X

/-- the determinant of the
covector-row matrix.-/
def deltaStar (P : ResidualPair K) : K :=
  Matrix.det P.A

/-- an audited determinant-one matrix
together with a specified two-sided inverse.-/
@[ext]
structure DetOneMatrix (K : Type u) [Field K] where
  g : Mat4 K
  gInv : Mat4 K
  g_mul_gInv : g * gInv = 1
  gInv_mul_g : gInv * g = 1
  det_g : Matrix.det g = 1

/-- the specified inverse of a
determinant-one matrix also has determinant one.
@isnad1 id=eq.0h2v.s5.583db924c9f1 from=translated src=- shape=46d9f30e vocab=df69f5e7
-/
theorem DetOneMatrix.det_gInv (G : DetOneMatrix K) :
    Matrix.det G.gInv = 1 := by
  calc
    Matrix.det G.gInv = Matrix.det G.gInv * Matrix.det G.g := by
      rw [G.det_g, mul_one]
    _ = Matrix.det (G.gInv * G.g) := by rw [Matrix.det_mul]
    _ = 1 := by rw [G.gInv_mul_g, Matrix.det_one]

/-- the frozen action
`X |-> gX`, `A |-> A gInv`.-/
def act (G : DetOneMatrix K) (P : ResidualPair K) : ResidualPair K where
  A := P.A * G.gInv
  X := G.g * P.X

/-- the covector-row projection
of the explicit action.
@isnad1 id=eq.0h3v.s6.d82417153657 from=translated src=- shape=db10997c vocab=58a085af
-/
@[simp] theorem act_A (G : DetOneMatrix K) (P : ResidualPair K) :
    (act G P).A = P.A * G.gInv := rfl

/-- the vector-column
projection of the explicit action.
@isnad1 id=eq.0h3v.s6.fd9b68010f3e from=translated src=- shape=e7f5674a vocab=ea72dd31
-/
@[simp] theorem act_X (G : DetOneMatrix K) (P : ResidualPair K) :
    (act G P).X = G.g * P.X := rfl

/-- the pairing matrix is fixed by the
explicit determinant-one action.
@isnad1 id=eq.0h3v.s4.329b7182c5a2 from=translated src=- shape=12de1466 vocab=d61f1704
-/
@[simp] theorem moment_act (G : DetOneMatrix K) (P : ResidualPair K) :
    moment (act G P) = moment P := by
  calc
    (P.A * G.gInv) * (G.g * P.X) =
        P.A * (G.gInv * G.g) * P.X := by
      simp only [Matrix.mul_assoc]
    _ = P.A * P.X := by rw [G.gInv_mul_g, Matrix.mul_one]

/-- `Delta = det X` is fixed by the
explicit determinant-one action.
@isnad1 id=eq.0h3v.s4.661456771b2c from=translated src=- shape=15709cb3 vocab=6c10f88c
-/
@[simp] theorem delta_act (G : DetOneMatrix K) (P : ResidualPair K) :
    delta (act G P) = delta P := by
  simp [delta, Matrix.det_mul, G.det_g]

/-- `DeltaStar = det A` is fixed by the
explicit determinant-one action.
@isnad1 id=eq.0h3v.s4.47a4c099de7d from=translated src=- shape=15709cb3 vocab=f4720696
-/
@[simp] theorem deltaStar_act (G : DetOneMatrix K) (P : ResidualPair K) :
    deltaStar (act G P) = deltaStar P := by
  simp [deltaStar, Matrix.det_mul, G.det_gInv]

/-- two residual pairs are explicitly
related when one is obtained from the other by the declared action.-/
def Related (P Q : ResidualPair K) : Prop :=
  ∃ G : DetOneMatrix K, act G P = Q

/-- explicit relatedness preserves the
pairing matrix and both determinant coordinates.
@isnad1 id=and.1h3v.s5.62578e6d1446 from=translated src=- shape=42fcfc6c vocab=034cec39
-/
theorem related_preserves_invariants {P Q : ResidualPair K}
    (h : Related P Q) :
    moment P = moment Q ∧ delta P = delta Q ∧ deltaStar P = deltaStar Q := by
  rcases h with ⟨G, rfl⟩
  simp

end AlbertLean.Residual.SL4PairAction
