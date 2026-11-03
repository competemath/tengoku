import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSelfAdjointCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms decode_encode` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms encode_decode` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms linearEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms linearEquiv_jordan` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms decode_coordinateJordan` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms decode_injective` (it only prints; the queue checks the axioms of every declaration). -/

/-! Literal `9+3+3` coordinates for the symplectic-selfadjoint carrier. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.CarrierCoordinates

open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev Index := (Fin 3 × Fin 3) ⊕ (Fin 3 ⊕ Fin 3)
abbrev Coordinates (K : Type u) := Index → K

def encode (P : Carrier K) : Coordinates K
  | Sum.inl (i, j) => topLeft P i j
  | Sum.inr (Sum.inl i) => unhat (topRight P) i
  | Sum.inr (Sum.inr i) => unhat (bottomLeft P) i

def decode (x : Coordinates K) : Carrier K :=
  ⟨grouped
      (fun i j => x (Sum.inl (i, j)))
      (fun i => x (Sum.inr (Sum.inl i)))
      (fun i => x (Sum.inr (Sum.inr i))),
    grouped_symplectic_selfadjoint _ _ _⟩

private theorem unhat_add (A B : Mat3 K) :
    unhat (A + B) = unhat A + unhat B := by
  funext i
  fin_cases i <;> simp [unhat, add_comm]

private theorem unhat_smul (a : K) (A : Mat3 K) :
    unhat (a • A) = a • unhat A := by
  funext i
  fin_cases i <;> simp [unhat, smul_eq_mul]

def encodeLinear : Carrier K →ₗ[K] Coordinates K where
  toFun := encode
  map_add' P Q := by
    funext i
    rcases i with ⟨i, j⟩ | i
    · rfl
    · rcases i with i | i
      · change unhat (topRight ((P + Q : Carrier K) : Mat6 K)) i =
          unhat (topRight (P : Mat6 K)) i + unhat (topRight (Q : Mat6 K)) i
        have hblock : topRight ((P + Q : Carrier K) : Mat6 K) =
            topRight (P : Mat6 K) + topRight (Q : Mat6 K) := rfl
        rw [hblock, unhat_add]
        rfl
      · change unhat (bottomLeft ((P + Q : Carrier K) : Mat6 K)) i =
          unhat (bottomLeft (P : Mat6 K)) i + unhat (bottomLeft (Q : Mat6 K)) i
        have hblock : bottomLeft ((P + Q : Carrier K) : Mat6 K) =
            bottomLeft (P : Mat6 K) + bottomLeft (Q : Mat6 K) := rfl
        rw [hblock, unhat_add]
        rfl
  map_smul' a P := by
    funext i
    rcases i with ⟨i, j⟩ | i
    · rfl
    · rcases i with i | i
      · change unhat (topRight ((a • P : Carrier K) : Mat6 K)) i =
          a * unhat (topRight (P : Mat6 K)) i
        have hblock : topRight ((a • P : Carrier K) : Mat6 K) =
            a • topRight (P : Mat6 K) := rfl
        rw [hblock, unhat_smul]
        rfl
      · change unhat (bottomLeft ((a • P : Carrier K) : Mat6 K)) i =
          a * unhat (bottomLeft (P : Mat6 K)) i
        have hblock : bottomLeft ((a • P : Carrier K) : Mat6 K) =
            a • bottomLeft (P : Mat6 K) := rfl
        rw [hblock, unhat_smul]
        rfl

theorem decode_encode (P : Carrier K) : decode (encode P) = P := by
  apply Subtype.ext
  exact grouped_extract (P : Mat6 K) (carrier_property P)

theorem encode_decode (x : Coordinates K) : encode (decode x) = x := by
  funext i
  rcases i with ⟨i, j⟩ | i
  · rfl
  · rcases i with i | i
    · change unhat (hat (fun k => x (Sum.inr (Sum.inl k)))) i =
        x (Sum.inr (Sum.inl i))
      exact congrFun (unhat_hat (fun k => x (Sum.inr (Sum.inl k)))) i
    · change unhat (hat (fun k => x (Sum.inr (Sum.inr k)))) i =
        x (Sum.inr (Sum.inr i))
      exact congrFun (unhat_hat (fun k => x (Sum.inr (Sum.inr k)))) i

/-- The actual carrier is linearly equivalent to its literal fifteen scalar
coordinates.  No finite-rank or dimension theorem is used.-/
def linearEquiv : Carrier K ≃ₗ[K] Coordinates K where
  toLinearMap := encodeLinear
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-- Linearity of decoding follows from the actual inverse laws.-/
def decodeLinear : Coordinates K →ₗ[K] Carrier K :=
  linearEquiv.symm.toLinearMap

/-- The literal coordinate product is the transport of the actual carrier
Jordan product through the displayed inverse coordinate laws.-/
def coordinateJordan (x y : Coordinates K) : Coordinates K :=
  encode (jordan (decode x) (decode y))

theorem linearEquiv_jordan (P Q : Carrier K) :
    linearEquiv (jordan P Q) = coordinateJordan (linearEquiv P) (linearEquiv Q) := by
  change encode (jordan P Q) =
    encode (jordan (decode (encode P)) (decode (encode Q)))
  rw [decode_encode, decode_encode]

theorem decode_coordinateJordan (x y : Coordinates K) :
    decode (coordinateJordan x y) = jordan (decode x) (decode y) := by
  exact decode_encode _

/-- Uniqueness of grouped coordinates, exposed at the carrier level.-/
theorem decode_injective : Function.Injective (decode (K := K)) := by
  intro x y h
  have hg : grouped
      (fun i j => x (Sum.inl (i, j)))
      (fun i => x (Sum.inr (Sum.inl i)))
      (fun i => x (Sum.inr (Sum.inr i))) =
      grouped
      (fun i j => y (Sum.inl (i, j)))
      (fun i => y (Sum.inr (Sum.inl i)))
      (fun i => y (Sum.inr (Sum.inr i))) := congrArg Subtype.val h
  obtain ⟨ha, hu, hv⟩ := grouped_injective hg
  funext i
  rcases i with ⟨i, j⟩ | i
  · exact congrFun (congrFun ha i) j
  · rcases i with i | i
    · exact congrFun hu i
    · exact congrFun hv i

end AlbertLean.Generic.QuaternionRow.CarrierCoordinates
