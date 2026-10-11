import Tengoku.OpenaiMath.OAI.Computability.RationalHitting.Determinant

namespace OAI

namespace RationalHitting.ExecutableGenerator
open Matrix DeterminantAlgorithm

/-- Dense, staged integer input tables. No quotient-field element is computed. -/
def inputTables (n N e : ℕ) (x : Fin 3 → ℕ) : Vector (Table (Generator.D e)) (n+1) :=
  Vector.ofFn fun a => tabulate (Generator.U n N e x a)

@[simp] lemma inputTables_denote (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) :
    denote ((inputTables n N e x).get a) = Generator.U n N e x a := by
  simp [inputTables]

/-- Cramer's numerators are computed by the staged division-free algorithm. -/
def normalizedEntry {d : ℕ} (A B : Table d) (den : ℤ) (i j : Fin d) : ℚ :=
  Rat.divInt (determinant (tabulate ((denote A).updateCol i (fun r => denote B r j)))) den

lemma normalizedEntry_spec {d : ℕ} (A B : Table d) (hA : (denote A).det ≠ 0) (i j : Fin d) :
    normalizedEntry A B (determinant A) i j =
      (((denote A).map (Int.castRingHom ℚ))⁻¹*(denote B).map (Int.castRingHom ℚ)) i j := by
  rw [normalizedEntry,determinant_eq,denote_tabulate,determinant_eq]
  exact (EncodingBounds.normalized_entry_ratio (denote A) (denote B) hA i j).symm

abbrev RationalTable (n d : ℕ) := Vector (Vector (Vector ℚ d) d) n

def tuple {n d : ℕ} (T : RationalTable n d) : Tuple n d :=
  fun a i j => ((T.get a).get i).get j

def normalized {n d : ℕ} (A : Vector (Table d) (n+1)) (den : ℤ) : RationalTable n d :=
  Vector.ofFn fun a => Vector.ofFn fun i => Vector.ofFn fun j =>
    normalizedEntry (A.get 0) (A.get a.succ) den i j

@[simp] lemma tuple_normalized {n d : ℕ} (A : Vector (Table d) (n+1)) (den : ℤ)
    (a : Fin n) (i j : Fin d) :
    tuple (normalized A den) a i j = normalizedEntry (A.get 0) (A.get a.succ) den i j := by
  simp [tuple,normalized]

/-- The only singularity test; all repeated algebra is materialized in dense tables. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (Generator.D e)) :=
  let A := inputTables n N e x
  let den := determinant (A.get 0)
  if den = 0 then none else some (tuple (normalized A den))

lemma U_det_eq_zero (n N e : ℕ) (x : Fin 3 → ℕ) :
    (Generator.U n N e x 0).det = 0 ↔ (Generator.Z n N e x 0).det = 0 := by
  have he := congrArg Matrix.det (Generator.U_cast n N e x 0)
  rw [Matrix.det_smul] at he
  simp only [Fintype.card_fin] at he
  change ((Generator.U n N e x 0).map (fun z : ℤ => (z : ℚ))).det =
    (CyclotomicRing.dimension e : ℚ)^(Generator.D e) * (Generator.Z n N e x 0).det at he
  have hc : (CyclotomicRing.dimension e : ℚ)^(Generator.D e) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')
  constructor
  · intro h
    have hv : (((Generator.U n N e x 0).det : ℤ) : ℚ) = 0 := by simp [h]
    rw [Int.cast_det,he] at hv
    exact (mul_eq_zero.mp hv).resolve_left hc
  · intro h
    have hv : (((Generator.U n N e x 0).det : ℤ) : ℚ) = 0 := by
      rw [Int.cast_det,he,h,mul_zero]
    exact_mod_cast hv

/-- Exact pointwise equality, including points rejected by the original determinant test. -/
theorem atPoint_spec (n N e : ℕ) (x : Fin 3 → ℕ) :
    atPoint n N e x = Generator.atPoint n N e x := by
  simp only [atPoint,determinant_eq,inputTables_denote,Generator.atPoint]
  by_cases hz : (Generator.Z n N e x 0).det = 0
  · simp [hz,(U_det_eq_zero n N e x).mpr hz]
  · have hu := mt (U_det_eq_zero n N e x).mp hz
    simp only [hz,hu,ite_false,Option.some.injEq]
    funext a i j
    rw [tuple_normalized]
    have hh := normalizedEntry_spec ((inputTables n N e x).get 0)
      ((inputTables n N e x).get a.succ) (by simpa using hu) i j
    simp only [inputTables_denote,determinant_eq] at hh
    rw [hh,Generator.tupleAt_integer n N e x hz a]

/-- A computable generator preserving the list and its order. -/
def output (n N e H : ℕ) : Output n where
  dimension := Generator.D e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (Generator.grid H).filterMap fun x => atPoint n N e (fun i => (x i).val+1)

theorem output_spec (n N e H : ℕ) : output n N e H = Generator.output n N e H := by
  simp only [output,Generator.output,atPoint_spec]

def list (n s : ℕ) : Output n :=
  output n (Parameters.N n s) (Parameters.exponent n s) (Parameters.H n s)

theorem list_spec (n s : ℕ) : list n s = Generator.list n s := output_spec ..

def encoded (n s : ℕ) : List Bool := encodeOutput (list n s)

theorem encoded_spec (n s : ℕ) : encoded n s = encodeOutput (Generator.list n s) := by
  rw [encoded,list_spec]

end RationalHitting.ExecutableGenerator

namespace RationalHitting.ExecutableGenerator

/-- A finite-state implementation with polynomial transition count. -/

def Implementation : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → OutputsWithin G s (C*(n+s+1)^k) (list n s)

end RationalHitting.ExecutableGenerator

/-! Quantitative compilation measured in ordinary TM0 transitions. -/

end OAI
