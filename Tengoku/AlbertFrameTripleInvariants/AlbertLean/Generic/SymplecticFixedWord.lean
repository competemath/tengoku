import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticTransvection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms wordMap_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wordMap_fixes_of_centers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wordMap_append` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedTwelveMap_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wordMap_zero_parameters` (it only prints; the queue checks the axioms of every declaration). -/

/-! Polynomial words in symplectic transvections, including the literal
twelve-slot schedule used for dimension-six frame coverage. -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

abbrev Step := V × K

def wordMap (omega : BilinForm (K := K) (V := V)) :
    List (Step (K := K) (V := V)) → V →ₗ[K] V
  | [] => LinearMap.id
  | (d, t) :: word => (map omega d t).comp (wordMap omega word)

@[simp] theorem wordMap_nil
    (omega : BilinForm (K := K) (V := V)) :
    wordMap omega [] = LinearMap.id := rfl

@[simp] theorem wordMap_cons_apply
    (omega : BilinForm (K := K) (V := V)) (d : V) (t : K)
    (word : List (Step (K := K) (V := V))) (x : V) :
    wordMap omega ((d, t) :: word) x = map omega d t (wordMap omega word x) := rfl

theorem wordMap_preserves
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0)
    (word : List (Step (K := K) (V := V))) (x y : V) :
    omega (wordMap omega word x) (wordMap omega word y) = omega x y := by
  induction word with
  | nil => rfl
  | cons step word ih =>
      rcases step with ⟨d, t⟩
      rw [wordMap_cons_apply, wordMap_cons_apply,
        map_preserves omega halt d t, ih]

theorem wordMap_fixes_of_centers
    (omega : BilinForm (K := K) (V := V))
    (word : List (Step (K := K) (V := V))) (q : V)
    (hfix : ∀ step ∈ word, omega step.1 q = 0) :
    wordMap omega word q = q := by
  induction word with
  | nil => rfl
  | cons step word ih =>
      rcases step with ⟨d, t⟩
      rw [wordMap_cons_apply, ih]
      · simp only [map_apply, hfix (d, t) (by simp), mul_zero, zero_smul, add_zero]
      · intro step hstep
        exact hfix step (by simp [hstep])

theorem wordMap_append
    (omega : BilinForm (K := K) (V := V))
    (left right : List (Step (K := K) (V := V))) :
    wordMap omega (left ++ right) =
      (wordMap omega left).comp (wordMap omega right) := by
  induction left with
  | nil => simp [wordMap]
  | cons step left ih =>
      rcases step with ⟨d, t⟩
      simp only [List.cons_append, wordMap, ih, LinearMap.comp_assoc]

def inverseWord (word : List (Step (K := K) (V := V))) :
    List (Step (K := K) (V := V)) :=
  word.reverse.map fun step => (step.1, -step.2)

def FixedTwelveSchedule := Fin 12 → Step (K := K) (V := V)

def fixedTwelveMap
    (omega : BilinForm (K := K) (V := V))
    (schedule : FixedTwelveSchedule (K := K) (V := V)) : V →ₗ[K] V :=
  wordMap omega (List.ofFn schedule)

theorem fixedTwelveMap_preserves
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0)
    (schedule : FixedTwelveSchedule (K := K) (V := V)) (x y : V) :
    omega (fixedTwelveMap omega schedule x) (fixedTwelveMap omega schedule y) =
      omega x y :=
  wordMap_preserves omega halt (List.ofFn schedule) x y

theorem map_zero_parameter
    (omega : BilinForm (K := K) (V := V)) (d : V) :
    map omega d 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [map_apply]

theorem wordMap_zero_parameters
    (omega : BilinForm (K := K) (V := V)) (directions : List V) :
    wordMap omega (directions.map fun d => (d, (0 : K))) = LinearMap.id := by
  induction directions with
  | nil => rfl
  | cons d directions ih =>
      simp only [List.map_cons, wordMap, map_zero_parameter omega d, ih,
        LinearMap.id_comp]

end AlbertLean.Generic.SymplecticTransvection
