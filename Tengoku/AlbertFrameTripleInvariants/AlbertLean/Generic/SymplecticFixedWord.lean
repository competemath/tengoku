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

/--
@isnad1 id=eq.0h3v.s6.1f1bc5926e22 from=translated src=- shape=c602b6d2 vocab=41b88771
-/
@[simp] theorem wordMap_nil
    (omega : BilinForm (K := K) (V := V)) :
    wordMap omega [] = LinearMap.id := rfl

/--
@isnad1 id=eq.0h7v.s8.fcdda3c7086e from=translated src=- shape=71ddc9de vocab=bfa7a629
-/
@[simp] theorem wordMap_cons_apply
    (omega : BilinForm (K := K) (V := V)) (d : V) (t : K)
    (word : List (Step (K := K) (V := V))) (x : V) :
    wordMap omega ((d, t) :: word) x = map omega d t (wordMap omega word x) := rfl

/--
@isnad1 id=eq.1h6v.s10.adecaa7bd2a8 from=translated src=- shape=aa2fa419 vocab=466bf795
-/
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

/--
@isnad1 id=eq.1h5v.s9.2e1a0672404f from=translated src=- shape=37307532 vocab=f16e7d64
-/
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

/--
@isnad1 id=eq.0h5v.s7.a3324b3873e5 from=translated src=- shape=800df3a9 vocab=1227ee66
-/
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

/--
@isnad1 id=eq.1h6v.s10.c5b361a9d77d from=translated src=- shape=0ff1f3b0 vocab=59f21c5c
-/
theorem fixedTwelveMap_preserves
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0)
    (schedule : FixedTwelveSchedule (K := K) (V := V)) (x y : V) :
    omega (fixedTwelveMap omega schedule x) (fixedTwelveMap omega schedule y) =
      omega x y :=
  wordMap_preserves omega halt (List.ofFn schedule) x y

/--
@isnad1 id=eq.0h4v.s6.1b566302b809 from=translated src=- shape=2dd0a869 vocab=697f8bb3
-/
theorem map_zero_parameter
    (omega : BilinForm (K := K) (V := V)) (d : V) :
    map omega d 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [map_apply]

/--
@isnad1 id=eq.0h4v.s6.ca3182a271b6 from=translated src=- shape=4e8d1c98 vocab=572e7714
-/
theorem wordMap_zero_parameters
    (omega : BilinForm (K := K) (V := V)) (directions : List V) :
    wordMap omega (directions.map fun d => (d, (0 : K))) = LinearMap.id := by
  induction directions with
  | nil => rfl
  | cons d directions ih =>
      simp only [List.map_cons, wordMap, map_zero_parameter omega d, ih,
        LinearMap.id_comp]

end AlbertLean.Generic.SymplecticTransvection
