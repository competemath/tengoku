import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticTransvection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms projectPair_pairing_right` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms projectPair_pairing_left` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms projectPairs_pairing_right` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms projectPairs_pairing_left` (it only prints; the queue checks the axioms of every declaration). -/

/-! Explicit projection away from already aligned hyperbolic pairs. -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def projectPair (omega : BilinForm (K := K) (V := V)) (e f c : V) : V :=
  c - (omega e c • f - omega f c • e)

/--
@isnad1 id=eq.2h7v.s10.a70477ce3eab from=translated src=- shape=82c1b313 vocab=6b4f90ca
-/
theorem projectPair_pairing_right
    (omega : BilinForm (K := K) (V := V)) (e f c q : V)
    (heq : omega e q = 0) (hfq : omega f q = 0) :
    omega (projectPair omega e f c) q = omega c q := by
  simp only [projectPair, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, heq, hfq, mul_zero, sub_zero]

/--
@isnad1 id=eq.2h7v.s10.2b1eebdbabae from=translated src=- shape=99d298ff vocab=6b4f90ca
-/
theorem projectPair_pairing_left
    (omega : BilinForm (K := K) (V := V)) (e f c q : V)
    (hqe : omega q e = 0) (hqf : omega q f = 0) :
    omega q (projectPair omega e f c) = omega q c := by
  simp only [projectPair, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hqe, hqf, mul_zero, sub_zero]

def projectPairs (omega : BilinForm (K := K) (V := V)) :
    List (V × V) → V → V
  | [], c => c
  | (e, f) :: pairs, c => projectPairs omega pairs (projectPair omega e f c)

/--
@isnad1 id=eq.1h6v.s10.faeac16ec8bf from=translated src=- shape=e4258253 vocab=953d9a79
-/
theorem projectPairs_pairing_right
    (omega : BilinForm (K := K) (V := V))
    (pairs : List (V × V)) (c q : V)
    (hortho : ∀ pair ∈ pairs, omega pair.1 q = 0 ∧ omega pair.2 q = 0) :
    omega (projectPairs omega pairs c) q = omega c q := by
  induction pairs generalizing c with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨e, f⟩
      rw [projectPairs, ih]
      · exact projectPair_pairing_right omega e f c q
          (hortho (e, f) (by simp)).1 (hortho (e, f) (by simp)).2
      · intro pair hpair
        exact hortho pair (by simp [hpair])

/--
@isnad1 id=eq.1h6v.s10.433d86d35e30 from=translated src=- shape=6aee588c vocab=953d9a79
-/
theorem projectPairs_pairing_left
    (omega : BilinForm (K := K) (V := V))
    (pairs : List (V × V)) (c q : V)
    (hortho : ∀ pair ∈ pairs, omega q pair.1 = 0 ∧ omega q pair.2 = 0) :
    omega q (projectPairs omega pairs c) = omega q c := by
  induction pairs generalizing c with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨e, f⟩
      rw [projectPairs, ih]
      · exact projectPair_pairing_left omega e f c q
          (hortho (e, f) (by simp)).1 (hortho (e, f) (by simp)).2
      · intro pair hpair
        exact hortho pair (by simp [hpair])

end AlbertLean.Generic.SymplecticTransvection
