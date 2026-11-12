import Tengoku.AbelFormalization.AbelFormalization.WeightedNormalization
import Tengoku.Seed.Algebra.Order.Group.PiLex
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual finite-dimensional lexicographic initial forms

The public weight space is `Lex (Fin h → ℤ)`, with the coordinate order on
`Fin h` used by mathlib's `Pi.Lex`. The minimum is taken over the actual finite
monomial support. The head-tail theorem is a proved identity of coefficient
filters, rather than a recursive definition of the lexicographic initial.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*} [CommSemiring R] {h : ℕ}

/-- The minimum actual lexicographic vector weight among supported monomials;
the zero polynomial is assigned the zero vector.-/
def lexicographicMinimumWeight (ω : ι → Fin h → ℤ) (f : MvPolynomial ι R) :
    Lex (Fin h → ℤ) := by
  classical
  exact if hs : f.support.Nonempty then
    f.support.inf' hs (Finsupp.weight (fun i => toLex (ω i))) else 0

/--
@isnad1 id=eq.0h4v.s6.7eb0a6dbb4c8 from=translated src=- shape=c516e4ac vocab=8a939c1f
-/
@[simp]
theorem lexicographicMinimumWeight_zero (ω : ι → Fin h → ℤ) :
    lexicographicMinimumWeight ω (0 : MvPolynomial ι R) = 0 := by
  simp [lexicographicMinimumWeight]

/--
@isnad1 id=le.1h6v.s8.88695303e71e from=translated src=- shape=37cd8bb7 vocab=9234eeaa
-/
theorem lexicographicMinimumWeight_le (ω : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) {d : ι →₀ ℕ} (hd : d ∈ f.support) :
    lexicographicMinimumWeight ω f ≤ Finsupp.weight (fun i => toLex (ω i)) d := by
  classical
  have hs : f.support.Nonempty := ⟨d, hd⟩
  simp only [lexicographicMinimumWeight, dite_eq_left hs]
  exact Finset.inf'_le _ hd

/--
@isnad1 id=ex.1h5v.s8.a794e9dff165 from=translated src=- shape=ba814759 vocab=0067af92
-/
theorem exists_support_lexicographicWeight_eq_minimum (ω : ι → Fin h → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ d ∈ f.support,
      Finsupp.weight (fun i => toLex (ω i)) d = lexicographicMinimumWeight ω f := by
  classical
  have hs : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
  obtain ⟨d, hd, hle⟩ :=
    (Finset.inf'_le_iff hs (f := Finsupp.weight (fun i => toLex (ω i)))).mp le_rfl
  refine ⟨d, hd, le_antisymm ?_ (lexicographicMinimumWeight_le ω f hd)⟩
  simpa only [lexicographicMinimumWeight, dite_eq_left hs] using hle

/-- The actual least-vector-weight component, defined using mathlib's
multivariate polynomial component operator over the lexicographic group.-/
def lexicographicInitialForm (ω : ι → Fin h → ℤ) (f : MvPolynomial ι R) :
    MvPolynomial ι R :=
  MvPolynomial.weightedHomogeneousComponent (fun i => toLex (ω i))
    (lexicographicMinimumWeight ω f) f

/--
@isnad1 id=eq.0h6v.s9.c938dd1da814 from=translated src=- shape=d0cb19a9 vocab=ce44915b
-/
theorem lexicographicInitialForm_coeff (ω : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) (d : ι →₀ ℕ) :
    (lexicographicInitialForm ω f).coeff d =
      if Finsupp.weight (fun i => toLex (ω i)) d = lexicographicMinimumWeight ω f
      then f.coeff d else 0 := by
  classical
  exact MvPolynomial.coeff_weightedHomogeneousComponent _ _ _

/--
@isnad1 id=eq.0h5v.s9.fe1aafa6c5c8 from=translated src=- shape=d7659b11 vocab=8e4d7409
-/
theorem lexicographicInitialForm_support (ω : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) :
    (lexicographicInitialForm ω f).support =
      f.support.filter (fun d =>
        Finsupp.weight (fun i => toLex (ω i)) d = lexicographicMinimumWeight ω f) := by
  classical
  exact MvPolynomial.support_weightedHomogeneousComponent _ _

/--
@isnad1 id=eq.0h4v.s6.193ff3957279 from=translated src=- shape=bc1340e3 vocab=99ceb11c
-/
@[simp]
theorem lexicographicInitialForm_zero (ω : ι → Fin h → ℤ) :
    lexicographicInitialForm ω (0 : MvPolynomial ι R) = 0 := by
  simp [lexicographicInitialForm]

/-- With no weight coordinates, all monomials have the same weight and the
initial form leaves the polynomial unchanged.
@isnad1 id=eq.0h4v.s5.c32e8818b147 from=translated src=- shape=280b4ba7 vocab=8f1d7f51
-/
@[simp]
theorem lexicographicInitialForm_zero_dim (ω : ι → Fin 0 → ℤ)
    (f : MvPolynomial ι R) : lexicographicInitialForm ω f = f := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [lexicographicInitialForm_coeff]
  exact ite_eq_left (Subsingleton.elim _ _)

/-- The actual `Fin`-indexed lexicographic order first compares the new head
coordinate, and compares the tails precisely when the heads agree.
@isnad1 id=iff.0h5v.s9.bcdfe1ef48ae from=translated src=- shape=a925b3a2 vocab=2fbc6c2d
-/
theorem finLex_cons_lt_iff (a b : ℤ) (u v : Fin h → ℤ) :
    toLex (Fin.cons a u : Fin (h + 1) → ℤ) <
      toLex (Fin.cons b v : Fin (h + 1) → ℤ) ↔
      a < b ∨ a = b ∧ toLex u < toLex v := by
  constructor
  · rintro ⟨j, hbefore, hlt⟩
    cases j using Fin.cases with
    | zero => exact Or.inl (by simpa only [Pi.toLex_apply, Fin.cons_zero] using hlt)
    | succ j =>
        right
        refine ⟨?_, j, ?_, ?_⟩
        · simpa only [Pi.toLex_apply, Fin.cons_zero] using hbefore 0 (Fin.succ_pos j)
        · intro k hk
          simpa only [Pi.toLex_apply, Fin.cons_succ] using
            hbefore k.succ (Fin.succ_lt_succ_iff.mpr hk)
        · simpa only [Pi.toLex_apply, Fin.cons_succ] using hlt
  · rintro (hab | ⟨hab, j, hbefore, hlt⟩)
    · refine ⟨0, ?_, ?_⟩
      · intro k hk
        exact (Fin.not_lt_zero k hk).elim
      · simpa only [Pi.toLex_apply, Fin.cons_zero] using hab
    · refine ⟨j.succ, ?_, ?_⟩
      · intro k hk
        cases k using Fin.cases with
        | zero => simpa only [Pi.toLex_apply, Fin.cons_zero] using hab
        | succ k =>
            simpa only [Pi.toLex_apply, Fin.cons_succ] using
              hbefore k (Fin.succ_lt_succ_iff.mp hk)
      · simpa only [Pi.toLex_apply, Fin.cons_succ] using hlt

/-- Evaluation of a lexicographic weight at one coordinate is an additive
homomorphism; this statement does not assert that it preserves lex order.-/
def lexicographicCoordinate (j : Fin h) : Lex (Fin h → ℤ) →+ ℤ where
  toFun x := ofLex x j
  map_zero' := rfl
  map_add' _ _ := rfl

/--
@isnad1 id=eq.0h5v.s8.835e3a4a1801 from=translated src=- shape=a2f93a64 vocab=3bcac22d
-/
theorem lexicographicWeight_apply (ω : ι → Fin h → ℤ)
    (d : ι →₀ ℕ) (j : Fin h) :
    ofLex (Finsupp.weight (fun i => toLex (ω i)) d) j =
      Finsupp.weight (fun i => ω i j) d := by
  change lexicographicCoordinate j (Finsupp.weight (fun i => toLex (ω i)) d) = _
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]
  rfl

/-- Computing a vector monomial weight commutes with splitting its head and
tail coordinates.
@isnad1 id=eq.0h5v.s10.2ec7dc49c8fc from=translated src=- shape=14b757b1 vocab=1ace09ec
-/
theorem lexicographicWeight_cons (ω : ι → ℤ) (ν : ι → Fin h → ℤ)
    (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => toLex (Fin.cons (ω i) (ν i))) d =
      toLex (Fin.cons (Finsupp.weight ω d)
        (ofLex (Finsupp.weight (fun i => toLex (ν i)) d)) : Fin (h + 1) → ℤ) := by
  apply ofLex.injective
  funext j
  rw [lexicographicWeight_apply, ofLex_toLex]
  cases j using Fin.cases with
  | zero => simp only [Fin.cons_zero]
  | succ j => simp only [Fin.cons_succ, lexicographicWeight_apply]

end AbelFormalization
