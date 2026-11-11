import Tengoku.LeanCharacteristicSet.CharacteristicSet.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Main degree of a polynomial

This file defines the *main degree* of a multivariate polynomial,
which is the degree with respect to its main variable.

## Main definitions

* `MvPolynomial.mainDegree p`:
  The degree of `p` with respect to its main variable.
  If `max_vars p = ⊥` (i.e., `p` is a constant or zero), the degree is `0`.

## Main theorems

* `mainDegree_eq_zero_iff`: `p.mainDegree = 0` iff `p.max_vars = ⊥`
* `mainDegree_of_max_vars_isSome`: When `p.max_vars = c ≠ ⊥`,
  `p.mainDegree = p.degreeOf c`

-/

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {p q : MvPolynomial σ R}

section MainDegree

variable [LinearOrder σ] {i j c : σ}

/-- The "main degree" of `p`: the degree of `p` with respect to its main variable.
If `max_vars p = ⊥` (i.e., `p` is a constant or zero), the degree is 0.-/
noncomputable def mainDegree (p : MvPolynomial σ R) : ℕ :=
  match p.vars.max with
  | ⊥ => 0
  | some c => p.degreeOf c

/--
@isnad1 id=eq.1h4v.s5.70445a231397 from=translated src=- shape=26d4553b vocab=26580a74
-/
theorem mainDegree_of_max_vars_isSome : p.vars.max = c → p.mainDegree = p.degreeOf c :=
  fun h ↦ by rw [mainDegree, h]

/--
@isnad1 id=eq.1h4v.s6.5dcba829ba3c from=translated src=- shape=b3a814e5 vocab=eccef867
-/
theorem mainDegree_of_max_vars_isSome' :
    p.vars.max = c → p.mainDegree = p.support.sup (fun s ↦ s c) :=
  fun h ↦ by rw [mainDegree_of_max_vars_isSome h, degreeOf_eq_sup]

/--
@isnad1 id=iff.0h3v.s5.cc0214340cc2 from=translated src=- shape=64367d12 vocab=05704ee2
-/
theorem mainDegree_eq_zero_iff : p.mainDegree = 0 ↔ p.vars.max = ⊥ where
  mp h :=
    match hc : p.vars.max with
    | ⊥ => rfl
    | some c => by
      rw [mainDegree_of_max_vars_isSome hc, degreeOf] at h
      have : c ∉ p.degrees := by simpa only [Multiset.count_eq_zero] using h
      have hc := Finset.mem_of_max hc
      simp only [vars_def, Multiset.mem_toFinset] at hc
      exact absurd hc this
  mpr h := by rw [mainDegree, h]

/--
@isnad1 id=ne.1h4v.s5.940ebe2566f4 from=translated src=- shape=0fe20488 vocab=d81400fd
-/
theorem degreeOf_max_vars_ne_zero : p.vars.max = c → p.degreeOf c ≠ 0 := fun h ↦
  have := (not_iff_not.mpr mainDegree_eq_zero_iff).mpr (h ▸ WithBot.coe_ne_bot)
  mainDegree_of_max_vars_isSome h ▸ this

/--
@isnad1 id=mem.1h4v.s5.a5c8ce5b6770 from=translated src=- shape=35aeeb4f vocab=5d099a6c
-/
theorem max_vars_mem_degrees : p.vars.max = c → c ∈ p.degrees := fun h ↦
  have := degreeOf_max_vars_ne_zero h; Multiset.count_ne_zero.mp (degreeOf_def c p ▸ this)

/--
@isnad1 id=eq.0h2v.s5.d871dcc59ad3 from=translated src=- shape=0bff1b8b vocab=ce0e3e7e
-/
@[simp] theorem mainDegree_zero : (0 : MvPolynomial σ R).mainDegree = 0 := rfl

/--
@isnad1 id=eq.2h5v.s7.6e2882bbbfad from=translated src=- shape=2958370f vocab=750a16ec
-/
@[simp] theorem mainDegree_monomial {s : σ →₀ ℕ} {r : R} (hr : r ≠ 0)
    (hs : s.support.max = c) : (monomial s r).mainDegree = s c := by
  rw [mainDegree_of_max_vars_isSome <| (congrArg _ (vars_monomial hr)).trans hs]
  exact degreeOf_monomial_eq s c hr

/--
@isnad1 id=eq.0h3v.s6.db33af73bc3e from=translated src=- shape=a5c725d0 vocab=ab1183d4
-/
@[simp] theorem mainDegree_C (r : R) : (C r : MvPolynomial σ R).mainDegree = 0 :=
  mainDegree_eq_zero_iff.mpr <| congrArg _ (vars_C)

/--
@isnad1 id=eq.0h4v.s6.b610bb5558fc from=translated src=- shape=cf6ea1d5 vocab=dd09c530
-/
@[simp] theorem mainDegree_X_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : MvPolynomial σ R) ^ k).mainDegree = k := by
  by_cases hk : k = 0
  · exact hk ▸ pow_zero (X i : MvPolynomial σ R) ▸ mainDegree_C 1
  have : (Finsupp.single i k).support.max = i := by rw [Finsupp.support_single i hk]; rfl
  rw [X_pow_eq_monomial, mainDegree_monomial one_ne_zero this, Finsupp.single_eq_same]

/--
@isnad1 id=eq.0h3v.s5.d8ef49048094 from=translated src=- shape=e45d4cce vocab=04ceb2d3
-/
@[simp] theorem mainDegree_X [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).mainDegree = 1 :=
  pow_one (X i : MvPolynomial σ R) ▸ mainDegree_X_pow i 1

end MainDegree
end MvPolynomial
