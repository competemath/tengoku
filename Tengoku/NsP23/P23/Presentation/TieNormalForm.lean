import Tengoku.NsP23.P23.Presentation.PolynomialTie
import Tengoku.Seed.Algebra.Polynomial.Degree.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Monic x-normal forms for the one-tie polynomial

The implementation transports the public three-variable polynomial to a
univariate polynomial in x over the two-variable y/z coefficient ring.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie
open scoped BigOperators

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- The two-variable coefficient ring used only by the internal proof engine.-/
abbrev YZPoly (k : Type*) [Field k] := MvPolynomial (Fin 2) k

/-- The public-to-iterated polynomial algebra equivalence.-/
def threePolyEquivIterated :
    ThreePoly k ≃ₐ[k] Polynomial (YZPoly k) :=
  MvPolynomial.finSuccEquiv k 2

/-- The y variable in the internal coefficient ring.-/
def yzY : YZPoly k := MvPolynomial.X 0

/-- The z variable in the internal coefficient ring.-/
def yzZ : YZPoly k := MvPolynomial.X 1

/-- The monic internal form of the unique tie.-/
def iteratedTiePolynomial (a b c : ℕ) : Polynomial (YZPoly k) :=
  Polynomial.X ^ a - Polynomial.C (yzY ^ b * yzZ ^ c)

@[simp] theorem threePolyEquivIterated_polyX :
    threePolyEquivIterated (k := k) polyX = Polynomial.X := by
  exact MvPolynomial.finSuccEquiv_X_zero

@[simp] theorem threePolyEquivIterated_polyY :
    threePolyEquivIterated (k := k) polyY = Polynomial.C yzY := by
  simpa [threePolyEquivIterated, polyY, yzY] using
    (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 2) (j := (0 : Fin 2)))

@[simp] theorem threePolyEquivIterated_polyZ :
    threePolyEquivIterated (k := k) polyZ = Polynomial.C yzZ := by
  simpa [threePolyEquivIterated, polyZ, yzZ] using
    (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 2) (j := (1 : Fin 2)))

@[simp] theorem threePolyEquivIterated_tiePolynomial :
    threePolyEquivIterated (k := k) (tiePolynomial (k := k) a b c) =
      iteratedTiePolynomial (k := k) a b c := by
  simp [tiePolynomial, iteratedTiePolynomial]

theorem iteratedTiePolynomial_monic :
    (iteratedTiePolynomial (k := k) a b c).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (NeZero.ne a)

@[simp] theorem iteratedTiePolynomial_natDegree :
    (iteratedTiePolynomial (k := k) a b c).natDegree = a := by
  exact Polynomial.natDegree_X_pow_sub_C

/-- The principal tie ideal, defined independently of the polynomial map.-/
def tieIdeal (k : Type*) [Field k] (a b c : ℕ) [NeZero a] : Ideal (ThreePoly k) :=
  Ideal.span {tiePolynomial (k := k) a b c}

theorem tiePolynomial_mem_tieIdeal :
    tiePolynomial (k := k) a b c ∈ tieIdeal k a b c :=
  Ideal.subset_span (Set.mem_singleton _)

/-- A polynomial is x-reduced when every support exponent has x-coordinate
strictly below `a`.-/
def IsXReduced (a : ℕ) (f : ThreePoly k) : Prop :=
  ∀ d ∈ f.support, d 0 < a

/-- The canonical monic remainder representative.-/
def reducedRepresentative (a b c : ℕ) [NeZero a] (f : ThreePoly k) : ThreePoly k :=
  (threePolyEquivIterated (k := k)).symm
    (threePolyEquivIterated (k := k) f %ₘ iteratedTiePolynomial (k := k) a b c)

@[simp] theorem threePolyEquivIterated_reducedRepresentative (f : ThreePoly k) :
    threePolyEquivIterated (k := k) (reducedRepresentative a b c f) =
      threePolyEquivIterated (k := k) f %ₘ iteratedTiePolynomial (k := k) a b c := by
  simp [reducedRepresentative]

/-- The monic remainder has no x exponent reaching the tie degree.-/
theorem reducedRepresentative_isReduced (f : ThreePoly k) :
    IsXReduced a (reducedRepresentative a b c f) := by
  intro d hd
  let g := threePolyEquivIterated (k := k) f %ₘ iteratedTiePolynomial (k := k) a b c
  have hd' : d 0 ∈ g.support := by
    have hi : d 0 ∈ Finset.image (fun e : Fin 3 →₀ ℕ => e 0)
        (reducedRepresentative a b c f).support :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hi' : d 0 ∈
        (threePolyEquivIterated (k := k) (reducedRepresentative a b c f)).support := by
      change d 0 ∈
        (MvPolynomial.finSuccEquiv k 2 (reducedRepresentative a b c f)).support
      rw [MvPolynomial.support_finSuccEquiv]
      exact hi
    simpa [g] using hi'
  have hle : d 0 ≤ g.natDegree := Polynomial.le_natDegree_of_mem_supp _ hd'
  have hlt : g.natDegree < a := by
    simpa [g] using Polynomial.natDegree_modByMonic_lt
      (threePolyEquivIterated (k := k) f)
      (iteratedTiePolynomial_monic (k := k) (a := a) (b := b) (c := c))
      (by
        intro h
        have := congrArg Polynomial.natDegree h
        simp at this
        exact (NeZero.ne a this).elim)
  exact hle.trans_lt hlt

/-- Every polynomial differs from its monic remainder by a tie multiple.-/
theorem sub_reducedRepresentative_mem_tieIdeal (f : ThreePoly k) :
    f - reducedRepresentative a b c f ∈ tieIdeal k a b c := by
  let E := threePolyEquivIterated (k := k)
  let q := iteratedTiePolynomial (k := k) a b c
  let h : ThreePoly k := E.symm (E f /ₘ q)
  have hdecomp : reducedRepresentative a b c f + tiePolynomial (k := k) a b c * h = f := by
    apply E.injective
    simp only [map_add, map_mul, threePolyEquivIterated_reducedRepresentative,
      threePolyEquivIterated_tiePolynomial, E, q, h, AlgEquiv.apply_symm_apply]
    exact Polynomial.modByMonic_add_div _ _
  have hsub : f - reducedRepresentative a b c f = tiePolynomial (k := k) a b c * h := by
    nth_rewrite 1 [← hdecomp]
    simp only [add_sub_cancel_left]
  rw [hsub]
  exact Ideal.mul_mem_right h (tieIdeal k a b c)
    (tiePolynomial_mem_tieIdeal (k := k) (a := a) (b := b) (c := c))

/-- Exact coefficient formula for the polynomial-to-normal map.-/
theorem coeff_polyToNormalAlg (f : ThreePoly k) (p : Normal a b c) :
    (polyToNormalAlg (k := k) (a := a) (b := b) (c := c) f).coeff p =
      ∑ d ∈ f.support,
        if normalizeExponent a b c d = p then f.coeff d else 0 := by
  classical
  have hf := congrArg (polyToNormalAlg (k := k) (a := a) (b := b) (c := c))
    (MvPolynomial.as_sum f)
  calc
    (polyToNormalAlg (k := k) (a := a) (b := b) (c := c) f).coeff p =
        (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
          (∑ d ∈ f.support, MvPolynomial.monomial d (f.coeff d))).coeff p :=
      congrArg (fun z : NormalMonoidAlgebra k a b c => z.coeff p) hf
    _ = ∑ d ∈ f.support,
        if normalizeExponent a b c d = p then f.coeff d else 0 := by
      simp_rw [map_sum, polyToNormalAlg_monomial]
      have hcoeff := congrArg (fun g => g p)
        (MonoidAlgebra.coeff_sum f.support
          (fun d => f.coeff d • monomial (k := k) (normalizeExponent a b c d)))
      rw [hcoeff]
      have happ :
          (∑ d ∈ f.support,
            (f.coeff d • monomial (k := k) (normalizeExponent a b c d)).coeff) p =
          ∑ d ∈ f.support,
            (f.coeff d • monomial (k := k) (normalizeExponent a b c d)).coeff p := by
        exact map_sum (Finsupp.applyAddHom p)
          (fun d => (f.coeff d • monomial (k := k) (normalizeExponent a b c d)).coeff)
          f.support
      rw [happ]
      apply Finset.sum_congr rfl
      intro d hd
      simp [Finsupp.single_apply]

/-- Normalization is injective on x-reduced exponent triples.-/
theorem normalizeExponent_injective_of_x_lt {d e : Fin 3 →₀ ℕ}
    (hd : d 0 < a) (he : e 0 < a)
    (h : normalizeExponent a b c d = normalizeExponent a b c e) : d = e := by
  have hx := congrArg Normal.x h
  have hy := congrArg Normal.y h
  have hz := congrArg Normal.z h
  simp only [normalizeExponent, exponentRaw, Normal.normalize_x,
    Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at hx
  simp only [normalizeExponent, exponentRaw, Normal.normalize_y,
    Nat.div_eq_of_lt hd, Nat.div_eq_of_lt he, zero_mul, add_zero] at hy
  simp only [normalizeExponent, exponentRaw, Normal.normalize_z,
    Nat.div_eq_of_lt hd, Nat.div_eq_of_lt he, zero_mul, add_zero] at hz
  ext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

/-- The polynomial map is injective on x-reduced representatives.-/
theorem polyToNormalAlg_injective_on_reduced {f : ThreePoly k}
    (hred : IsXReduced a f)
    (hmap : polyToNormalAlg (k := k) (a := a) (b := b) (c := c) f = 0) :
    f = 0 := by
  classical
  ext d
  by_cases hd0 : f.coeff d = 0
  · simp [hd0]
  · have hd : d ∈ f.support := MvPolynomial.mem_support_iff.mpr hd0
    have hdx : d 0 < a := hred d hd
    have hc := congrArg (fun z : NormalMonoidAlgebra k a b c =>
      z.coeff (normalizeExponent a b c d)) hmap
    rw [coeff_polyToNormalAlg] at hc
    change (∑ e ∈ f.support,
        if normalizeExponent a b c e = normalizeExponent a b c d then f.coeff e else 0) = 0 at hc
    have hsum : (∑ e ∈ f.support,
        if normalizeExponent a b c e = normalizeExponent a b c d then f.coeff e else 0) =
        f.coeff d := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro e he hed
        have hex : e 0 < a := hred e he
        have hne : normalizeExponent a b c e ≠ normalizeExponent a b c d := by
          intro hnorm
          exact hed (normalizeExponent_injective_of_x_lt hex hdx hnorm)
        simp [hne]
      · intro hnot
        exact (hnot hd).elim
    rw [hsum] at hc
    exact (hd0 hc).elim

end

end P23.Presentation
