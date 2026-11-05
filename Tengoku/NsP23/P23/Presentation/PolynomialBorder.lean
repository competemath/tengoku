import Tengoku.NsP23.P23.Presentation.MonomialQuotient
import Tengoku.NsP23.P23.Presentation.TieQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial lifts of the exact border

This file pulls the frozen Run 13 border ideal back through the frozen Run 14
single-tie presentation, then computes the kernel of the composite map to the
direct finite model.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie P23.Artin

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- The reduced three-variable polynomial representative of a normalized
monomial.-/
def polynomialLift (p : Normal a b c) : ThreePoly k :=
  MvPolynomial.monomial (normalExponent p) 1

@[simp]
theorem polyToNormalAlg_polynomialLift (p : Normal a b c) :
    polyToNormalAlg (k := k) (polynomialLift (k := k) p) =
      monomial (k := k) p := by
  simp [polynomialLift]

/-- Distinct normalized exponents have distinct reduced polynomial lifts.-/
theorem polynomialLift_injective :
    Function.Injective (polynomialLift (k := k) (a := a) (b := b) (c := c)) := by
  intro p q h
  have hexp : normalExponent p = normalExponent q :=
    MvPolynomial.monomial_left_injective (one_ne_zero : (1 : k) ≠ 0) <| by
      simpa only [polynomialLift] using h
  apply Normal.ext
  · simpa using congrArg (fun d : Fin 3 →₀ ℕ => d 0) hexp
  · simpa using congrArg (fun d : Fin 3 →₀ ℕ => d 1) hexp
  · simpa using congrArg (fun d : Fin 3 →₀ ℕ => d 2) hexp

/-- Polynomial lifts indexed by the exact frozen border.-/
def polynomialBorderSet (S : Finset (Normal a b c)) : Set (ThreePoly k) :=
  {f | ∃ g ∈ borderFinset S, f = polynomialLift (k := k) g}

/-- The polynomial border ideal, defined independently as an actual span.-/
def polynomialBorderIdeal (S : Finset (Normal a b c)) : Ideal (ThreePoly k) :=
  Ideal.span (polynomialBorderSet (k := k) S)

/-- The displayed final presentation ideal: the principal tie joined with the
independently generated polynomial border ideal.-/
def finitePresentationIdeal (S : Finset (Normal a b c)) : Ideal (ThreePoly k) :=
  tieIdeal k a b c ⊔ polynomialBorderIdeal (k := k) S

theorem polynomialLift_mem_polynomialBorderIdeal (S : Finset (Normal a b c))
    {g : Normal a b c} (hg : g ∈ borderFinset S) :
    polynomialLift (k := k) g ∈ polynomialBorderIdeal (k := k) S := by
  apply Ideal.subset_span
  exact ⟨g, hg, rfl⟩

theorem tiePolynomial_mem_finitePresentationIdeal
    (S : Finset (Normal a b c)) :
    tiePolynomial (k := k) a b c ∈ finitePresentationIdeal (k := k) S := by
  apply Ideal.mem_sup_left
  exact Ideal.subset_span (Set.mem_singleton _)

theorem polynomialLift_mem_finitePresentationIdeal_of_border
    (S : Finset (Normal a b c)) {g : Normal a b c}
    (hg : g ∈ borderFinset S) :
    polynomialLift (k := k) g ∈ finitePresentationIdeal (k := k) S := by
  apply Ideal.mem_sup_right
  exact polynomialLift_mem_polynomialBorderIdeal S hg

/-- The independently defined polynomial border span maps exactly to the
frozen normal-monoid border ideal.-/
theorem polynomialBorderIdeal_map (S : Finset (Normal a b c)) :
    Ideal.map
        (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom
        (polynomialBorderIdeal (k := k) S) =
      borderMonomialIdeal (k := k) S := by
  rw [polynomialBorderIdeal, borderMonomialIdeal, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨p, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, by simp⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨polynomialLift (k := k) g, ⟨g, hg, rfl⟩, ?_⟩
    simp

/-- Exact pullback of the frozen normal-monoid border ideal.-/
theorem borderMonomialIdeal_comap (S : Finset (Normal a b c)) :
    Ideal.comap
        (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom
        (borderMonomialIdeal (k := k) S) =
      finitePresentationIdeal (k := k) S := by
  rw [← polynomialBorderIdeal_map (k := k) S]
  rw [Ideal.comap_map_of_surjective
    (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom
    (polyToNormalAlg_surjective (k := k) (a := a) (b := b) (c := c))]
  rw [← RingHom.ker_eq_comap_bot, polyToNormalAlg_ker]
  simpa only [finitePresentationIdeal] using
    (sup_comm (polynomialBorderIdeal (k := k) S) (tieIdeal k a b c))

/-- In the live nonempty domain, the killed-ideal pullback has the same exact
tie-plus-border presentation.-/
theorem killedMonomialIdeal_comap (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c) :
    Ideal.comap
        (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom
        (killedMonomialIdeal (k := k) S) =
      finitePresentationIdeal (k := k) S := by
  rw [← borderMonomialIdeal_eq_killedMonomialIdeal (k := k) S hS hdom]
  exact borderMonomialIdeal_comap (k := k) S

/-- The composite polynomial-to-direct-model algebra homomorphism.-/
def polyToDirectAlg (S : Finset (Normal a b c)) :
    ThreePoly k →ₐ[k] MonomialArtin k S :=
  (truncateAlgHom (k := k) S).comp
    (polyToNormalAlg (k := k) (a := a) (b := b) (c := c))

/-- Exact normalized monomial formula for the composite map.-/
@[simp]
theorem polyToDirectAlg_monomial (S : Finset (Normal a b c))
    (d : Fin 3 →₀ ℕ) (r : k) :
    polyToDirectAlg (k := k) S (MvPolynomial.monomial d r) =
      r • truncatedMonomial (k := k) S (normalizeExponent a b c d) := by
  simp [polyToDirectAlg]

@[simp] theorem polyToDirectAlg_polyX (S : Finset (Normal a b c)) :
    polyToDirectAlg (k := k) S polyX =
      truncatedMonomial (k := k) S (Normal.xGenerator : Normal a b c) := by
  simp [polyToDirectAlg]

@[simp] theorem polyToDirectAlg_polyY (S : Finset (Normal a b c)) :
    polyToDirectAlg (k := k) S polyY =
      truncatedMonomial (k := k) S (Normal.yGenerator : Normal a b c) := by
  simp [polyToDirectAlg]

@[simp] theorem polyToDirectAlg_polyZ (S : Finset (Normal a b c)) :
    polyToDirectAlg (k := k) S polyZ =
      truncatedMonomial (k := k) S (Normal.zGenerator : Normal a b c) := by
  simp [polyToDirectAlg]

theorem polyToDirectAlg_surjective (S : Finset (Normal a b c)) :
    Function.Surjective (polyToDirectAlg (k := k) S) := by
  intro x
  obtain ⟨f, rfl⟩ := truncateAlgHom_surjective (k := k) S x
  obtain ⟨p, rfl⟩ :=
    polyToNormalAlg_surjective (k := k) (a := a) (b := b) (c := c) f
  exact ⟨p, rfl⟩

/-- The final polynomial kernel is generated by the single tie and the exact
polynomial border lifts.-/
theorem polyToDirectAlg_ker (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c) :
    RingHom.ker (polyToDirectAlg (k := k) S).toRingHom =
      finitePresentationIdeal (k := k) S := by
  calc
    RingHom.ker (polyToDirectAlg (k := k) S).toRingHom =
        Ideal.comap
          (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom
          (RingHom.ker (truncateAlgHom (k := k) S).toRingHom) := by
            change RingHom.ker
                ((truncateAlgHom (k := k) S).comp
                  (polyToNormalAlg (k := k) (a := a) (b := b) (c := c))) =
              Ideal.comap
                (polyToNormalAlg (k := k) (a := a) (b := b) (c := c))
                (RingHom.ker (truncateAlgHom (k := k) S))
            exact (AlgHom.comap_ker (truncateAlgHom (k := k) S)
              (polyToNormalAlg (k := k) (a := a) (b := b) (c := c))).symm
    _ = Ideal.comap
          (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom
          (killedMonomialIdeal (k := k) S) := by
            rw [truncateAlgHom_ker]
    _ = finitePresentationIdeal (k := k) S :=
      killedMonomialIdeal_comap (k := k) S hS hdom

end

end P23.Presentation
