import Tengoku.TdaLib.TDA.Persistence.FinitePresentationClosure
import Tengoku.Seed.Topology.EMetricSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The interleaving distance on finitely presented isomorphism classes

For a ring `R` and `n : ℕ`, take the subtype of finitely presented modules
`PModule R (Fin n → ℝ)` and quotient it by natural isomorphism. The coordinate
interleaving distance descends to this quotient and defines an extended metric.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

variable {R : Type u} [Ring R] {n : ℕ}

/-- A coordinate persistence module together with a proof of finite presentation.-/
abbrev FinitelyPresentedModule :=
  {M : PModule.{u,0,max u w} R (Fin n → ℝ) // FinitelyPresented (R := R) M}

namespace FinitePresentationIsoClasses

/-- Finitely presented modules are equivalent when naturally isomorphic.-/
def isoSetoid : Setoid (FinitelyPresentedModule (R := R) (n := n)) where
  r M N := Nonempty (M.1 ≅ N.1)
  iseqv := ⟨
    fun M => ⟨Iso.refl M.1⟩,
    fun h => by
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩,
    fun h₁ h₂ => by
      rcases h₁ with ⟨e⟩
      rcases h₂ with ⟨f⟩
      exact ⟨e ≪≫ f⟩⟩

end FinitePresentationIsoClasses

/-- Isomorphism classes of finitely presented coordinate persistence modules.-/
abbrev FinitePresentationIsoClasses :=
  Quotient (FinitePresentationIsoClasses.isoSetoid (R := R) (n := n))

namespace FinitePresentationIsoClasses

/-- The isomorphism class represented by a finitely presented module.-/
def classOf (M : FinitelyPresentedModule (R := R) (n := n)) :
    FinitePresentationIsoClasses (R := R) (n := n) :=
  Quotient.mk isoSetoid M

/-- The coordinate interleaving distance on isomorphism classes.-/
noncomputable def distance
    (x y : FinitePresentationIsoClasses (R := R) (n := n)) : ℝ≥0∞ :=
  Quotient.lift₂
    (fun M N => coordinateInterleavingDistance M.1 N.1)
    (by
      intro M M' N N' hM hN
      rcases hM with ⟨e⟩
      rcases hN with ⟨f⟩
      exact coordinateInterleavingDistance_congr e f)
    x y

/--
@isnad1 id=eq.0h4v.s7.17a0e105d270 from=translated src=- shape=2e08607d vocab=82e7c871
-/
@[simp]
theorem distance_classOf
    (M N : FinitelyPresentedModule (R := R) (n := n)) :
    distance (classOf M) (classOf N) =
      coordinateInterleavingDistance M.1 N.1 := rfl

/-- Isomorphic representatives have the same distance to any isomorphic pair.
@isnad1 id=eq.0h8v.s8.c566b6b1fe3c from=translated src=- shape=5faf3f09 vocab=2730b514
-/
theorem distance_congr
    {M M' N N' : FinitelyPresentedModule (R := R) (n := n)}
    (e : M.1 ≅ M'.1) (f : N.1 ≅ N'.1) :
    distance (classOf M) (classOf N) = distance (classOf M') (classOf N') := by
  rw [distance_classOf, distance_classOf]
  exact coordinateInterleavingDistance_congr e f

/-- Every isomorphism class has zero distance from itself.
@isnad1 id=eq.0h3v.s4.cc524bf95ba4 from=translated src=- shape=e4b56650 vocab=4216ec41
-/
theorem distance_self (x : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x x = 0 := by
  induction x using Quotient.inductionOn with
  | h M =>
    change distance (classOf M) (classOf M) = 0
    rw [distance_classOf]
    exact coordinateInterleavingDistance_self M.1

/-- The quotient distance is symmetric.
@isnad1 id=eq.0h4v.s4.b05e2f3a73b3 from=translated src=- shape=9af7f099 vocab=4216ec41
-/
theorem distance_comm (x y : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x y = distance y x := by
  induction x using Quotient.inductionOn with
  | h M =>
    induction y using Quotient.inductionOn with
    | h N =>
      change distance (classOf M) (classOf N) = distance (classOf N) (classOf M)
      rw [distance_classOf, distance_classOf]
      exact coordinateInterleavingDistance_comm M.1 N.1

/-- The quotient distance satisfies the extended triangle inequality.
@isnad1 id=le.0h5v.s5.2f5487210e16 from=translated src=- shape=4df0f0c4 vocab=904d8760
-/
theorem distance_triangle
    (x y z : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x z ≤ distance x y + distance y z := by
  induction x using Quotient.inductionOn with
  | h M =>
    induction y using Quotient.inductionOn with
    | h N =>
      induction z using Quotient.inductionOn with
      | h P =>
        change distance (classOf M) (classOf P) ≤
          distance (classOf M) (classOf N) + distance (classOf N) (classOf P)
        rw [distance_classOf, distance_classOf, distance_classOf]
        exact coordinateInterleavingDistance_triangle M.1 N.1 P.1

/-- On presented representatives, zero distance is equivalent to natural isomorphism.
@isnad1 id=iff.0h4v.s7.0dae5f8108df from=translated src=- shape=45ea3b20 vocab=885d5d31
-/
theorem distance_classOf_eq_zero_iff_iso
    (M N : FinitelyPresentedModule (R := R) (n := n)) :
    distance (classOf M) (classOf N) = 0 ↔ Nonempty (M.1 ≅ N.1) := by
  rw [distance_classOf]
  exact finitelyPresented_distance_eq_zero_iff_iso M.2 N.2

/-- Zero distance on the quotient is equality of isomorphism classes.
@isnad1 id=iff.0h4v.s5.2a8db290f730 from=translated src=- shape=c6db8ed5 vocab=4216ec41
-/
theorem distance_eq_zero_iff_eq
    (x y : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x y = 0 ↔ x = y := by
  constructor
  · intro h
    induction x using Quotient.inductionOn with
    | h M =>
      induction y using Quotient.inductionOn with
      | h N =>
        change distance (classOf M) (classOf N) = 0 at h
        rw [distance_classOf] at h
        apply Quotient.sound
        apply (finitelyPresented_distance_eq_zero_iff_iso M.2 N.2).mp
        exact h
  · rintro rfl
    exact distance_self x

/-- Isomorphism classes form an extended metric space for the descended distance.-/
noncomputable instance emetricSpace :
    EMetricSpace (FinitePresentationIsoClasses (R := R) (n := n)) where
  toPseudoEMetricSpace :=
    PseudoEMetricSpace.ofEDist distance distance_self distance_comm distance_triangle
  eq_of_edist_eq_zero := by
    intro x y h
    change distance x y = 0 at h
    exact distance_eq_zero_iff_eq x y |>.mp h

/-- The `edist` instance agrees with the original distance on representatives.
@isnad1 id=eq.0h4v.s7.8507059d1fd6 from=translated src=- shape=5e4dfa42 vocab=e02b441f
-/
@[simp]
theorem edist_classOf
    (M N : FinitelyPresentedModule (R := R) (n := n)) :
    edist (classOf M) (classOf N) = coordinateInterleavingDistance M.1 N.1 := rfl

end FinitePresentationIsoClasses

end TDA.Persistence.GradedFree
