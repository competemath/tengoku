import Tengoku.NsP23.P23.Artin.Coefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical dual relations and coefficient obstructions

Reusable direct-model lemmas underlying the exact-family Run-10 trace
contradictions.  No family geometry or trace extraction is introduced here.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

/-- Two monomial actions on dual basis elements agree when they remove their
respective scalar factors and leave the same surviving quotient.-/
theorem dual_relation_of_common_quotient (S : Finset (Normal a b c))
    (m n q s t : MonomialIndex S)
    (hms : m.1 * q.1 = s.1) (hnt : n.1 * q.1 = t.1) :
    X (k := k) S m.1 m.2 • U (k := k) S s =
      X (k := k) S n.1 n.2 • U (k := k) S t := by
  rw [X_smul_U_eq_U (k := k) S m q s hms]
  rw [X_smul_U_eq_U (k := k) S n q t hnt]

/-- An A-linear map transfers coefficients across a dual relation whenever
both scalar/coefficient products are the same surviving target.-/
theorem coeff_transfer_of_dual_relation (S : Finset (Normal a b c))
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (m n e h w s t : MonomialIndex S)
    (hrel : X (k := k) S m.1 m.2 • U (k := k) S s =
      X (k := k) S n.1 n.2 • U (k := k) S t)
    (hmew : m.1 * e.1 = w.1) (hnhw : n.1 * h.1 = w.1) :
    coeffAt (k := k) S e (F (U (k := k) S s)) =
      coeffAt (k := k) S h (F (U (k := k) S t)) := by
  have hmap :
      X (k := k) S m.1 m.2 * F (U (k := k) S s) =
        X (k := k) S n.1 n.2 * F (U (k := k) S t) := by
    simpa [smul_eq_mul] using congrArg F hrel
  have hcoeff := congrArg (coeffAt (k := k) S w) hmap
  rw [coeffAt_X_mul (k := k) S m e w hmew,
    coeffAt_X_mul (k := k) S n h w hnhw] at hcoeff
  exact hcoeff

/-- Common-quotient form of coefficient transfer, combining the preceding two
generic lemmas.-/
theorem coeff_transfer_of_common_quotient (S : Finset (Normal a b c))
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (m n q e h w s t : MonomialIndex S)
    (hms : m.1 * q.1 = s.1) (hnt : n.1 * q.1 = t.1)
    (hmew : m.1 * e.1 = w.1) (hnhw : n.1 * h.1 = w.1) :
    coeffAt (k := k) S e (F (U (k := k) S s)) =
      coeffAt (k := k) S h (F (U (k := k) S t)) :=
  coeff_transfer_of_dual_relation (k := k) S F m n e h w s t
    (dual_relation_of_common_quotient (k := k) S m n q s t hms hnt)
    hmew hnhw

/-- If a monomial annihilates a dual basis element, every coefficient whose
product with that monomial survives must vanish in every A-linear image.-/
theorem coeff_eq_zero_of_annihilator (S : Finset (Normal a b c))
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (l h g s : MonomialIndex S)
    (hzero : X (k := k) S l.1 l.2 • U (k := k) S s = 0)
    (hlhg : l.1 * h.1 = g.1) :
    coeffAt (k := k) S h (F (U (k := k) S s)) = 0 := by
  have hmap :
      X (k := k) S l.1 l.2 * F (U (k := k) S s) = 0 := by
    simpa [smul_eq_mul] using congrArg F hzero
  have hcoeff := congrArg (coeffAt (k := k) S g) hmap
  rw [coeffAt_X_mul (k := k) S l h g hlhg] at hcoeff
  simpa using hcoeff

end

end P23.Artin
