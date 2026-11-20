import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Plane cubics as coefficient vectors

A homogeneous cubic form in the variables `x, y, z` (indexed `0, 1, 2` in `Fin 3`)
is represented by its vector of 10 coefficients, in the fixed monomial order

| index | 0  | 1   | 2   | 3   | 4   | 5   | 6  | 7   | 8   | 9  |
|-------|----|-----|-----|-----|-----|-----|----|-----|-----|----|
| mono  | x³ | x²y | x²z | xy² | xyz | xz² | y³ | y²z | yz² | z³ |
-/
namespace Tengoku.CayleyBacharach end Tengoku.CayleyBacharach open Tengoku.CayleyBacharach
/-- A plane cubic form over `K`: coefficient vector w.r.t. the monomial order
`x³, x²y, x²z, xy², xyz, xz², y³, y²z, yz², z³`.-/
abbrev _root_.Tengoku.CayleyBacharach.PlaneCubic (K : Type*) := Fin 10 → K

namespace Tengoku.CayleyBacharach.PlaneCubic

section CommRing

variable {R : Type*} [CommRing R]

/-- The values of the 10 cubic monomials at `v = (x, y, z)`, in the fixed order.-/
def mono (v : Fin 3 → R) : Fin 10 → R :=
  ![v 0 ^ 3, v 0 ^ 2 * v 1, v 0 ^ 2 * v 2, v 0 * v 1 ^ 2, v 0 * v 1 * v 2,
    v 0 * v 2 ^ 2, v 1 ^ 3, v 1 ^ 2 * v 2, v 1 * v 2 ^ 2, v 2 ^ 3]

/-- Evaluation of a cubic at a vector `v : Fin 3 → R`.-/
def eval (F : PlaneCubic R) (v : Fin 3 → R) : R := ∑ i, F i * mono v i

/-- The `i`-th monomial, as a cubic.-/
def monomial (i : Fin 10) : PlaneCubic R := Pi.single i 1

/--
@isnad1 id=eq.0h3v.s10.60391a50908f from=translated src=- shape=34dd4545 vocab=e16825d2
-/
theorem eval_expand (F : PlaneCubic R) (v : Fin 3 → R) :
    eval F v = F 0 * v 0 ^ 3 + F 1 * (v 0 ^ 2 * v 1) + F 2 * (v 0 ^ 2 * v 2)
      + F 3 * (v 0 * v 1 ^ 2) + F 4 * (v 0 * v 1 * v 2) + F 5 * (v 0 * v 2 ^ 2)
      + F 6 * v 1 ^ 3 + F 7 * (v 1 ^ 2 * v 2) + F 8 * (v 1 * v 2 ^ 2)
      + F 9 * v 2 ^ 3 := by
  simp [eval, mono, Fin.sum_univ_succ]
  ring

/--
@isnad1 id=eq.0h3v.s5.126943c7675a from=translated src=- shape=b7c3bb76 vocab=0ae58647
-/
theorem eval_monomial (i : Fin 10) (v : Fin 3 → R) : eval (monomial i) v = mono v i := by
  simp [eval, monomial, Pi.single_apply]

/--
@isnad1 id=eq.0h4v.s6.9899e594576f from=translated src=- shape=5ae239bd vocab=9d0f635d
-/
theorem eval_add (F G : PlaneCubic R) (v : Fin 3 → R) : eval (F + G) v = eval F v + eval G v := by
  simp [eval, add_mul, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h4v.s6.f555c1bc292e from=translated src=- shape=5ae239bd vocab=7888851f
-/
theorem eval_sub (F G : PlaneCubic R) (v : Fin 3 → R) : eval (F - G) v = eval F v - eval G v := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]

/--
@isnad1 id=eq.0h2v.s6.bc46f4d2f6be from=translated src=- shape=d8207e70 vocab=d7fd5035
-/
theorem eval_zero (v : Fin 3 → R) : eval (0 : PlaneCubic R) v = 0 := by
  simp [eval]

/--
@isnad1 id=eq.0h4v.s6.3364393b571f from=translated src=- shape=bb861dfd vocab=26380d4a
-/
theorem eval_smul (c : R) (F : PlaneCubic R) (v : Fin 3 → R) : eval (c • F) v = c * eval F v := by
  simp [eval, Finset.mul_sum, mul_assoc]

/-- Evaluation at a fixed vector, as a linear functional on cubics.-/
def evalLin (v : Fin 3 → R) : PlaneCubic R →ₗ[R] R where
  toFun F := eval F v
  map_add' F G := eval_add F G v
  map_smul' c F := eval_smul c F v

/--
@isnad1 id=eq.0h3v.s7.4d570bc69d68 from=translated src=- shape=23b51f21 vocab=14dae371
-/
@[simp] theorem evalLin_apply (v : Fin 3 → R) (F : PlaneCubic R) : evalLin v F = eval F v := rfl

/-- The monomial basis of the space of cubics.-/
noncomputable def monoBasis : Module.Basis (Fin 10) R (PlaneCubic R) := Pi.basisFun R (Fin 10)

/--
@isnad1 id=eq.0h2v.s7.2fbc602e2d3d from=translated src=- shape=d6dbc0fb vocab=6d0a16d5
-/
theorem monoBasis_apply (i : Fin 10) : (monoBasis i : PlaneCubic R) = monomial i := by
  simp [monoBasis, monomial]

/--
@isnad1 id=eq.0h4v.s6.4e444dd2ba7e from=translated src=- shape=fab7dfb2 vocab=a4049932
-/
theorem mono_smul (c : R) (v : Fin 3 → R) (i : Fin 10) :
    mono (c • v) i = c ^ 3 * mono v i := by
  fin_cases i <;> simp [mono] <;> ring

/-- Homogeneity: `F(c • v) = c³ F(v)`.
@isnad1 id=eq.0h4v.s6.bdfc5c9da061 from=translated src=- shape=d71a8eab vocab=c7bcb341
-/
theorem eval_smul_vec (F : PlaneCubic R) (c : R) (v : Fin 3 → R) :
    eval F (c • v) = c ^ 3 * eval F v := by
  simp only [eval, mono_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `F` vanishes at the (projective point represented by the) vector `v`.-/
def VanishesAt (F : PlaneCubic R) (v : Fin 3 → R) : Prop := eval F v = 0

/-- Vanishing at a projective point is independent of the representative.
@isnad1 id=iff.1h4v.s6.bffbb27099fd from=translated src=- shape=dd570391 vocab=faa234f0
-/
theorem vanishesAt_smul_iff [IsDomain R] (F : PlaneCubic R) {c : R} (hc : c ≠ 0)
    (v : Fin 3 → R) : VanishesAt F (c • v) ↔ VanishesAt F v := by
  simp [VanishesAt, eval_smul_vec, hc]

end CommRing

end Tengoku.CayleyBacharach.PlaneCubic
-- Tengoku: root names of this library moved to Tengoku.CayleyBacharach so they do not collide with other libraries (generated)
