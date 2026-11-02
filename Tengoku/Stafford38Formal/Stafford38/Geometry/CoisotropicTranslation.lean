module
public import Tengoku.Stafford38Formal.Stafford38.Characteristic.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms derivative_fibreLinePolynomial` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fibreLinePolynomial_poissonBracket_baseLift` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms hamiltonIter_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms polynomial_eq_zero_of_eval_iterate_derivative_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fibreLinePolynomial_eq_zero_of_poisson` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms zeroSection_stable_under_differential_translation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms radicalPoisson_zeroSection_stable_under_differential_translation` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-!
# Poisson closure and vertical translation

This file proves a polynomial statement used by the coisotropic part of the
Stafford argument.  If a Poisson ideal vanishes at a point of the zero section
and contains a polynomial in the base variables, then it also vanishes after
the fibre coordinate is translated by any scalar multiple of the differential
of that base polynomial at the point.

Only polynomial rings, ideals, partial derivatives, and evaluation maps occur
here.  In particular, no variety, characteristic support, conormal bundle, or
geometric integration theorem is represented by these declarations.
-/

namespace Stafford38.Geometry.CoisotropicTranslation

open Stafford38.Characteristic

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Embed a polynomial in the base coordinates into the phase-space ring.-/
def baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n :=
  MvPolynomial.rename Sum.inl

/-- Evaluate the differential of a base polynomial at a base point.-/
def differentialAt (y : Fin n → k) (f : MvPolynomial (Fin n) k) (i : Fin n) : k :=
  MvPolynomial.eval y (MvPolynomial.pderiv i f)

/-- The polynomial obtained by evaluating a phase-space polynomial along the
arbitrary affine fibre line `(y, xi + t v)`.-/
def affineFibreLinePolynomial
    (y xi v : Fin n → k) (g : SymbolRing k n) : Polynomial k :=
  MvPolynomial.aeval
    (Sum.elim (fun i => Polynomial.C (y i))
      (fun i => Polynomial.C (xi i) + Polynomial.C (v i) * Polynomial.X)) g

/-- The point on the affine fibre line `(y, xi + t v)`.-/
def affineFibreTranslatePoint
    (y xi v : Fin n → k) (t : k) : PhaseVar n → k
  | Sum.inl i => y i
  | Sum.inr i => xi i + t * v i

/--
@isnad1 id=eq.0h7v.s5.0a8059294dea from=translated src=- shape=5bd96a76 vocab=68ac9a38
-/
@[simp] theorem affineFibreTranslatePoint_inl
    (y xi v : Fin n → k) (t : k) (i : Fin n) :
    affineFibreTranslatePoint y xi v t (Sum.inl i) = y i := rfl

/--
@isnad1 id=eq.0h7v.s6.51cc21eb2217 from=translated src=- shape=2ad3bb11 vocab=f77eabd4
-/
@[simp] theorem affineFibreTranslatePoint_inr
    (y xi v : Fin n → k) (t : k) (i : Fin n) :
    affineFibreTranslatePoint y xi v t (Sum.inr i) = xi i + t * v i := rfl

/-- The zero-section point over `y`.-/
def zeroSectionPoint (y : Fin n → k) : PhaseVar n → k
  | Sum.inl i => y i
  | Sum.inr _ => 0

/-- The zero-fibre specialization of `affineFibreTranslatePoint`, translating
`(y, 0)` by `t df_y`.-/
abbrev differentialTranslatePoint
    (y : Fin n → k) (f : MvPolynomial (Fin n) k) (t : k) : PhaseVar n → k :=
  affineFibreTranslatePoint y (fun _ => 0) (differentialAt y f) t

/--
@isnad1 id=eq.0h5v.s6.2cf27b5584c8 from=translated src=- shape=16e043e0 vocab=6a98ab2b
-/
theorem differentialTranslatePoint_eq_affineFibreTranslatePoint_zero
    (y : Fin n → k) (f : MvPolynomial (Fin n) k) (t : k) :
    differentialTranslatePoint y f t =
      affineFibreTranslatePoint y (fun _ => 0) (differentialAt y f) t := rfl

/-- The polynomial line `t ↦ g(y, t v)` in the fibre over `y`, the
zero-fibre specialization of `affineFibreLinePolynomial`.-/
abbrev fibreLinePolynomial
    (y v : Fin n → k) (g : SymbolRing k n) : Polynomial k :=
  affineFibreLinePolynomial y (fun _ => 0) v g

/--
@isnad1 id=eq.0h5v.s6.0ef208f2ac28 from=translated src=- shape=0da27763 vocab=fbc77b80
-/
theorem fibreLinePolynomial_eq_affineFibreLinePolynomial_zero
    (y v : Fin n → k) (g : SymbolRing k n) :
    fibreLinePolynomial y v g = affineFibreLinePolynomial y (fun _ => 0) v g := rfl

/-- Directional derivative in the fibre variables.-/
def verticalDeriv (v : Fin n → k) (g : SymbolRing k n) : SymbolRing k n :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv (Sum.inr i) g

/--
@isnad1 id=eq.0h4v.s7.be0029a17741 from=translated src=- shape=cfadfa59 vocab=39a31d50
-/
@[simp] theorem verticalDeriv_C (v : Fin n → k) (a : k) :
    verticalDeriv v (MvPolynomial.C a) = 0 := by
  simp [verticalDeriv]

/--
@isnad1 id=eq.0h5v.s7.cd9c47c1aa6b from=translated src=- shape=71802370 vocab=d7f5d10f
-/
theorem verticalDeriv_add (v : Fin n → k) (g h : SymbolRing k n) :
    verticalDeriv v (g + h) = verticalDeriv v g + verticalDeriv v h := by
  simp [verticalDeriv, mul_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h5v.s8.2739076a3b51 from=translated src=- shape=29d65c85 vocab=6079a141
-/
theorem verticalDeriv_mul (v : Fin n → k) (g h : SymbolRing k n) :
    verticalDeriv v (g * h) = verticalDeriv v g * h + g * verticalDeriv v h := by
  simp only [verticalDeriv, MvPolynomial.pderiv_mul, mul_add,
    Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl

/--
@isnad1 id=eq.0h4v.s6.28c61f20e81e from=translated src=- shape=8af65f9b vocab=38cac6db
-/
@[simp] theorem verticalDeriv_X_base (v : Fin n → k) (i : Fin n) :
    verticalDeriv v (MvPolynomial.X (Sum.inl i)) = 0 := by
  simp [verticalDeriv]

/--
@isnad1 id=eq.0h4v.s7.fb6ee9eb704a from=translated src=- shape=7555ff48 vocab=395952c1
-/
@[simp] theorem verticalDeriv_X_fibre (v : Fin n → k) (i : Fin n) :
    verticalDeriv v (MvPolynomial.X (Sum.inr i)) = MvPolynomial.C (v i) := by
  classical
  simp [verticalDeriv, Pi.single_apply]

/--
@isnad1 id=eq.0h5v.s7.3c087cba0749 from=translated src=- shape=e95c1b1a vocab=f7cbd216
-/
@[simp] theorem fibreLinePolynomial_C
    (y v : Fin n → k) (a : k) :
    fibreLinePolynomial y v (MvPolynomial.C a) = Polynomial.C a := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/--
@isnad1 id=eq.0h4v.s6.4b825fc78f27 from=translated src=- shape=96876ad1 vocab=1ad0cded
-/
@[simp] theorem fibreLinePolynomial_zero (y v : Fin n → k) :
    fibreLinePolynomial y v 0 = 0 := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/--
@isnad1 id=eq.0h6v.s7.035eda6496b1 from=translated src=- shape=70272549 vocab=0fe335cf
-/
@[simp] theorem fibreLinePolynomial_add
    (y v : Fin n → k) (g h : SymbolRing k n) :
    fibreLinePolynomial y v (g + h) =
      fibreLinePolynomial y v g + fibreLinePolynomial y v h := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/--
@isnad1 id=eq.0h6v.s7.ec2bd0f1b673 from=translated src=- shape=70272549 vocab=d2dbdd89
-/
@[simp] theorem fibreLinePolynomial_mul
    (y v : Fin n → k) (g h : SymbolRing k n) :
    fibreLinePolynomial y v (g * h) =
      fibreLinePolynomial y v g * fibreLinePolynomial y v h := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/--
@isnad1 id=eq.0h6v.s6.a137711469c7 from=translated src=- shape=44de4078 vocab=df90d563
-/
theorem fibreLinePolynomial_sum {ι : Type*} [Fintype ι]
    (y v : Fin n → k) (g : ι → SymbolRing k n) :
    fibreLinePolynomial y v (∑ i, g i) = ∑ i, fibreLinePolynomial y v (g i) := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/--
@isnad1 id=eq.0h5v.s7.a1d09830b57a from=translated src=- shape=9c76aae0 vocab=9d6f132e
-/
@[simp] theorem fibreLinePolynomial_X_base
    (y v : Fin n → k) (i : Fin n) :
    fibreLinePolynomial y v (MvPolynomial.X (Sum.inl i)) = Polynomial.C (y i) := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/--
@isnad1 id=eq.0h5v.s7.7dfa9492bfa9 from=translated src=- shape=50b84723 vocab=2d9ec925
-/
@[simp] theorem fibreLinePolynomial_X_fibre
    (y v : Fin n → k) (i : Fin n) :
    fibreLinePolynomial y v (MvPolynomial.X (Sum.inr i)) =
      Polynomial.C (v i) * Polynomial.X := by
  simp [fibreLinePolynomial, affineFibreLinePolynomial]

/-- Evaluating the affine fibre-line polynomial at time `t` is evaluation at
`(y, xi + t v)`.
@isnad1 id=eq.0h7v.s7.be3fe6a9cae9 from=translated src=- shape=70e6ce21 vocab=61e3e0e9
-/
theorem eval_affineFibreLinePolynomial (y xi v : Fin n → k)
    (g : SymbolRing k n) (t : k) :
    Polynomial.eval t (affineFibreLinePolynomial y xi v g) =
      MvPolynomial.eval (Sum.elim y (fun i => xi i + t * v i)) g := by
  change Polynomial.aeval t
      (MvPolynomial.aeval (Sum.elim
        (fun i => Polynomial.C (y i))
        (fun i => Polynomial.C (xi i) + Polynomial.C (v i) * Polynomial.X)) g) = _
  rw [MvPolynomial.comp_aeval_apply]
  change MvPolynomial.aeval _ g = MvPolynomial.aeval _ g
  apply DFunLike.congr_fun
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with i | i
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp only [Sum.elim_inr, map_add, Polynomial.aeval_C, Polynomial.aeval_mul,
      Polynomial.aeval_X]
    simp
    ring

/--
@isnad1 id=eq.0h5v.s8.a9adc1ef69a0 from=translated src=- shape=1c0e03fb vocab=23c3bf6f
-/
theorem derivative_fibreLinePolynomial
    (y v : Fin n → k) (g : SymbolRing k n) :
    Polynomial.derivative (fibreLinePolynomial y v g) =
      fibreLinePolynomial y v (verticalDeriv v g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [verticalDeriv]
  | add p q hp hq =>
      simp only [fibreLinePolynomial_add, Polynomial.derivative_add, hp, hq]
      rw [verticalDeriv_add, fibreLinePolynomial_add]
  | mul_X p i hp =>
      rcases i with i | i
      · simp only [fibreLinePolynomial_mul, fibreLinePolynomial_X_base, Polynomial.derivative_mul,
          Polynomial.derivative_C, zero_mul, add_zero, hp]
        simp [verticalDeriv_mul]
      · simp only [fibreLinePolynomial_mul, fibreLinePolynomial_X_fibre, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, zero_add, mul_one, hp]
        simp [verticalDeriv_mul]

/--
@isnad1 id=eq.0h6v.s7.a93cf5e548ec from=translated src=- shape=090914c7 vocab=a82f85de
-/
theorem eval_fibreLinePolynomial (y v : Fin n → k)
    (g : SymbolRing k n) (t : k) :
    Polynomial.eval t (fibreLinePolynomial y v g) =
      MvPolynomial.eval (Sum.elim y (fun i => t * v i)) g := by
  rw [fibreLinePolynomial_eq_affineFibreLinePolynomial_zero,
    eval_affineFibreLinePolynomial]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  rcases i with i | i <;> simp

/--
@isnad1 id=eq.0h5v.s7.56d1ed89ff24 from=translated src=- shape=f0fee42a vocab=4d68bd64
-/
theorem eval_zero_fibreLinePolynomial (y v : Fin n → k)
    (g : SymbolRing k n) :
    Polynomial.eval 0 (fibreLinePolynomial y v g) =
      MvPolynomial.eval (zeroSectionPoint y) g := by
  rw [eval_fibreLinePolynomial]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  rcases i with i | i <;> simp [zeroSectionPoint]

/--
@isnad1 id=eq.0h4v.s10.f27ce32111d6 from=translated src=- shape=6ecae5eb vocab=ff541e85
-/
theorem pderiv_baseLift_base (f : MvPolynomial (Fin n) k) (i : Fin n) :
    MvPolynomial.pderiv (Sum.inl i) (baseLift f) =
      baseLift (MvPolynomial.pderiv i f) := by
  exact MvPolynomial.pderiv_rename Sum.inl_injective i f

/--
@isnad1 id=eq.0h4v.s9.2174e9c7df49 from=translated src=- shape=f9445644 vocab=9a82b584
-/
theorem pderiv_baseLift_fibre (f : MvPolynomial (Fin n) k) (i : Fin n) :
    MvPolynomial.pderiv (Sum.inr i) (baseLift f) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hi
  rcases MvPolynomial.mem_vars_rename Sum.inl f hi with ⟨j, hj, hji⟩
  exact Sum.inl_ne_inr hji

/--
@isnad1 id=eq.0h5v.s9.41adcd821aa2 from=translated src=- shape=af87ed8c vocab=ac09cd2b
-/
theorem fibreLinePolynomial_baseLift
    (y v : Fin n → k) (f : MvPolynomial (Fin n) k) :
    fibreLinePolynomial y v (baseLift f) = Polynomial.C (MvPolynomial.eval y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [baseLift, fibreLinePolynomial, differentialAt]
  | add p q hp hq => simp only [map_add, fibreLinePolynomial_add, hp, hq,
      MvPolynomial.eval_add, map_add]
  | mul_X p j hp =>
      rw [map_mul, fibreLinePolynomial_mul, hp, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, map_mul]
      simp [baseLift]

/--
@isnad1 id=eq.0h6v.s9.86310be4936b from=translated src=- shape=a008206e vocab=afb3f83b
-/
theorem fibreLinePolynomial_baseLift_pderiv
    (y v : Fin n → k) (f : MvPolynomial (Fin n) k) (i : Fin n) :
    fibreLinePolynomial y v
        (MvPolynomial.pderiv (Sum.inl i) (baseLift f)) =
      Polynomial.C (differentialAt y f i) := by
  rw [pderiv_baseLift_base, fibreLinePolynomial_baseLift]
  rfl

/--
@isnad1 id=eq.0h5v.s8.09be6a11eb03 from=translated src=- shape=c25bcc19 vocab=4ea78ad6
-/
theorem fibreLinePolynomial_poissonBracket_baseLift
    (y : Fin n → k) (f : MvPolynomial (Fin n) k) (g : SymbolRing k n) :
    fibreLinePolynomial y (differentialAt y f) (poissonBracket (baseLift f) g) =
      fibreLinePolynomial y (differentialAt y f)
        (verticalDeriv (differentialAt y f) g) := by
  simp only [poissonBracket, pderiv_baseLift_base, pderiv_baseLift_fibre, zero_mul,
    sub_zero, verticalDeriv, fibreLinePolynomial_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [fibreLinePolynomial_mul, fibreLinePolynomial_baseLift, differentialAt]

/-! ## Iterated Hamiltonian differentiation -/

/-- Iteration of bracketing on the left by one base equation.-/
def hamiltonIter (f : MvPolynomial (Fin n) k) : ℕ → SymbolRing k n → SymbolRing k n
  | 0, g => g
  | m + 1, g => poissonBracket (baseLift f) (hamiltonIter f m g)

/--
@isnad1 id=eq.0h6v.s8.f8c896a75f68 from=translated src=- shape=da46be2f vocab=f9210720
-/
theorem iterate_derivative_fibreLinePolynomial
    (y : Fin n → k) (f : MvPolynomial (Fin n) k)
    (g : SymbolRing k n) (m : ℕ) :
    (Polynomial.derivative^[m])
        (fibreLinePolynomial y (differentialAt y f) g) =
      fibreLinePolynomial y (differentialAt y f) (hamiltonIter f m g) := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', hm, derivative_fibreLinePolynomial,
        ← fibreLinePolynomial_poissonBracket_baseLift]
      rfl

/--
@isnad1 id=mem.3h6v.s9.e76a6d8c2e32 from=translated src=- shape=0e8643c5 vocab=9ff0ac61
-/
theorem hamiltonIter_mem
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    ∀ m, hamiltonIter f m g ∈ J := by
  intro m
  induction m with
  | zero => exact hg
  | succ m hm => exact hJ (baseLift f) hf (hamiltonIter f m g)

/--
@isnad1 id=eq.1h2v.s8.14d988cbf826 from=translated src=- shape=57786bc1 vocab=e745f989
-/
theorem polynomial_eq_zero_of_eval_iterate_derivative_zero
    [CharZero k]
    (q : Polynomial k)
    (h : ∀ m, Polynomial.eval 0 ((Polynomial.derivative^[m]) q) = 0) :
    q = 0 := by
  ext m
  have hm0 : ((Polynomial.derivative^[m]) q).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact h m
  have hm : (Nat.factorial m : k) * q.coeff m = 0 := by
    simpa only [Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul] using hm0
  have hc : q.coeff m = 0 :=
    (mul_eq_zero.mp hm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero m)
  simpa using hc

/--
@isnad1 id=eq.4h6v.s10.d36805727b67 from=translated src=- shape=0506babc vocab=410473a8
-/
theorem fibreLinePolynomial_eq_zero_of_poisson
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    fibreLinePolynomial y (differentialAt y f) g = 0 := by
  apply polynomial_eq_zero_of_eval_iterate_derivative_zero
  intro m
  rw [iterate_derivative_fibreLinePolynomial, eval_zero_fibreLinePolynomial]
  exact hzero _ (hamiltonIter_mem J hJ f hf g hg m)

/-! ## The exact translation statement -/

/--
A zero-section common zero of a Poisson ideal remains a common zero after
vertical translation by `t df_y`, for every scalar `t`, whenever the base
polynomial `f` belongs to the ideal.

The radical hypothesis customary in the geometric application is unnecessary
for this polynomial implication; see the wrapper below.
@isnad1 id=eq.4h7v.s10.3f2e485cba9f from=translated src=- shape=72982ac5 vocab=84c7bab5
-/
theorem zeroSection_stable_under_differential_translation
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) (t : k) :
    MvPolynomial.eval (differentialTranslatePoint y f t) g = 0 := by
  have heval :
      MvPolynomial.eval (differentialTranslatePoint y f t) g =
        MvPolynomial.eval (Sum.elim y (fun i => t * differentialAt y f i)) g := by
    apply MvPolynomial.eval₂_congr
    intro i c hi hc
    rcases i with i | i <;> simp [differentialTranslatePoint, affineFibreTranslatePoint]
  rw [heval, ← eval_fibreLinePolynomial]
  rw [fibreLinePolynomial_eq_zero_of_poisson J hJ y hzero f hf g hg]
  exact Polynomial.eval_zero

/-- The same statement with the radical hypothesis carried explicitly.
@isnad1 id=eq.5h7v.s10.d152fe04ac35 from=translated src=- shape=8f97e560 vocab=552869ee
-/
theorem radicalPoisson_zeroSection_stable_under_differential_translation
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (_hJrad : J.IsRadical) (hJ : IsPoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) (t : k) :
    MvPolynomial.eval (differentialTranslatePoint y f t) g = 0 :=
  zeroSection_stable_under_differential_translation J hJ y hzero f hf g hg t

end

end Stafford38.Geometry.CoisotropicTranslation
