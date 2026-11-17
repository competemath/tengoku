/-
Agrawal r = 5 — THE LITERAL ROW-TO-RESULTANT INTERFACE.

For an inert prime `q`, the cyclotomic quotient `Phi5Ring q` is a field.
A pure or twisted literal row at exponent `A + 1` then supplies a common
root modulo `q` of `Φ₅` and the corresponding integer fiber polynomial:

  pure:    (X - 1)^A - 1,
  twisted: X (X - 1)^A + 1.

The Sylvester resultant therefore vanishes modulo `q`.  Irreducibility of
`Φ₅ mod q` gives more: `Φ₅` divides the fiber polynomial modulo `q`, so the
integral remainder has every coefficient divisible by `q`.  Homogeneity of
the resultant in its second input then supplies the full factor `q^4`.
Independently, reduction modulo `5` identifies `Φ₅` with `(X - 1)^4`;
evaluation at `1` shows that both resultants are `1 mod 5`, hence nonzero.
Together these facts yield the fixed-exponent size trap
`q^4 ≤ natAbs resultant`.  A complex-root product then proves the closed
estimate `natAbs resultant ≤ 16 * 5^A`.
-/
import Tengoku.AgrawalR5.AgrawalCore.QuarticRigidity
import Tengoku.Seed.FieldTheory.Minpoly.Field
import Tengoku.Seed.RingTheory.Polynomial.Resultant.Basic
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Factorization
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.Seed.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial
open scoped ComplexConjugate

namespace AgrawalCore

theorem phi5_eq_cyclotomic {p : ℕ} [Fact p.Prime] :
    phi5 p = cyclotomic 5 (ZMod p) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [cyclotomic_prime]
  simp [phi5, Finset.sum_range_succ, add_assoc, add_comm]

theorem inertModFive_orderOf_unitOfCoprime {p : ℕ} [Fact p.Prime]
    (hp : InertModFive p) :
    orderOf (ZMod.unitOfCoprime p (by
      apply (show p.Prime from Fact.out).coprime_iff_not_dvd.mpr
      intro h
      have hp5 : p = 5 :=
        (Nat.prime_dvd_prime_iff_eq (show p.Prime from Fact.out) (by norm_num)).mp h
      subst p
      norm_num [InertModFive] at hp)) = 4 := by
  let hcop : p.Coprime 5 := by
    apply (show p.Prime from Fact.out).coprime_iff_not_dvd.mpr
    intro h
    have hp5 : p = 5 :=
      (Nat.prime_dvd_prime_iff_eq (show p.Prime from Fact.out) (by norm_num)).mp h
    subst p
    norm_num [InertModFive] at hp
  change orderOf (ZMod.unitOfCoprime p hcop) = 4
  apply (orderOf_eq_iff (x := ZMod.unitOfCoprime p hcop) (by norm_num)).2
  constructor
  · apply Units.ext
    change (p : ZMod 5) ^ 4 = 1
    rw [← ZMod.natCast_mod p 5]
    rcases hp with hp2 | hp3
    · rw [hp2]
      decide
    · rw [hp3]
      decide
  · intro m hm hpos heq
    have hv := congrArg Units.val heq
    change (p : ZMod 5) ^ m = 1 at hv
    rw [← ZMod.natCast_mod p 5] at hv
    rcases hp with hp2 | hp3
    · rw [hp2] at hv
      interval_cases m <;> norm_num at hpos hm
      all_goals revert hv; decide
    · rw [hp3] at hv
      interval_cases m <;> norm_num at hpos hm
      all_goals revert hv; decide

theorem phi5_irreducible_of_inert {p : ℕ} [Fact p.Prime]
    (hp : InertModFive p) :
    Irreducible (phi5 p) := by
  have hp5 : ¬ p ∣ 5 := by
    intro h
    have heq : p = 5 :=
      (Nat.prime_dvd_prime_iff_eq (show p.Prime from Fact.out) (by norm_num)).mp h
    subst p
    norm_num [InertModFive] at hp
  rw [phi5_eq_cyclotomic]
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hp5
  · exact dvd_refl _
  · rw [natDegree_cyclotomic]
    exact (inertModFive_orderOf_unitOfCoprime hp).symm

theorem map_resultant_eq_zero_of_common_root
    {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) {f g : R[X]} (hf : f.Monic) (hg : g.Monic)
    {x : K} (hfx : (f.map φ).eval x = 0)
    (hgx : (g.map φ).eval x = 0) :
    φ (f.resultant g) = 0 := by
  have hnotcoprime : ¬ IsCoprime (f.map φ) (g.map φ) := by
    intro hcop
    have hne := aeval_ne_zero_of_isCoprime hcop x
    simp only [aeval_def] at hne
    exact hne.elim (fun h => h hfx) (fun h => h hgx)
  have hres : (f.map φ).resultant (g.map φ) = 0 := by
    rw [resultant_eq_zero_iff]
    exact ⟨Or.inl (hf.map φ).ne_zero, hnotcoprime⟩
  rw [← hres]
  simpa only [hf.natDegree_map, hg.natDegree_map] using
    (Polynomial.resultant_map_map (f := f) (g := g)
      (m := f.natDegree) (n := g.natDegree) φ).symm

theorem prime_dvd_resultant_of_common_root
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    [Algebra (ZMod q) K]
    {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic) {x : K}
    (hfx : (f.map ((algebraMap (ZMod q) K).comp
      (Int.castRingHom (ZMod q)))).eval x = 0)
    (hgx : (g.map ((algebraMap (ZMod q) K).comp
      (Int.castRingHom (ZMod q)))).eval x = 0) :
    (q : ℤ) ∣ f.resultant g := by
  have hmap :
      ((algebraMap (ZMod q) K).comp
        (Int.castRingHom (ZMod q))) (f.resultant g) = 0 :=
    map_resultant_eq_zero_of_common_root
      ((algebraMap (ZMod q) K).comp
        (Int.castRingHom (ZMod q))) hf hg hfx hgx
  have hz : ((f.resultant g : ℤ) : ZMod q) = 0 := by
    apply (algebraMap (ZMod q) K).injective
    simpa using hmap
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz

/-- If the reduction of a monic integral polynomial is irreducible and has
the same root as a second polynomial in a field extension of `ZMod q`, then
the full `q ^ deg f` divides their integral resultant.

The proof is coefficient-level.  Irreducibility identifies the reduction of
`f` with the minimal polynomial of the common root.  Thus it divides the
reduction of `g`; equivalently, the integral remainder of `g` modulo `f` is
coefficientwise divisible by `q`.  Resultant invariance under adding a
multiple of `f`, followed by homogeneity in the second input, produces one
factor of `q` for each degree of `f`.-/
theorem prime_pow_natDegree_dvd_resultant_of_common_root
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    [Algebra (ZMod q) K]
    {f g : ℤ[X]} (hf : f.Monic)
    (hfirr : Irreducible (f.map (Int.castRingHom (ZMod q))))
    {x : K}
    (hfx : (f.map ((algebraMap (ZMod q) K).comp
      (Int.castRingHom (ZMod q)))).eval x = 0)
    (hgx : (g.map ((algebraMap (ZMod q) K).comp
      (Int.castRingHom (ZMod q)))).eval x = 0) :
    (q : ℤ) ^ f.natDegree ∣ f.resultant g := by
  let φ : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  let fbar : (ZMod q)[X] := f.map φ
  let gbar : (ZMod q)[X] := g.map φ
  have hfx' : Polynomial.aeval x fbar = 0 := by
    simpa [Polynomial.aeval_def, fbar, φ, eval_map, eval₂_map] using hfx
  have hgx' : Polynomial.aeval x gbar = 0 := by
    simpa [Polynomial.aeval_def, gbar, φ, eval_map, eval₂_map] using hgx
  have hmin : fbar = minpoly (ZMod q) x :=
    minpoly.eq_of_irreducible_of_monic
      (by simpa [fbar, φ] using hfirr) hfx' (hf.map φ)
  have hfdvd : fbar ∣ gbar := by
    rw [hmin]
    exact minpoly.dvd (ZMod q) x hgx'
  let rem : ℤ[X] := g %ₘ f
  let quo : ℤ[X] := g /ₘ f
  have hmaprem : rem.map φ = 0 := by
    rw [show rem.map φ = gbar %ₘ fbar by
      simpa [rem, fbar, gbar] using
        (Polynomial.map_modByMonic φ hf)]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (hf.map φ)).2 hfdvd
  have hC : C (q : ℤ) ∣ rem := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hz : ((rem.coeff i : ℤ) : ZMod q) = 0 := by
      have hc := congrArg (fun P : (ZMod q)[X] => P.coeff i) hmaprem
      simpa [φ] using hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  obtain ⟨scaledRem, hscaledRem⟩ := hC
  let m := f.natDegree
  let n := g.natDegree + f.natDegree
  have hquoDegree : quo.natDegree + m ≤ n := by
    rw [show quo.natDegree = g.natDegree - f.natDegree by
      simpa [quo] using Polynomial.natDegree_divByMonic g hf]
    simp [m, n]
  have hdefault : f.resultant g m n = f.resultant g := by
    simpa [m, n, Polynomial.coeff_natDegree, hf.leadingCoeff] using
      (Polynomial.resultant_add_right_deg
        f g m g.natDegree m (le_refl g.natDegree))
  refine ⟨f.resultant scaledRem m n, ?_⟩
  calc
    f.resultant g = f.resultant g m n := hdefault.symm
    _ = f.resultant (rem + f * quo) m n := by
      rw [Polynomial.modByMonic_add_div]
    _ = f.resultant rem m n :=
      Polynomial.resultant_add_mul_right
        f rem quo m n hquoDegree (le_refl f.natDegree)
    _ = f.resultant (C (q : ℤ) * scaledRem) m n := by rw [hscaledRem]
    _ = (q : ℤ) ^ m * f.resultant scaledRem m n :=
      Polynomial.resultant_C_mul_right f scaledRem m n (q : ℤ)
    _ = (q : ℤ) ^ f.natDegree * f.resultant scaledRem m n := rfl

noncomputable def pureFiberPolynomial (A : ℕ) : ℤ[X] :=
  (X - 1) ^ A - 1

noncomputable def twistedFiberPolynomial (A : ℕ) : ℤ[X] :=
  X * (X - 1) ^ A + 1

lemma pureFiberPolynomial_monic {A : ℕ} (hA : 0 < A) :
    (pureFiberPolynomial A).Monic := by
  unfold pureFiberPolynomial
  let hm : ((X - (1 : ℤ[X])) ^ A).Monic :=
    (monic_X_sub_C (1 : ℤ)).pow A
  have hdeg : ((X - (1 : ℤ[X])) ^ A).natDegree = A := by
    simpa [sub_eq_add_neg] using
      (natDegree_pow_X_add_C (R := ℤ) A (-1))
  apply hm.sub_of_left
  rw [degree_one, degree_eq_natDegree hm.ne_zero, hdeg]
  exact_mod_cast hA

lemma twistedFiberPolynomial_monic (A : ℕ) :
    (twistedFiberPolynomial A).Monic := by
  unfold twistedFiberPolynomial
  let hm : (X * (X - (1 : ℤ[X])) ^ A).Monic :=
    monic_X.mul ((monic_X_sub_C (1 : ℤ)).pow A)
  have hdeg : (X * (X - (1 : ℤ[X])) ^ A).natDegree = A + 1 := by
    have hq : ((X - (1 : ℤ[X])) ^ A).Monic :=
      (monic_X_sub_C (1 : ℤ)).pow A
    have hpdeg : ((X - (1 : ℤ[X])) ^ A).natDegree = A := by
      simpa [sub_eq_add_neg] using
        (natDegree_pow_X_add_C (R := ℤ) A (-1))
    rw [monic_X.natDegree_mul hq, natDegree_X, hpdeg]
    omega
  apply hm.add_of_left
  rw [degree_one, degree_eq_natDegree hm.ne_zero, hdeg]
  exact_mod_cast (Nat.zero_lt_succ A)

lemma intPhi5_monic : (cyclotomic 5 ℤ).Monic :=
  cyclotomic.monic 5 ℤ

lemma intPhi5_map_zmod_five :
    (cyclotomic 5 ℤ).map (Int.castRingHom (ZMod 5)) =
      (X - 1) ^ 4 := by
  rw [map_cyclotomic_int, cyclotomic_prime]
  norm_num [Finset.sum_range_succ]
  have hfour : (4 : ZMod 5) = -1 := by decide
  have hsix : (6 : ZMod 5) = 1 := by decide
  ring_nf
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n <;>
      simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X,
        coeff_one, hfour, hsix]
  · have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X,
      coeff_one, hfour, hsix, hn0, hn2, hn3, Ne.symm hn1]

theorem intPhi5_map_irreducible_of_inert {q : ℕ} [Fact q.Prime]
    (hq : InertModFive q) :
    Irreducible
      ((cyclotomic 5 ℤ).map (Int.castRingHom (ZMod q))) := by
  rw [map_cyclotomic_int, ← phi5_eq_cyclotomic]
  exact phi5_irreducible_of_inert hq

theorem pure_resultant_mod_five_eq_one {A : ℕ} (hA : 0 < A) :
    ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A) : ZMod 5) =
      1 := by
  let φ : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)
  let gbar : (ZMod 5)[X] := (pureFiberPolynomial A).map φ
  have hres :=
    resultant_X_sub_C_pow_left (1 : ZMod 5) gbar 4 gbar.natDegree le_rfl
  have hdegPhi : (cyclotomic 5 ℤ).natDegree = 4 := by
    rw [natDegree_cyclotomic]
    decide
  have hdegG :
      gbar.natDegree = (pureFiberPolynomial A).natDegree := by
    simpa [gbar] using
      (pureFiberPolynomial_monic hA).natDegree_map φ
  rw [hdegG] at hres
  have heval : eval 1 gbar = (-1 : ZMod 5) := by
    simp [gbar, pureFiberPolynomial, hA.ne']
  have hpure : ((-1 : ZMod 5) ^ 4) = 1 := by decide
  rw [heval, hpure] at hres
  change φ ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A)) = 1
  rw [← resultant_map_map]
  rw [intPhi5_map_zmod_five]
  simpa [gbar, pureFiberPolynomial, hdegPhi, hA.ne', C_1] using hres

theorem twisted_resultant_mod_five_eq_one (A : ℕ) :
    ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A) : ZMod 5) =
      1 := by
  let φ : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)
  let gbar : (ZMod 5)[X] := (twistedFiberPolynomial A).map φ
  have hres :=
    resultant_X_sub_C_pow_left (1 : ZMod 5) gbar 4 gbar.natDegree le_rfl
  have hdegPhi : (cyclotomic 5 ℤ).natDegree = 4 := by
    rw [natDegree_cyclotomic]
    decide
  have hdegG :
      gbar.natDegree = (twistedFiberPolynomial A).natDegree := by
    simpa [gbar] using
      (twistedFiberPolynomial_monic A).natDegree_map φ
  rw [hdegG] at hres
  have heval : eval 1 gbar = (0 : ZMod 5) ^ A + 1 := by
    simp [gbar, twistedFiberPolynomial]
  have htwisted : (((0 : ZMod 5) ^ A + 1) ^ 4) = 1 := by
    cases A with
    | zero => decide
    | succ A => simp
  rw [heval, htwisted] at hres
  change φ ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A)) = 1
  rw [← resultant_map_map]
  rw [intPhi5_map_zmod_five]
  simpa [gbar, twistedFiberPolynomial, hdegPhi, C_1] using hres

/-- The pure resultant is a nonzero integer for every positive fiber
exponent.  In fact, its reduction modulo `5` is `1`.-/
theorem pure_resultant_ne_zero {A : ℕ} (hA : 0 < A) :
    (cyclotomic 5 ℤ).resultant (pureFiberPolynomial A) ≠ 0 := by
  intro hzero
  have hmod := pure_resultant_mod_five_eq_one hA
  rw [hzero] at hmod
  exact zero_ne_one hmod

/-- The twisted resultant is a nonzero integer for every fiber exponent.-/
theorem twisted_resultant_ne_zero (A : ℕ) :
    (cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A) ≠ 0 := by
  intro hzero
  have hmod := twisted_resultant_mod_five_eq_one A
  rw [hzero] at hmod
  exact zero_ne_one hmod

theorem intPhi5_eval_zeta_of_inert {q : ℕ} [Fact q.Prime]
    (hq : InertModFive q) :
    letI : Fact (Irreducible (phi5 q)) :=
      ⟨phi5_irreducible_of_inert hq⟩
    ((cyclotomic 5 ℤ).map
      ((algebraMap (ZMod q) (Phi5Ring q)).comp
        (Int.castRingHom (ZMod q)))).eval zeta5 = 0 := by
  dsimp
  rw [eval_map, ← eval₂_map]
  change Polynomial.aeval (zeta5 : Phi5Ring q)
    ((cyclotomic 5 ℤ).map (Int.castRingHom (ZMod q))) = 0
  rw [map_cyclotomic_int, ← phi5_eq_cyclotomic]
  unfold zeta5
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self (f := phi5 q)

theorem pureFiberPolynomial_eval_zeta {q A : ℕ} [Fact q.Prime] :
    ((pureFiberPolynomial A).map
      ((algebraMap (ZMod q) (Phi5Ring q)).comp
        (Int.castRingHom (ZMod q)))).eval zeta5
      = ((zeta5 : Phi5Ring q) - 1) ^ A - 1 := by
  simp [pureFiberPolynomial]

theorem twistedFiberPolynomial_eval_zeta {q A : ℕ} [Fact q.Prime] :
    ((twistedFiberPolynomial A).map
      ((algebraMap (ZMod q) (Phi5Ring q)).comp
        (Int.castRingHom (ZMod q)))).eval zeta5
      = (zeta5 : Phi5Ring q) * ((zeta5 : Phi5Ring q) - 1) ^ A + 1 := by
  simp [twistedFiberPolynomial]

lemma ne_five_of_inertModFive {q : ℕ} (hq : InertModFive q) : q ≠ 5 := by
  intro h
  subst q
  norm_num [InertModFive] at hq

theorem pure_row_power {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q) (hres : (A + 1) % 5 = 1)
    (hrow : LocalS5 q (A + 1)) :
    ((zeta5 : Phi5Ring q) - 1) ^ A = 1 := by
  have hq5 : q ≠ 5 := ne_five_of_inertModFive hq
  let u : (Phi5Ring q)ˣ :=
    localCyclotomicUnit hq5 (1 : (ZMod 5)ˣ)
  have hunitEq : u ^ (A + 1) = u := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, u, localCyclotomicUnit_val,
      zmodFiveUnitOne_val, pow_one]
    calc
      ((zeta5 : Phi5Ring q) - 1) ^ (A + 1)
          = zeta5 ^ (A + 1) - 1 := hrow
      _ = zeta5 ^ ((A + 1) % 5) - 1 :=
        congrArg (fun x : Phi5Ring q => x - 1)
          (zeta5_pow_mod (p := q) (A + 1))
      _ = zeta5 - 1 := by rw [hres]; simp
  have huA : u ^ A = 1 := by
    apply mul_right_cancel (b := u)
    simpa [pow_succ] using hunitEq
  have hval := congrArg Units.val huA
  simp only [Units.val_pow_eq_pow_val, Units.val_one, u,
    localCyclotomicUnit_val] at hval
  have hone : (1 : ZMod 5).val = 1 := by decide
  rw [hone] at hval
  simpa using hval

theorem twisted_row_vanishing {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q) (hres : (A + 1) % 5 = 4)
    (hrow : LocalS5 q (A + 1)) :
    (zeta5 : Phi5Ring q) * ((zeta5 : Phi5Ring q) - 1) ^ A + 1 = 0 := by
  let z : Phi5Ring q := zeta5
  change z * (z - 1) ^ A + 1 = 0
  have hq5 : q ≠ 5 := ne_five_of_inertModFive hq
  let u : (Phi5Ring q)ˣ :=
    localCyclotomicUnit hq5 (1 : (ZMod 5)ˣ)
  have huval :
      (u : Phi5Ring q) = z - 1 := by
    simp only [u, localCyclotomicUnit_val]
    have hone : (((1 : (ZMod 5)ˣ) : ZMod 5)).val = 1 := by decide
    rw [hone, pow_one]
  have hrow' :
      (z - 1) ^ (A + 1) = z ^ 4 - 1 := by
    calc
      (z - 1) ^ (A + 1) = z ^ (A + 1) - 1 := by
        simpa [LocalS5, z] using hrow
      _ = z ^ ((A + 1) % 5) - 1 :=
        congrArg (fun x : Phi5Ring q => x - 1)
          (by simpa [z] using (zeta5_pow_mod (p := q) (A + 1)))
      _ = z ^ 4 - 1 := by rw [hres]
  have hmul :
      (z - 1) * (z * (z - 1) ^ A + 1) = 0 := by
    calc
      (z - 1) * (z * (z - 1) ^ A + 1)
          = z * (z - 1) ^ (A + 1) + (z - 1) := by
              rw [pow_succ]
              ring
      _ = z * (z ^ 4 - 1) + (z - 1) := by rw [hrow']
      _ = 0 := by
        have hz5 : z ^ 5 = 1 := by simpa [z] using (zeta5_pow_five (p := q))
        rw [mul_sub, ← pow_succ', hz5]
        ring
  calc
    z * (z - 1) ^ A + 1
        = (↑u⁻¹ : Phi5Ring q)
            * ((z - 1) * (z * (z - 1) ^ A + 1)) := by
              rw [← huval]
              simp
    _ = 0 := by rw [hmul, mul_zero]

theorem pure_row_dvd_resultant {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q) (hA : 0 < A)
    (hres : (A + 1) % 5 = 1) (hrow : LocalS5 q (A + 1)) :
    (q : ℤ) ∣ (cyclotomic 5 ℤ).resultant (pureFiberPolynomial A) := by
  letI : Fact (Irreducible (phi5 q)) :=
    ⟨phi5_irreducible_of_inert hq⟩
  apply prime_dvd_resultant_of_common_root
    intPhi5_monic (pureFiberPolynomial_monic hA)
      (x := (zeta5 : Phi5Ring q))
  · exact intPhi5_eval_zeta_of_inert hq
  · rw [pureFiberPolynomial_eval_zeta,
      pure_row_power hq hres hrow, sub_self]

theorem twisted_row_dvd_resultant {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q)
    (hres : (A + 1) % 5 = 4) (hrow : LocalS5 q (A + 1)) :
    (q : ℤ) ∣ (cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A) := by
  letI : Fact (Irreducible (phi5 q)) :=
    ⟨phi5_irreducible_of_inert hq⟩
  apply prime_dvd_resultant_of_common_root
    intPhi5_monic (twistedFiberPolynomial_monic A)
      (x := (zeta5 : Phi5Ring q))
  · exact intPhi5_eval_zeta_of_inert hq
  · rw [twistedFiberPolynomial_eval_zeta,
      twisted_row_vanishing hq hres hrow]

/-- The full inert-degree contribution for the pure final row:
the quartic cyclotomic factor forces `q^4`, not merely `q`, to divide the
explicit integer resultant.-/
theorem pure_row_pow_four_dvd_resultant {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q)
    (hres : (A + 1) % 5 = 1) (hrow : LocalS5 q (A + 1)) :
    (q : ℤ) ^ 4 ∣
      (cyclotomic 5 ℤ).resultant (pureFiberPolynomial A) := by
  letI : Fact (Irreducible (phi5 q)) :=
    ⟨phi5_irreducible_of_inert hq⟩
  have hpow :=
    prime_pow_natDegree_dvd_resultant_of_common_root
      intPhi5_monic (intPhi5_map_irreducible_of_inert hq)
      (x := (zeta5 : Phi5Ring q))
      (intPhi5_eval_zeta_of_inert hq)
      (by rw [pureFiberPolynomial_eval_zeta,
          pure_row_power hq hres hrow, sub_self])
  have htot : Nat.totient 5 = 4 := by decide
  simpa [natDegree_cyclotomic, htot] using hpow

/-- The full inert-degree contribution for the twisted final row.-/
theorem twisted_row_pow_four_dvd_resultant {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q)
    (hres : (A + 1) % 5 = 4) (hrow : LocalS5 q (A + 1)) :
    (q : ℤ) ^ 4 ∣
      (cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A) := by
  letI : Fact (Irreducible (phi5 q)) :=
    ⟨phi5_irreducible_of_inert hq⟩
  have hpow :=
    prime_pow_natDegree_dvd_resultant_of_common_root
      intPhi5_monic (intPhi5_map_irreducible_of_inert hq)
      (x := (zeta5 : Phi5Ring q))
      (intPhi5_eval_zeta_of_inert hq)
      (by rw [twistedFiberPolynomial_eval_zeta,
          twisted_row_vanishing hq hres hrow])
  have htot : Nat.totient 5 = 4 := by decide
  simpa [natDegree_cyclotomic, htot] using hpow

/-- A pure final row at positive exponent gives a finite size trap:
`q^4` is bounded by the absolute value of the fixed nonzero resultant.-/
theorem pure_row_pow_four_le_resultant_natAbs {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q) (hA : 0 < A)
    (hres : (A + 1) % 5 = 1) (hrow : LocalS5 q (A + 1)) :
    q ^ 4 ≤
      Int.natAbs
        ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A)) := by
  have hle :=
    Int.natAbs_le_of_dvd_ne_zero
      (pure_row_pow_four_dvd_resultant hq hres hrow)
      (pure_resultant_ne_zero hA)
  simpa [Int.natAbs_pow] using hle

/-- The corresponding finite size trap in the twisted branch.-/
theorem twisted_row_pow_four_le_resultant_natAbs {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q)
    (hres : (A + 1) % 5 = 4) (hrow : LocalS5 q (A + 1)) :
    q ^ 4 ≤
      Int.natAbs
        ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A)) := by
  have hle :=
    Int.natAbs_le_of_dvd_ne_zero
      (twisted_row_pow_four_dvd_resultant hq hres hrow)
      (twisted_resultant_ne_zero A)
  simpa [Int.natAbs_pow] using hle

/-! ## The explicit archimedean bound

The fixed-resultant trap above is already enough for pointwise finiteness.
The following section proves the sharper paper bound

`natAbs resultant ≤ 16 * 5 ^ A`.

The proof is intrinsic.  Every complex root `z` of `Φ₅` is primitive, hence
has norm one.  Its distance from `1` is at least one, and the product of the
four distances is exactly `5`.  Each pure or twisted fiber value is therefore
at most twice the corresponding `A`-th power of that distance.  Multiplying
over the four roots gives `2^4 * 5^A`.
-/

/-- Every primitive fifth root of unity is at complex distance at least one
from `1`.  The proof uses only the fifth cyclotomic equation and the identity
for the squared complex norm.-/
lemma norm_sub_one_one_le_of_isPrimitiveRoot_five
    {z : ℂ} (hz : IsPrimitiveRoot z 5) :
    1 ≤ ‖z - 1‖ := by
  have hnorm : ‖z‖ = 1 := hz.norm'_eq_one (by norm_num)
  have hpow5 : z ^ 5 = 1 := hz.pow_eq_one
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hpow5
    exact zero_ne_one hpow5
  have hconj : conj z = z⁻¹ := by
    exact (Complex.inv_eq_conj hnorm).symm
  have hz4inv : z ^ 4 = z⁻¹ := by
    have hmul : z ^ 4 * z = 1 := by
      simpa [pow_succ] using hpow5
    have h := (eq_mul_inv_iff_mul_eq₀ hz0).2 hmul
    simpa using h
  have hz4 : z ^ 4 = conj z := hz4inv.trans hconj.symm
  have hz3inv : z ^ 3 = (z ^ 2)⁻¹ := by
    have hmul : z ^ 3 * z ^ 2 = 1 := by
      simpa [← pow_add] using hpow5
    have h := (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hz0)).2 hmul
    simpa using h
  have hz3 : z ^ 3 = conj (z ^ 2) := by
    rw [hz3inv, Complex.inv_eq_conj]
    rw [norm_pow, hnorm, one_pow]
  have hroot : eval z (cyclotomic 5 ℂ) = 0 := by
    exact hz.isRoot_cyclotomic (by norm_num)
  rw [cyclotomic_prime] at hroot
  norm_num [Finset.sum_range_succ] at hroot
  have hre : 4 * z.re ^ 2 + 2 * z.re - 1 = 0 := by
    have hnormsq : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
          rw [Complex.normSq_apply]
          ring
        _ = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
        _ = 1 := by rw [hnorm]; norm_num
    have hrootre := congrArg Complex.re hroot
    rw [hz4, hz3] at hrootre
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re,
      Complex.conj_re, pow_two, Complex.mul_re] at hrootre
    nlinarith
  have hzre : z.re ≤ 1 / 2 := by
    by_contra h
    have hgt : 1 / 2 < z.re := lt_of_not_ge h
    nlinarith [sq_nonneg (z.re - 1 / 2)]
  have hsquare := Complex.norm_sub_one_sq_eq_of_norm_eq_one hnorm
  have hone_sq : 1 ^ 2 ≤ ‖z - 1‖ ^ 2 := by
    rw [hsquare]
    nlinarith
  nlinarith [norm_nonneg (z - 1)]

/-- After embedding into `ℂ`, the integral resultant is the product of the
values of the second polynomial over the four complex roots of `Φ₅`.-/
lemma complex_cast_resultant_eq_prod_eval (g : ℤ[X]) :
    (((cyclotomic 5 ℤ).resultant g : ℤ) : ℂ) =
      (((cyclotomic 5 ℂ).roots.map
        fun z => eval z (g.map (Int.castRingHom ℂ))).prod) := by
  let φ : ℤ →+* ℂ := Int.castRingHom ℂ
  have hφinj : Function.Injective φ := Int.cast_injective
  have hsplit : (cyclotomic 5 ℂ).Splits := IsAlgClosed.splits _
  have hprod :=
    Polynomial.resultant_eq_prod_eval
      (cyclotomic 5 ℂ) (g.map φ) (g.map φ).natDegree le_rfl hsplit
  have hlead : (cyclotomic 5 ℂ).leadingCoeff = 1 :=
    (cyclotomic.monic 5 ℂ).leadingCoeff
  rw [hlead, one_pow, one_mul] at hprod
  change φ ((cyclotomic 5 ℤ).resultant g) = _
  rw [← Polynomial.resultant_map_map]
  rw [map_cyclotomic_int]
  simpa [φ, natDegree_cyclotomic,
    natDegree_map_eq_of_injective hφinj] using hprod

lemma intPhi5_resultant_X_sub_one :
    (cyclotomic 5 ℤ).resultant (X - 1) = 5 := by
  have hdeg : (cyclotomic 5 ℤ).natDegree = 4 := by
    rw [natDegree_cyclotomic]
    decide
  have hgdeg : (X - (1 : ℤ[X])).natDegree = 1 := by
    change (X - C (1 : ℤ)).natDegree = 1
    rw [natDegree_X_sub_C]
  have heval : eval (1 : ℤ) (cyclotomic 5 ℤ) = 5 := by
    rw [cyclotomic_prime]
    norm_num [Finset.sum_range_succ]
  change
    (cyclotomic 5 ℤ).resultant (X - 1)
      (cyclotomic 5 ℤ).natDegree (X - (1 : ℤ[X])).natDegree = 5
  rw [hdeg, hgdeg]
  change
    (cyclotomic 5 ℤ).resultant (X - C (1 : ℤ)) 4 1 = 5
  rw [Polynomial.resultant_X_sub_C_right, heval]
  all_goals norm_num [hdeg]

/-- The product of the distances of the four primitive fifth roots from
`1` is exactly `5`.-/
lemma prod_norm_sub_one_roots_cyclotomic_five :
    (((cyclotomic 5 ℂ).roots.map fun z => ‖z - 1‖).prod) = 5 := by
  have hprod :=
    complex_cast_resultant_eq_prod_eval (X - 1 : ℤ[X])
  rw [intPhi5_resultant_X_sub_one] at hprod
  have hnorm := congrArg norm hprod
  have hnormprod :
      ‖((cyclotomic 5 ℂ).roots.map fun z => z - 1).prod‖ =
        (((cyclotomic 5 ℂ).roots.map fun z => ‖z - 1‖).prod) := by
    change
      normHom (((cyclotomic 5 ℂ).roots.map fun z => z - 1).prod) = _
    rw [map_multiset_prod, Multiset.map_map]
    simp [Function.comp_apply]
  rw [show
    ((cyclotomic 5 ℂ).roots.map
      fun z => eval z ((X - 1 : ℤ[X]).map (Int.castRingHom ℂ))).prod =
      ((cyclotomic 5 ℂ).roots.map fun z => z - 1).prod by
        congr 1
        apply Multiset.map_congr rfl
        intro z hz
        simp] at hnorm
  rw [hnormprod] at hnorm
  norm_num at hnorm
  exact hnorm.symm

lemma multiset_prod_map_le_prod_map
    {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      apply mul_le_mul
      · exact hfg a (by simp)
      · exact ih
          (fun x hx => hf x (by simp [hx]))
          (fun x hx => hg x (by simp [hx]))
          (fun x hx => hfg x (by simp [hx]))
      · exact Multiset.prod_nonneg fun y hy => by
          obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
          exact hf x (by simp [hx])
      · exact hg a (by simp)

lemma root_of_cyclotomic_five_isPrimitive
    {z : ℂ} (hz : z ∈ (cyclotomic 5 ℂ).roots) :
    IsPrimitiveRoot z 5 := by
  rw [← isRoot_cyclotomic_iff (R := ℂ)]
  rw [← mem_roots (cyclotomic_ne_zero 5 ℂ)]
  exact hz

lemma pure_root_product_norm_le (A : ℕ) :
    (((cyclotomic 5 ℂ).roots.map
      fun z => ‖(z - 1) ^ A - 1‖).prod) ≤
        16 * 5 ^ A := by
  let s := (cyclotomic 5 ℂ).roots
  have hpoint :
      ∀ z ∈ s, ‖(z - 1) ^ A - 1‖ ≤ 2 * ‖z - 1‖ ^ A := by
    intro z hz
    have hbase : 1 ≤ ‖z - 1‖ :=
      norm_sub_one_one_le_of_isPrimitiveRoot_five
        (root_of_cyclotomic_five_isPrimitive hz)
    have hpowbase : 1 ≤ ‖z - 1‖ ^ A := one_le_pow₀ hbase
    calc
      ‖(z - 1) ^ A - 1‖
          ≤ ‖(z - 1) ^ A‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z - 1‖ ^ A + 1 := by rw [norm_pow, norm_one]
      _ ≤ 2 * ‖z - 1‖ ^ A := by linarith
  calc
    (s.map fun z => ‖(z - 1) ^ A - 1‖).prod
        ≤ (s.map fun z => 2 * ‖z - 1‖ ^ A).prod :=
          multiset_prod_map_le_prod_map s _ _
            (fun z hz => norm_nonneg _)
            (fun z hz => mul_nonneg (by norm_num) (pow_nonneg (norm_nonneg _) _))
            hpoint
    _ = 2 ^ s.card * ((s.map fun z => ‖z - 1‖).prod) ^ A := by
      rw [Multiset.prod_map_mul, Multiset.prod_map_pow]
      simp
    _ = 16 * 5 ^ A := by
      have hcard : s.card = 4 := by
        dsimp [s]
        rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_cyclotomic]
        decide
      rw [hcard, prod_norm_sub_one_roots_cyclotomic_five]
      norm_num

lemma twisted_root_product_norm_le (A : ℕ) :
    (((cyclotomic 5 ℂ).roots.map
      fun z => ‖z * (z - 1) ^ A + 1‖).prod) ≤
        16 * 5 ^ A := by
  let s := (cyclotomic 5 ℂ).roots
  have hpoint :
      ∀ z ∈ s, ‖z * (z - 1) ^ A + 1‖ ≤ 2 * ‖z - 1‖ ^ A := by
    intro z hz
    have hzprim := root_of_cyclotomic_five_isPrimitive hz
    have hznorm : ‖z‖ = 1 := hzprim.norm'_eq_one (by norm_num)
    have hbase : 1 ≤ ‖z - 1‖ :=
      norm_sub_one_one_le_of_isPrimitiveRoot_five hzprim
    have hpowbase : 1 ≤ ‖z - 1‖ ^ A := one_le_pow₀ hbase
    calc
      ‖z * (z - 1) ^ A + 1‖
          ≤ ‖z * (z - 1) ^ A‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖z - 1‖ ^ A + 1 := by
        rw [norm_mul, hznorm, one_mul, norm_pow, norm_one]
      _ ≤ 2 * ‖z - 1‖ ^ A := by linarith
  calc
    (s.map fun z => ‖z * (z - 1) ^ A + 1‖).prod
        ≤ (s.map fun z => 2 * ‖z - 1‖ ^ A).prod :=
          multiset_prod_map_le_prod_map s _ _
            (fun z hz => norm_nonneg _)
            (fun z hz => mul_nonneg (by norm_num) (pow_nonneg (norm_nonneg _) _))
            hpoint
    _ = 2 ^ s.card * ((s.map fun z => ‖z - 1‖).prod) ^ A := by
      rw [Multiset.prod_map_mul, Multiset.prod_map_pow]
      simp
    _ = 16 * 5 ^ A := by
      have hcard : s.card = 4 := by
        dsimp [s]
        rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_cyclotomic]
        decide
      rw [hcard, prod_norm_sub_one_roots_cyclotomic_five]
      norm_num

lemma norm_intCast_complex_eq_natAbs (z : ℤ) :
    ‖(z : ℂ)‖ = (Int.natAbs z : ℝ) := by
  simp

/-- Closed-form archimedean estimate for the pure resultant.-/
theorem pure_resultant_natAbs_le (A : ℕ) :
    Int.natAbs
        ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A))
      ≤ 16 * 5 ^ A := by
  have hprod :=
    complex_cast_resultant_eq_prod_eval (pureFiberPolynomial A)
  have hnorm := congrArg norm hprod
  have hevals :
      ((cyclotomic 5 ℂ).roots.map fun z =>
        eval z ((pureFiberPolynomial A).map (Int.castRingHom ℂ))).prod =
      ((cyclotomic 5 ℂ).roots.map fun z =>
        (z - 1) ^ A - 1).prod := by
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    simp [pureFiberPolynomial]
  rw [hevals] at hnorm
  have hnormprod :
      ‖((cyclotomic 5 ℂ).roots.map fun z =>
          (z - 1) ^ A - 1).prod‖ =
        ((cyclotomic 5 ℂ).roots.map fun z =>
          ‖(z - 1) ^ A - 1‖).prod := by
    change (normHom : ℂ →*₀ ℝ) _ = _
    rw [map_multiset_prod, Multiset.map_map]
    simp [Function.comp_apply]
  rw [norm_intCast_complex_eq_natAbs, hnormprod] at hnorm
  have hreal :
      (Int.natAbs
          ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A)) : ℝ)
        ≤ (16 * 5 ^ A : ℕ) := by
    calc
      (Int.natAbs
          ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A)) : ℝ)
          = ((cyclotomic 5 ℂ).roots.map fun z =>
              ‖(z - 1) ^ A - 1‖).prod := hnorm
      _ ≤ ((16 * 5 ^ A : ℕ) : ℝ) := by
        have hcast :
            (16 : ℝ) * (5 : ℝ) ^ A =
              ((16 * 5 ^ A : ℕ) : ℝ) := by norm_cast
        exact (pure_root_product_norm_le A).trans_eq hcast
  exact_mod_cast hreal

/-- Closed-form archimedean estimate for the twisted resultant.-/
theorem twisted_resultant_natAbs_le (A : ℕ) :
    Int.natAbs
        ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A))
      ≤ 16 * 5 ^ A := by
  have hprod :=
    complex_cast_resultant_eq_prod_eval (twistedFiberPolynomial A)
  have hnorm := congrArg norm hprod
  have hevals :
      ((cyclotomic 5 ℂ).roots.map fun z =>
        eval z ((twistedFiberPolynomial A).map (Int.castRingHom ℂ))).prod =
      ((cyclotomic 5 ℂ).roots.map fun z =>
        z * (z - 1) ^ A + 1).prod := by
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    simp [twistedFiberPolynomial]
  rw [hevals] at hnorm
  have hnormprod :
      ‖((cyclotomic 5 ℂ).roots.map fun z =>
          z * (z - 1) ^ A + 1).prod‖ =
        ((cyclotomic 5 ℂ).roots.map fun z =>
          ‖z * (z - 1) ^ A + 1‖).prod := by
    change (normHom : ℂ →*₀ ℝ) _ = _
    rw [map_multiset_prod, Multiset.map_map]
    simp [Function.comp_apply]
  rw [norm_intCast_complex_eq_natAbs, hnormprod] at hnorm
  have hreal :
      (Int.natAbs
          ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A)) : ℝ)
        ≤ (16 * 5 ^ A : ℕ) := by
    calc
      (Int.natAbs
          ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A)) : ℝ)
          = ((cyclotomic 5 ℂ).roots.map fun z =>
              ‖z * (z - 1) ^ A + 1‖).prod := hnorm
      _ ≤ ((16 * 5 ^ A : ℕ) : ℝ) := by
        have hcast :
            (16 : ℝ) * (5 : ℝ) ^ A =
              ((16 * 5 ^ A : ℕ) : ℝ) := by norm_cast
        exact (twisted_root_product_norm_le A).trans_eq hcast
  exact_mod_cast hreal

/-- A literal pure final row satisfies the fully explicit fourth-power
bound used in the finite-fiber theorem.-/
theorem pure_row_pow_four_le_sixteen_mul_five_pow
    {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q) (hA : 0 < A)
    (hres : (A + 1) % 5 = 1) (hrow : LocalS5 q (A + 1)) :
    q ^ 4 ≤ 16 * 5 ^ A :=
  (pure_row_pow_four_le_resultant_natAbs hq hA hres hrow).trans
    (pure_resultant_natAbs_le A)

/-- The corresponding explicit fourth-power bound in the twisted branch.-/
theorem twisted_row_pow_four_le_sixteen_mul_five_pow
    {q A : ℕ} [Fact q.Prime]
    (hq : InertModFive q)
    (hres : (A + 1) % 5 = 4) (hrow : LocalS5 q (A + 1)) :
    q ^ 4 ≤ 16 * 5 ^ A :=
  (twisted_row_pow_four_le_resultant_natAbs hq hres hrow).trans
    (twisted_resultant_natAbs_le A)

end AgrawalCore
