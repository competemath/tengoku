/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import Tengoku.LeanPool.LeanPool.Nivat.Core.Basic
public import Tengoku

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Laurent polynomial operators

This module implements the notation of Section 1.1. `Laurent` is the rational
Laurent ring, `act` is its forward-shift action, and `lineEval` substitutes a
lattice monomial into an ordinary polynomial.

The principal identities are `act_apply`, `act_mul`, `act_difference`, and
`act_lineEval_X_pow_sub_one`. The theorem `finiteRange_act` verifies that the
class of finite-range rational configurations is closed under every operator.
-/

@[expose] public section

namespace Nivat

/-- Section 1.1 (Notation): the rational Laurent polynomial ring on the full integer lattice. -/
abbrev Laurent := AddMonoidAlgebra ℚ Lattice

namespace Algebra

/-- Section 1.1 (Notation): a forward lattice translation as a rational linear endomorphism. -/
def shiftLinear (h : Lattice) : Module.End ℚ (Configuration ℚ) where
  toFun := shift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Section 1.1 (Notation): the bundled translation evaluates to the forward shift.
@isnad1 id=eq.0h2v.s6.b07233bebecb from=translated src=- shape=07ec0594 vocab=854ea06a
-/
@[simp] theorem shiftLinear_apply (h : Lattice) (c : Configuration ℚ) :
    shiftLinear h c = shift h c := rfl

/-- Section 1.1 (Notation): the additive lattice acts on configurations by commuting forward
shifts. -/
def shiftRepresentation : Multiplicative Lattice →* Module.End ℚ (Configuration ℚ) where
  toFun h := shiftLinear h.toAdd
  map_one' := by ext c z; simp [shiftLinear, shift]
  map_mul' h t := by
    ext c z
    change c (z + (h.toAdd + t.toAdd)) = c ((z + h.toAdd) + t.toAdd)
    rw [add_assoc]

/-- Section 1.1 (Notation): the algebra homomorphism extending lattice translations to Laurent
filters. -/
noncomputable def actionHom : Laurent →ₐ[ℚ] Module.End ℚ (Configuration ℚ) :=
  AddMonoidAlgebra.lift ℚ (Module.End ℚ (Configuration ℚ)) Lattice shiftRepresentation

/-- Section 1.1 (Notation): the finite Laurent polynomial operator applied to a rational
configuration. -/
noncomputable def act (f : Laurent) (c : Configuration ℚ) : Configuration ℚ :=
  actionHom f c

/-- Section 1.1 (Notation): the operator is the finite sum of coefficients times forward-shifted
values.
@isnad1 id=eq.0h3v.s5.4e214318837f from=translated src=- shape=07f25c61 vocab=c73b7396
-/
theorem act_apply (f : Laurent) (c : Configuration ℚ) (z : Lattice) :
    act f c z = f.coeff.sum (fun h a => a * c (z + h)) := by
  classical
  simp [act, actionHom, AddMonoidAlgebra.lift_apply, Finsupp.sum,
    shiftRepresentation, shiftLinear, shift, Finset.sum_apply]

/-- Section 1.1 (Notation): the zero filter sends every configuration to zero.
@isnad1 id=eq.0h1v.s5.5f7c25f89c1c from=translated src=- shape=62da6f45 vocab=1e8a7fba
-/
@[simp] theorem act_zero (c : Configuration ℚ) : act 0 c = 0 := by
  simp [act]

/-- Section 1.1 (Notation): the constant filter one acts as the identity.
@isnad1 id=eq.0h1v.s4.33cfafa3729e from=translated src=- shape=330166a7 vocab=1e8a7fba
-/
@[simp] theorem act_one (c : Configuration ℚ) : act 1 c = c := by
  simp [act]

/-- Section 1.1 (Notation): adding filters adds their outputs.
@isnad1 id=eq.0h3v.s5.a8b9f0e75b6a from=translated src=- shape=15a46cae vocab=14bb63a3
-/
theorem act_add (f g : Laurent) (c : Configuration ℚ) :
    act (f + g) c = act f c + act g c := by
  simp [act]

/-- Section 1.1 (Notation): multiplying filters composes their operators.
@isnad1 id=eq.0h3v.s5.2228da3b72a6 from=translated src=- shape=e7cee0e0 vocab=8d6d62c5
-/
theorem act_mul (f g : Laurent) (c : Configuration ℚ) :
    act (f * g) c = act f (act g c) := by
  simp [act, Module.End.mul_apply]

/-- Section 1.1 (Notation): subtracting filters subtracts their outputs.
@isnad1 id=eq.0h3v.s5.b8c134951490 from=translated src=- shape=15a46cae vocab=43111728
-/
theorem act_sub (f g : Laurent) (c : Configuration ℚ) :
    act (f - g) c = act f c - act g c := by
  simp [act]

/-- Section 1.1 (Notation): negating a filter negates its output.
@isnad1 id=eq.0h2v.s5.0c5cf1a0f278 from=translated src=- shape=d5b31cf1 vocab=45e5b21e
-/
theorem act_neg (f : Laurent) (c : Configuration ℚ) : act (-f) c = -act f c := by
  simp [act]

/-- Section 1.1 (Notation): every Laurent filter annihilates the zero configuration.
@isnad1 id=eq.0h1v.s5.bcc5a9a3bc4d from=translated src=- shape=1971634a vocab=56720138
-/
@[simp] theorem act_config_zero (f : Laurent) : act f 0 = 0 := by
  exact map_zero (actionHom f)

/-- Section 1.1 (Notation): each Laurent operator preserves sums of configurations.
@isnad1 id=eq.0h3v.s5.80830ea4cd96 from=translated src=- shape=ec118bcd vocab=0fb9a1e9
-/
theorem act_config_add (f : Laurent) (c d : Configuration ℚ) :
    act f (c + d) = act f c + act f d := by
  exact map_add (actionHom f) c d

/-- Section 1.1 (Notation): each Laurent operator preserves differences of configurations.
@isnad1 id=eq.0h3v.s5.84b06b3b4f43 from=translated src=- shape=ec118bcd vocab=d67fabdd
-/
theorem act_config_sub (f : Laurent) (c d : Configuration ℚ) :
    act f (c - d) = act f c - act f d := by
  exact map_sub (actionHom f) c d

/-- Section 1.1 (Notation): each Laurent operator commutes with rational scaling of the
configuration.
@isnad1 id=eq.0h3v.s5.9487b0e74b15 from=translated src=- shape=774de2b6 vocab=bf71f84e
-/
theorem act_config_smul (f : Laurent) (a : ℚ) (c : Configuration ℚ) :
    act f (a • c) = a • act f c := by
  exact map_smul (actionHom f) a c

/-- Section 1.1 (Notation): rational scaling of the filter scales its output.
@isnad1 id=eq.0h3v.s6.c4dfb200e5e7 from=translated src=- shape=32293d20 vocab=7388a8ca
-/
theorem act_smul (a : ℚ) (f : Laurent) (c : Configuration ℚ) :
    act (a • f) c = a • act f c := by
  simp [act]

/-- Section 1.1 (Notation): a single supported coefficient acts by scaling a forward shift.
@isnad1 id=eq.0h3v.s5.40466a73785d from=translated src=- shape=68d918f6 vocab=483dbc66
-/
@[simp] theorem act_single (h : Lattice) (a : ℚ) (c : Configuration ℚ) :
    act (AddMonoidAlgebra.single h a) c = a • shift h c := by
  simp [act, actionHom, shiftRepresentation, shiftLinear]

/-- Section 1.1 (Notation): the lattice monomial with exponent `h` and coefficient one. -/
noncomputable def monomial (h : Lattice) : Laurent := AddMonoidAlgebra.single h 1

/-- Section 1.1 (Notation): the zero-exponent monomial is the multiplicative identity.
@isnad1 id=eq.0h0v.s5.950c63cfe6b2 from=translated src=- shape=1ac31801 vocab=e70a8e74
-/
@[simp] theorem monomial_zero : monomial 0 = 1 := rfl

/-- Section 1.1 (Notation): multiplication of lattice monomials adds their exponents.
@isnad1 id=eq.0h2v.s5.17e558d39900 from=translated src=- shape=a7d54e89 vocab=3142e532
-/
@[simp] theorem monomial_mul (h t : Lattice) :
    monomial h * monomial t = monomial (h + t) := by
  simp [monomial]

/-- Section 1.1 (Notation): a natural power of a monomial scales its exponent.
@isnad1 id=eq.0h2v.s5.b6adde2ddbfb from=translated src=- shape=6047f7c8 vocab=4a133bd7
-/
@[simp] theorem monomial_pow (h : Lattice) (q : ℕ) :
    monomial h ^ q = monomial (q • h) := by
  simp [monomial, AddMonoidAlgebra.single_pow]

/-- Section 1.1 (Notation): every lattice monomial is a unit, with inverse at the negated
exponent.
@isnad1 id=isunit.0h1v.s4.08649b630ae6 from=translated src=- shape=1a6c1393 vocab=ee20400c
-/
theorem monomial_isUnit (h : Lattice) : IsUnit (monomial h) := by
  exact ⟨⟨monomial h, monomial (-h), by simp, by simp⟩, rfl⟩

/-- Section 1.1 (Notation): a lattice monomial has a nonzero coefficient and is nonzero.
@isnad1 id=ne.0h1v.s4.6a60f190cc4d from=translated src=- shape=a311c14d vocab=e70a8e74
-/
theorem monomial_ne_zero (h : Lattice) : monomial h ≠ 0 :=
  (monomial_isUnit h).ne_zero

/-- Section 1.1 (Notation): distinct lattice exponents give distinct monomials.
@isnad1 id=injectiv.0h0v.s2.8569af71d170 from=translated src=- shape=54c8eceb vocab=8c2a5c20
-/
theorem monomial_injective : Function.Injective monomial :=
  AddMonoidAlgebra.single_left_injective one_ne_zero

/-- Section 1.1 (Notation): a nonzero direction gives a nonzero difference polynomial.
@isnad1 id=ne.1h1v.s6.b640f487d119 from=translated src=- shape=e9b05cc3 vocab=53ce95bc
-/
theorem monomial_sub_one_ne_zero {h : Lattice} (hh : h ≠ 0) :
    monomial h - 1 ≠ 0 := by
  intro heq
  have h : monomial h = monomial 0 := by simpa using sub_eq_zero.mp heq
  exact hh (monomial_injective h)

/-- Section 1.1 (Notation): a lattice monomial acts by its forward shift.
@isnad1 id=eq.0h2v.s4.52d71fc1ecfd from=translated src=- shape=2c757c7e vocab=cbbb07cc
-/
@[simp] theorem act_monomial (h : Lattice) (c : Configuration ℚ) :
    act (monomial h) c = shift h c := by simp [monomial]

/-- Section 1.1 (Notation): the polynomial `monomial h - 1` acts by the difference operator in
direction `h`.
@isnad1 id=eq.0h2v.s6.26c9cb94375b from=translated src=- shape=1a72a982 vocab=5932566e
-/
theorem act_difference (h : Lattice) (c : Configuration ℚ) :
    act (monomial h - 1) c = difference h c := by
  simp [act_sub, difference]

/-- Section 1.1 (Notation): every Laurent operator commutes with lattice translations.
@isnad1 id=eq.0h3v.s4.5a7cfa19e77c from=translated src=- shape=2b8d95fe vocab=256ed204
-/
theorem act_shift (f : Laurent) (h : Lattice) (c : Configuration ℚ) :
    act f (shift h c) = shift h (act f c) := by
  rw [← act_monomial, ← act_mul, mul_comm, act_mul, act_monomial]

/-- Section 1.1 (Notation): every Laurent operator commutes with lattice differences.
@isnad1 id=eq.0h3v.s4.60a911995c43 from=translated src=- shape=2b8d95fe vocab=0efe5171
-/
theorem act_difference_comm (f : Laurent) (h : Lattice) (c : Configuration ℚ) :
    act f (difference h c) = difference h (act f c) := by
  simp [difference, act_config_sub, act_shift]

/-- Section 1.1 (Notation): a constant rational configuration has finite range.
@isnad1 id=finitera.0h1v.s2.380e79a23c08 from=translated src=- shape=d78c63d9 vocab=3e577b06
-/
theorem finiteRange_const (a : ℚ) : FiniteRange (fun _ : Lattice => a) := by
  simp [FiniteRange]

/-- Section 1.1 (Notation): the sum of two finite-range rational configurations has finite range.
@isnad1 id=finitera.2h2v.s5.812b177a6673 from=translated src=- shape=26c2268c vocab=0af08889
-/
theorem finiteRange_add {c d : Configuration ℚ} (hc : FiniteRange c)
    (hd : FiniteRange d) : FiniteRange (c + d) := by
  apply ((hc.prod hd).image (fun p : ℚ × ℚ => p.1 + p.2)).subset
  rintro _ ⟨z, rfl⟩
  exact ⟨(c z, d z), ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩

/-- Section 1.1 (Notation): rational scaling preserves finite range.
@isnad1 id=finitera.1h2v.s4.eefedee5076d from=translated src=- shape=69d97dbc vocab=d18b3a29
-/
theorem finiteRange_smul {c : Configuration ℚ} (hc : FiniteRange c) (a : ℚ) :
    FiniteRange (a • c) := by
  exact hc.map (fun x => a * x)

/-- Section 1.1 (Notation): the finite sum defining a Laurent operator preserves finite rational
range.
@isnad1 id=finitera.1h2v.s3.b478d0207023 from=translated src=- shape=87feec25 vocab=48cdd99a
-/
theorem finiteRange_act (f : Laurent) {c : Configuration ℚ} (hc : FiniteRange c) :
    FiniteRange (act f c) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [act_zero]
    change FiniteRange (fun _ : Lattice => (0 : ℚ))
    exact finiteRange_const 0
  | add f g hf hg => rw [act_add]; exact finiteRange_add hf hg
  | single h a => rw [act_single]; exact finiteRange_smul (hc.shift h) a

/-- Section 1.1 (Notation): substitute the lattice monomial in direction `v` for a polynomial
variable. -/
noncomputable def lineEval (v : Lattice) : Polynomial ℚ →+* Laurent :=
  Polynomial.eval₂RingHom (algebraMap ℚ Laurent) (monomial v)

/-- Section 1.1 (Notation): the polynomial variable evaluates to the monomial in direction `v`.
@isnad1 id=eq.0h1v.s6.58740ebf3925 from=translated src=- shape=07338ac2 vocab=b61e6a25
-/
@[simp] theorem lineEval_X (v : Lattice) : lineEval v Polynomial.X = monomial v := by
  simp [lineEval]

/-- Section 1.1 (Notation): a constant polynomial evaluates to the corresponding zero-exponent
Laurent coefficient.
@isnad1 id=eq.0h2v.s7.c4ba6df8a64f from=translated src=- shape=8071946d vocab=0010eb64
-/
@[simp] theorem lineEval_C (v : Lattice) (a : ℚ) :
    lineEval v (Polynomial.C a) = AddMonoidAlgebra.single 0 a := by
  simp [lineEval]

/-- Section 1.1 (Notation): substitution along a lattice direction preserves polynomial
divisibility.
@isnad1 id=dvd.1h3v.s7.6deaa42bc4f5 from=translated src=- shape=011c9002 vocab=86d5130b
-/
theorem lineEval_dvd (v : Lattice) {f g : Polynomial ℚ} (h : f ∣ g) :
    lineEval v f ∣ lineEval v g := map_dvd (lineEval v) h

/-- Section 1.1 (Notation): a power of the polynomial variable evaluates to a scaled lattice
exponent.
@isnad1 id=eq.0h2v.s6.18c7e777275d from=translated src=- shape=ac023943 vocab=ba2c64f0
-/
@[simp] theorem lineEval_X_pow (v : Lattice) (q : ℕ) :
    lineEval v (Polynomial.X ^ q) = monomial (q • v) := by simp

/-- Section 1.1 (Notation): the period polynomial evaluates to the difference polynomial in
direction `q • v`.
@isnad1 id=eq.0h2v.s7.ca2860e5ad20 from=translated src=- shape=ac180b91 vocab=1e553bb3
-/
theorem lineEval_X_pow_sub_one (v : Lattice) (q : ℕ) :
    lineEval v (Polynomial.X ^ q - 1) = monomial (q • v) - 1 := by simp

/-- Section 1.1 (Notation): the evaluated period polynomial acts as the difference in direction `q •
v`.
@isnad1 id=eq.0h3v.s7.dcb47585e43a from=translated src=- shape=b6084c04 vocab=81d4e9a9
-/
theorem act_lineEval_X_pow_sub_one (v : Lattice) (q : ℕ) (c : Configuration ℚ) :
    act (lineEval v (Polynomial.X ^ q - 1)) c = difference (q • v) c := by
  rw [lineEval_X_pow_sub_one, act_difference]

end Algebra
end Nivat
