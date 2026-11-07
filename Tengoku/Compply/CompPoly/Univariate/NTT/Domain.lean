/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu, Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.Univariate.Raw
public import Init.Data.Vector.OfFn
public import Tengoku.Seed.Data.Nat.Log
public import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# NTT Domain

This file defines the radix-2 NTT domain parameters and basic raw-polynomial
shape helpers used by forward/inverse NTT.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

/-- Parameters for a radix-2 NTT domain of size `2 ^ logN`.-/
structure Domain (R : Type*) [Field R] where
  logN : Nat
  omega : R
  primitive : IsPrimitiveRoot omega (2 ^ logN)

namespace Domain

/-- Domain size.-/
@[simp, implicit_reducible] def n (D : Domain R) : Nat := 2 ^ D.logN

/-- Index type for vectors over the domain.-/
abbrev Idx (D : Domain R) := Fin D.n

/-- The `i`-th evaluation node `omega^i`.-/
@[inline] def node (D : Domain R) (i : D.Idx) : R := D.omega ^ (i : Nat)

/-- Inverse root of unity.-/
@[inline] def omegaInv (D : Domain R) : R := D.omega⁻¹

/-- The domain with the inverse root, used by inverse NTT butterflies.-/
def inverse (D : Domain R) : Domain R where
  logN := D.logN
  omega := D.omegaInv
  primitive := by
    simpa [omegaInv] using D.primitive.inv

/-- Multiplicative inverse of the domain size in `R`.-/
@[inline] def nInv (D : Domain R) : R := ((D.n : Nat) : R)⁻¹

/--
@isnad1 id=lt.0h2v.s4.7593d38f7be0 from=translated src=- shape=38fc717e vocab=38c11908
-/
@[simp] lemma n_pos (D : Domain R) : 0 < D.n := by
  simp [n]

/--
@isnad1 id=ne.0h2v.s4.8d0e4bf073ff from=translated src=- shape=428f6990 vocab=9515ba4b
-/
@[simp] lemma n_ne_zero (D : Domain R) : D.n ≠ 0 := by
  exact Nat.ne_of_gt D.n_pos

/-- The size of an NTT domain is nonzero in its coefficient field.
@isnad1 id=ne.0h2v.s5.be5b42338571 from=translated src=- shape=7101dedf vocab=0c368b63
-/
theorem natCast_ne_zero (D : Domain R) : ((D.n : Nat) : R) ≠ 0 := by
  let : NeZero D.n := ⟨D.n_ne_zero⟩
  exact D.primitive.neZero'.out

section RawHelpers

variable [BEq R]

/-- Required convolution length for multiplying `p` and `q`.-/
def requiredLength (p q : CPolynomial.Raw R) : Nat :=
  if p.trim.size = 0 ∨ q.trim.size = 0 then
    0
  else
    p.trim.size + q.trim.size - 1

/--
@isnad1 id=eq.1h3v.s5.3da23ecee9c6 from=translated src=- shape=185f4e05 vocab=12605f0e
-/
theorem requiredLength_eq_zero_of_left_trim_size_zero
    (p q : CPolynomial.Raw R) (hp : p.trim.size = 0) :
    requiredLength p q = 0 := by
  simp [requiredLength, hp]

/--
@isnad1 id=eq.1h3v.s5.6c0e954f238a from=translated src=- shape=897d6073 vocab=12605f0e
-/
theorem requiredLength_eq_zero_of_right_trim_size_zero
    (p q : CPolynomial.Raw R) (hq : q.trim.size = 0) :
    requiredLength p q = 0 := by
  simp [requiredLength, hq]

/--
@isnad1 id=eq.2h3v.s6.ccbe6203fb8e from=translated src=- shape=7112ebc3 vocab=b76bee68
-/
theorem requiredLength_eq_of_trim_size_pos
    (p q : CPolynomial.Raw R) (hp : 0 < p.trim.size) (hq : 0 < q.trim.size) :
    requiredLength p q = p.trim.size + q.trim.size - 1 := by
  have hp0 : p.trim.size ≠ 0 := Nat.ne_of_gt hp
  have hq0 : q.trim.size ≠ 0 := Nat.ne_of_gt hq
  simp [requiredLength, hp0, hq0]

/-- Whether domain `D` is large enough for multiplying `p` and `q`.-/
def fits (D : Domain R) (p q : CPolynomial.Raw R) : Prop :=
  requiredLength p q ≤ D.n

/-- Truncate a polynomial to at most `m` coefficients.-/
def truncate (m : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.extract 0 m

end RawHelpers
end Domain

/-- The smallest radix-2 exponent that can cover a requested convolution length.-/
def bestLogN (requiredLen : Nat) : Nat :=
  Nat.clog 2 requiredLen

/-- Load an array in natural order and pad it to a domain-sized array.-/
@[inline] def loadNaturalArray (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD i.1 0)

/--
@isnad1 id=eq.0h3v.s4.724f4f6e138c from=translated src=- shape=f6ab8635 vocab=f056a52a
-/
@[simp] theorem size_loadNaturalArray (D : Domain R) (a : Array R) :
    (loadNaturalArray D a).size = D.n := by
  simp [loadNaturalArray]

/--
@isnad1 id=eq.1h4v.s6.605807dffeb6 from=translated src=- shape=92bdc37f vocab=b7e69578
-/
@[simp] theorem getElem_loadNaturalArray (D : Domain R) (a : Array R) (i : Nat)
    (hi : i < (loadNaturalArray D a).size) :
    (loadNaturalArray D a)[i] = a.getD i 0 := by
  simp [loadNaturalArray]

/-- Load an array in natural order and pad it to a domain-sized vector.-/
@[inline] def loadNaturalVector (D : Domain R) (a : Array R) : Vector R D.n :=
  Vector.ofFn (fun i : D.Idx => a.getD i.1 0)

/-- An NTT domain bundled with proof that it covers the requested convolution length.-/
abbrev FittingDomain (R : Type*) [Field R] (requiredLen : Nat) :=
  { D : Domain R // requiredLen ≤ D.n }

/--
Generic adapter from field-specific radix-2 domain tables to a best-fitting domain lookup.

The adapter chooses `logN = Nat.clog 2 requiredLen`, then returns `none` if that exponent
is outside the supported table.-/
def bestDomainForLength?
    (maxLogN : Nat) (domainOfLogN : (logN : Nat) → logN ≤ maxLogN → Domain R)
    (domainOfLogN_logN : ∀ logN hlogN, (domainOfLogN logN hlogN).logN = logN)
    (requiredLen : Nat) : Option (FittingDomain R requiredLen) :=
  let logN := bestLogN requiredLen
  if hlogN : logN ≤ maxLogN then
    some ⟨domainOfLogN logN hlogN, by
      have hfit : requiredLen ≤ 2 ^ logN := by
        simpa [logN, bestLogN] using Nat.le_pow_clog (by decide : 1 < 2) requiredLen
      simpa [Domain.n, domainOfLogN_logN logN hlogN] using hfit⟩
  else
    none

end NTT
end CPolynomial
end CompPoly
