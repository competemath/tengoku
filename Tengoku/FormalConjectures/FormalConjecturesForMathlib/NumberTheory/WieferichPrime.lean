/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section
namespace Tengoku.FormalConjectures end Tengoku.FormalConjectures open Tengoku.FormalConjectures 
/-!
# Wieferich primes

A prime $p$ is a *Wieferich prime to base $a$* if $p^2$ divides $a^{p-1} - 1$, i.e. if the
congruence $a^{p-1} \equiv 1 \pmod{p}$ of Fermat's little theorem holds modulo $p^2$.
A *Wieferich prime* is a Wieferich prime to base $2$. The only known Wieferich primes are $1093$
and $3511$. A *Mirimanoff prime* is a Wieferich prime to base $3$. The only known Mirimanoff primes
are $11$ and $1006003$.

*References:*
- [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
- [OEIS A001220](https://oeis.org/A001220) (Wieferich primes)
- [OEIS A014127](https://oeis.org/A014127) (Mirimanoff primes)
- D. Mirimanoff, *Sur le dernier théorème de Fermat*, C. R. Acad. Sci. Paris 150 (1910), 204–206.
-/

/--
**Wieferich prime to base `a`**
A prime $p$ is a Wieferich prime to base $a$ if $p^2 \mid a^{p-1} - 1$, i.e. if
$a^{p-1} \equiv 1 \pmod{p^2}$.

The subtraction is truncated, so, as with `Nat.ProbablePrime`, every prime is a Wieferich prime to
base $0$. For `a ≠ 0` the definition agrees with the congruence, see
`isWieferichPrimeBase_iff_pow_modEq`.-/
@[mk_iff]
structure _root_.Tengoku.FormalConjectures.IsWieferichPrimeBase (a p : ℕ) : Prop where
  prime : p.Prime
  sq_dvd_pow_sub_one : p ^ 2 ∣ a ^ (p - 1) - 1

instance (a p : ℕ) : Decidable (IsWieferichPrimeBase a p) :=
  decidable_of_iff _ (isWieferichPrimeBase_iff a p).symm

namespace Tengoku.FormalConjectures.IsWieferichPrimeBase

variable {a p : ℕ}

/--
@isnad1 id=iswiefer.2h2v.s5.e460770474f1 from=translated src=- shape=4d0f4ed4 vocab=f0f55a8c
-/
theorem of_pow_modEq (hp : p.Prime) (h : a ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    IsWieferichPrimeBase a p :=
  ⟨hp, h.symm.dvd'⟩

/--
@isnad1 id=modeq.2h2v.s6.762da0bfecbc from=translated src=- shape=fb5733de vocab=a2f5203f
-/
theorem pow_modEq (h : IsWieferichPrimeBase a p) (ha : a ≠ 0) : a ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha))).2 h.sq_dvd_pow_sub_one).symm

/-- Every prime `p` is a Wieferich prime to any base `a ≡ 1 [MOD p ^ 2]`.
@isnad1 id=iswiefer.2h2v.s5.2449f2419176 from=translated src=- shape=0b759d14 vocab=bc7cc3c4
-/
theorem of_modEq_one (hp : p.Prime) (h : a ≡ 1 [MOD p ^ 2]) : IsWieferichPrimeBase a p :=
  .of_pow_modEq hp (by simpa using h.pow (p - 1))

end Tengoku.FormalConjectures.IsWieferichPrimeBase

/-- For a nonzero base `a`, being a Wieferich prime to base `a` is the congruence
`a ^ (p - 1) ≡ 1 [MOD p ^ 2]`. This fails for `a = 0`: see `isWieferichPrimeBase_zero_iff`.
@isnad1 id=iff.1h2v.s6.e5743de9e89d from=translated src=- shape=9a85701b vocab=f0f55a8c
-/
theorem _root_.Tengoku.FormalConjectures.isWieferichPrimeBase_iff_pow_modEq {a p : ℕ} (ha : a ≠ 0) :
    IsWieferichPrimeBase a p ↔ p.Prime ∧ a ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  ⟨fun h => ⟨h.prime, h.pow_modEq ha⟩, fun h => .of_pow_modEq h.1 h.2⟩

/-- Every prime is a Wieferich prime to base `0`, because `0 ^ (p - 1) - 1 = 0` in `ℕ`.
@isnad1 id=iff.0h1v.s3.c07b51e1807e from=translated src=- shape=dde04217 vocab=a7dced36
-/
@[simp]
theorem _root_.Tengoku.FormalConjectures.isWieferichPrimeBase_zero_iff {p : ℕ} : IsWieferichPrimeBase 0 p ↔ p.Prime :=
  ⟨fun h => h.prime, fun hp => ⟨hp, by simp [zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt)]⟩⟩

/-- Every prime is a Wieferich prime to base `1`.
@isnad1 id=iff.0h1v.s3.949fdf48dd5f from=translated src=- shape=dde04217 vocab=a7dced36
-/
@[simp]
theorem _root_.Tengoku.FormalConjectures.isWieferichPrimeBase_one_iff {p : ℕ} : IsWieferichPrimeBase 1 p ↔ p.Prime := by
  simp [isWieferichPrimeBase_iff]

/--
**Wieferich prime**
A Wieferich prime is a prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$, i.e. a Wieferich prime to
base $2$.-/
abbrev _root_.Tengoku.FormalConjectures.IsWieferichPrime (p : ℕ) : Prop := IsWieferichPrimeBase 2 p

/--
**Mirimanoff prime**
A Mirimanoff prime is a prime $p$ with $3^{p-1} \equiv 1 \pmod{p^2}$, i.e. a Wieferich prime to
base $3$. The name comes from Mirimanoff's 1910 result that a failure of the first case of
Fermat's Last Theorem for the exponent $p$ forces this congruence.-/
abbrev _root_.Tengoku.FormalConjectures.IsMirimanoffPrime (p : ℕ) : Prop := IsWieferichPrimeBase 3 p
-- Tengoku: root names of this library moved to Tengoku.FormalConjectures so they do not collide with other libraries (generated)
