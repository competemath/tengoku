/-
Copyright 2025 The Formal Conjectures Authors.

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
public import Tengoku.FormalConjectures.FormalConjecturesForMathlib.Data.Nat.Factorization.Basic

@[expose] public section

namespace Nat

/-- `n.squarefreePart` is the unique `a₀ : ℕ` such that `a₀` is squarefree and `n = a₀ * b ^ 2`,
for some `b : ℕ`. At `0` this property is not well defined because `b` must be `0` and `a₀` can be
any squarefree number; we give the junk value `1` at `n = 0` following the convention that the
squarefree part of any square is `1`.-/
def squarefreePart (n : ℕ) : ℕ := n.factorization.prod fun (p e : ℕ) ↦ p ^ (e % 2)

/--
@isnad1 id=ne.0h1v.s3.c2a2bb857037 from=translated src=- shape=b14ee516 vocab=813047a2
-/
theorem squarefreePart_ne_zero (n : ℕ) : n.squarefreePart ≠ 0 := by
  simp [squarefreePart]

/--
@isnad1 id=eq.0h0v.s3.ebb50e863057 from=translated src=- shape=3c26ae4f vocab=813047a2
-/
theorem squarefreePart_zero : squarefreePart 0 = 1 := by
  simp [squarefreePart]

/-- If `n` is squarefree, then its squarefree part is itself.
@isnad1 id=eq.1h1v.s3.4b56f056dc8b from=translated src=- shape=59f01cbc vocab=2e8d8538
-/
theorem squarefreePart_of_squarefree {n : ℕ} (hn : Squarefree n) :
    squarefreePart n = n := by
  nth_rw 2 [← n.prod_factorization_pow_eq_self fun _ ↦ by simp_all]
  simp only [squarefreePart, Finsupp.prod, support_factorization]
  exact Finset.prod_congr rfl fun p hp ↦ by
    rw [factorization_eq_one_of_squarefree hn (mem_primeFactors.1 hp).1 (mem_primeFactors.1 hp).2.1]

/-- The squarefree part of any square is `1`.
@isnad1 id=eq.1h1v.s4.0665873b0e3f from=translated src=- shape=c970409e vocab=97144e49
-/
theorem squarefreePart_of_isSquare {n : ℕ} (hn : IsSquare n) :
    squarefreePart n = 1 := by
  rcases eq_or_ne n 0 with (rfl | h₀); exact squarefreePart_zero
  obtain ⟨r, rfl⟩ := hn
  rw [ne_eq, mul_eq_zero, or_self] at h₀
  rw [squarefreePart, Finsupp.prod, support_factorization,
    Finset.prod_congr rfl fun p hp ↦ by rw [r.factorization_mul h₀ h₀]]
  simp [← two_mul]

/-- If $n = \prod_p p^{e_p}$ is the prime factorization of $n$, then $\prod_p p^{e_p \pmod{2}}$
is the prime factorization of the squarefree part of $n$.
@isnad1 id=eq.1h2v.s5.565b168431fd from=translated src=- shape=fedfd6fd vocab=6a1361d5
-/
theorem squarefreePart_factorization (n : ℕ) {p : ℕ} (hp : p.Prime) :
    n.squarefreePart.factorization p = n.factorization p % 2 := by
  rw [squarefreePart, prod_factorization_eq_prod_primeFactors,
    n.prod_primeFactors_factorization_apply hp (f := fun p n ↦ n.factorization p % 2)
      (fun _ _ h ↦ by simp [factorization_eq_zero_of_not_dvd h]) (by simp)]

/--
@isnad1 id=squarefr.1h1v.s3.ded17dbb9a0d from=translated src=- shape=4596ad61 vocab=95ce30db
-/
theorem Prime.squarefree {p : ℕ} (hp : p.Prime) : Squarefree p := Irreducible.squarefree hp

/--
@isnad1 id=squarefr.0h1v.s2.dd53d4f107ef from=translated src=- shape=6da4ece3 vocab=2e8d8538
-/
theorem squarefree_squarefreePart (n : ℕ) : Squarefree n.squarefreePart := by
  refine Nat.squarefree_iff_factorization_le_one n.squarefreePart_ne_zero |>.2 fun p ↦ ?_
  by_cases hp : p.Prime
  · linarith [n.squarefreePart_factorization hp, Nat.mod_lt (n.factorization p) two_pos]
  · linarith [factorization_eq_zero_of_not_prime n.squarefreePart hp]

/--
@isnad1 id=dvd.0h1v.s3.74bba88ee6a5 from=translated src=- shape=a365602c vocab=99e9b224
-/
theorem squarefreePart_dvd (n : ℕ) : squarefreePart n ∣ n := by
  rcases eq_or_ne n 0 with (rfl | h₀); simp
  exact Nat.factorization_prime_le_iff_dvd n.squarefreePart_ne_zero h₀ |>.1 fun p hp ↦
    squarefreePart_factorization _ hp ▸ Nat.mod_le _ _

/-- The square part is the value of `b ^ 2` in the squarefree decomposition of `n = a₀ * b ^ 2`.-/
def squarePart (n : ℕ) : ℕ := n / n.squarefreePart

/--
@isnad1 id=eq.0h0v.s3.4bf4e9e08ef0 from=translated src=- shape=3c26ae4f vocab=324f81c4
-/
theorem squarePart_zero : squarePart 0 = 0 := by simp [squarePart]

/-- The squarefree decomposition of a natural number.
@isnad1 id=eq.0h1v.s4.197f6d3071d7 from=translated src=- shape=b690c24f vocab=f1262eb0
-/
theorem squarefreePart_mul_squarePart (n : ℕ) : n.squarefreePart * n.squarePart = n :=
  Nat.mul_div_eq_iff_dvd.2 n.squarefreePart_dvd

/--
@isnad1 id=infinite.0h0v.s3.10294cc57d8b from=translated src=- shape=7fa0a85e vocab=e8e41267
-/
theorem squarefree_infinite : Set.Infinite { n : ℕ | Squarefree n } :=
  Set.Infinite.mono (fun _ hp ↦ hp.squarefree) Nat.infinite_setOfPred_prime

end Nat
