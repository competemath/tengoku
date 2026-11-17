/-
Nucleo Lean della campagna Agrawal — RIGIDITÀ DELLO SCHELETRO QUARTICO.

Una riga locale letterale `LocalS5 p m` identifica la potenza di
`ζ₅ - 1` all'esponente `m` con quella ottenuta dal Frobenius.  Nel ramo
inerte, il quoziente complementare ha residuo `1` oppure `4` modulo `5`;
le due righe aritmetiche risultanti sono quindi

  m ≡ 1   (mod lcm(ord(ζ₅ - 1), 5)),
  m ≡ p²  (mod lcm(ord(ζ₅ - 1), 5)).

Questo modulo porta nel kernel la rigidità che precede la costruzione
delle fibre. Non afferma la vacuità di alcuna fibra.
-/
import Tengoku.AgrawalR5.AgrawalCore.UnconditionalDichotomy
import Tengoku.AgrawalR5.AgrawalCore.LocalMomentBridge
import Tengoku.AgrawalR5.AgrawalCore.FinalRowSize

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- The concrete modulus used by the quartic order rows.-/
noncomputable def quarticOrderModulus (p : ℕ) [Fact p.Prime]
    (hp5 : p ≠ 5) : ℕ :=
  Nat.lcm (orderOf (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ))) 5

/-- The exponent `1` is always a literal local row.
@isnad1 id=locals5.0h1v.s3.dae04b068e5a from=translated src=- shape=2e48dd97 vocab=b403515c
-/
lemma localS5_one : LocalS5 p 1 := by
  simp [LocalS5]

/-- Every Frobenius power `p^j` is a literal local row.
@isnad1 id=locals5.0h2v.s4.5b73a2c175f5 from=translated src=- shape=99f5f1e7 vocab=0f65e7c9
-/
theorem localS5_frobenius_power (j : ℕ) :
    LocalS5 p (p ^ j) := by
  induction j with
  | zero => simpa using (localS5_one (p := p))
  | succ j ih =>
      have h := localS5_prime_multiple (p := p) ih
      simpa [pow_succ, Nat.mul_comm] using h

/-- **Literal local row to order congruence.**

If `m` and `p^j` induce the same permutation of the fifth roots, then a
literal local row forces equality of the corresponding powers of the
canonical unit `ζ₅ - 1`; hence the exponents are congruent modulo its
multiplicative order.
@isnad1 id=modeq.3h3v.s7.19782418c0b9 from=translated src=- shape=3ddd7203 vocab=457e7e4d
-/
theorem localS5_modEq_frobenius_power {m j : ℕ}
    (hp5 : p ≠ 5) (hrow : LocalS5 p m)
    (hm : m % 5 = (p ^ j) % 5) :
    m ≡ p ^ j
      [MOD orderOf (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ))] := by
  apply pow_eq_pow_iff_modEq.mp
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, localCyclotomicUnit_val,
    zmodFiveUnitOne_val, pow_one]
  have hfrob := localS5_frobenius_power (p := p) j
  calc
    ((zeta5 : Phi5Ring p) - 1) ^ m = zeta5 ^ m - 1 := hrow
    _ = zeta5 ^ (m % 5) - 1 := by rw [zeta5_pow_mod]
    _ = zeta5 ^ ((p ^ j) % 5) - 1 := by rw [hm]
    _ = zeta5 ^ (p ^ j) - 1 := by
      exact congrArg (fun x : Phi5Ring p => x - 1)
        (zeta5_pow_mod (p := p) (p ^ j)).symm
    _ = ((zeta5 : Phi5Ring p) - 1) ^ (p ^ j) := hfrob.symm

/-- The same comparison, with the residue modulo `5` incorporated into the
CRT modulus used by the paper.
@isnad1 id=modeq.3h3v.s6.a713ad29ca26 from=translated src=- shape=35af505d vocab=8cc1807f
-/
theorem localS5_modEq_frobenius_power_lcm {m j : ℕ}
    (hp5 : p ≠ 5) (hrow : LocalS5 p m)
    (hm : m % 5 = (p ^ j) % 5) :
    m ≡ p ^ j [MOD quarticOrderModulus p hp5] := by
  exact Nat.mod_lcm
    (localS5_modEq_frobenius_power hp5 hrow hm) hm

/-- Dividing an inert residue by another inert residue gives a split
residue (`1` or `4`) modulo `5`.
@isnad1 id=splitmod.3h2v.s4.07e5e264287b from=translated src=- shape=c8d2a134 vocab=a6422ae2
-/
theorem splitModFive_div_of_inertModFive {n p : ℕ}
    (hpdvd : p ∣ n) (hp : InertModFive p) (hn : InertModFive n) :
    SplitModFive (n / p) := by
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
  have hmod := congrArg (fun x : ℕ => x % 5) hmul
  have hlt : (n / p) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases hp with hp2 | hp3
  · rcases hn with hn2 | hn3
    · interval_cases hq : (n / p) % 5 <;>
        simp [SplitModFive, Nat.mul_mod, hp2, hn2, hq] at hmod ⊢
    · interval_cases hq : (n / p) % 5 <;>
        simp [SplitModFive, Nat.mul_mod, hp2, hn3, hq] at hmod ⊢
  · rcases hn with hn2 | hn3
    · interval_cases hq : (n / p) % 5 <;>
        simp [SplitModFive, Nat.mul_mod, hp3, hn2, hq] at hmod ⊢
    · interval_cases hq : (n / p) % 5 <;>
        simp [SplitModFive, Nat.mul_mod, hp3, hn3, hq] at hmod ⊢

/-- The complementary residue is determined, not merely known to be split:
it is `1` when the prime and the product have the same inert residue, and
`4` otherwise.
@isnad1 id=or.3h2v.s7.a6101159494e from=translated src=- shape=405e15ef vocab=9fd327e0
-/
theorem inertQuotient_residue_determined {n p : ℕ}
    (hpdvd : p ∣ n) (hp : InertModFive p) (hn : InertModFive n) :
    (p % 5 = n % 5 ∧ (n / p) % 5 = 1)
      ∨ (p % 5 ≠ n % 5 ∧ (n / p) % 5 = 4) := by
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
  have hmod := congrArg (fun x : ℕ => x % 5) hmul
  have hlt : (n / p) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases hp with hp2 | hp3
  · rcases hn with hn2 | hn3
    · interval_cases hq : (n / p) % 5 <;>
        simp [Nat.mul_mod, hp2, hn2, hq] at hmod ⊢
    · interval_cases hq : (n / p) % 5 <;>
        simp [Nat.mul_mod, hp2, hn3, hq] at hmod ⊢
  · rcases hn with hn2 | hn3
    · interval_cases hq : (n / p) % 5 <;>
        simp [Nat.mul_mod, hp3, hn2, hq] at hmod ⊢
    · interval_cases hq : (n / p) % 5 <;>
        simp [Nat.mul_mod, hp3, hn3, hq] at hmod ⊢

/-- The exact two-branch order row attached to a good inert prime.-/
def QuarticOrderRow (p m : ℕ) [Fact p.Prime] : Prop :=
  ∃ hp5 : p ≠ 5,
    m ≡ 1 [MOD quarticOrderModulus p hp5]
      ∨ m ≡ p ^ 2 [MOD quarticOrderModulus p hp5]

/-- A literal local row in the quartic branch produces one of the two exact
order congruences.
@isnad1 id=quartico.4h2v.s5.6224ff6b18fd from=translated src=- shape=7bd055c0 vocab=f14ef72c
-/
theorem quarticOrderRow_of_local {m : ℕ}
    (hp5 : p ≠ 5) (hp : InertModFive p)
    (hm : SplitModFive m) (hrow : LocalS5 p m) :
    QuarticOrderRow p m := by
  refine ⟨hp5, ?_⟩
  rcases hm with hm1 | hm4
  · left
    have hmod : m % 5 = (p ^ 0) % 5 := by simp [hm1]
    simpa using
      (localS5_modEq_frobenius_power_lcm (p := p) hp5 hrow hmod)
  · right
    have hpSq : (p ^ 2) % 5 = 4 := by
      rcases hp with hp2 | hp3
      · simp [Nat.pow_mod, hp2]
      · simp [Nat.pow_mod, hp3]
    have hmod : m % 5 = (p ^ 2) % 5 := hm4.trans hpSq.symm
    exact localS5_modEq_frobenius_power_lcm hp5 hrow hmod

/-- The exact row with its branch labelled by the residue of the prime
relative to the residue of the whole candidate.-/
def DeterminedQuarticOrderRow (n p m : ℕ) [Fact p.Prime] : Prop :=
  ∃ hp5 : p ≠ 5,
    (p % 5 = n % 5
      ∧ m ≡ 1 [MOD quarticOrderModulus p hp5])
      ∨ (p % 5 ≠ n % 5
        ∧ m ≡ p ^ 2 [MOD quarticOrderModulus p hp5])

/-- A literal row has the branch prescribed by the quotient residue.
@isnad1 id=determin.6h3v.s5.7fb1a3ed5358 from=translated src=- shape=19a4b08c vocab=93b7c8f9
-/
theorem determinedQuarticOrderRow_of_local {n m : ℕ}
    (hpdvd : p ∣ n) (hp5 : p ≠ 5)
    (hp : InertModFive p) (hn : InertModFive n)
    (hmul : m = n / p) (hrow : LocalS5 p m) :
    DeterminedQuarticOrderRow n p m := by
  refine ⟨hp5, ?_⟩
  rcases inertQuotient_residue_determined hpdvd hp hn with
    ⟨hsame, hm1⟩ | ⟨hdiff, hm4⟩
  · left
    refine ⟨hsame, ?_⟩
    have hmod : m % 5 = (p ^ 0) % 5 := by simp [hmul, hm1]
    simpa using
      (localS5_modEq_frobenius_power_lcm (p := p) hp5 hrow hmod)
  · right
    refine ⟨hdiff, ?_⟩
    have hpSq : (p ^ 2) % 5 = 4 := by
      rcases hp with hp2 | hp3
      · simp [Nat.pow_mod, hp2]
      · simp [Nat.pow_mod, hp3]
    have hmod : m % 5 = (p ^ 2) % 5 := by
      simpa [hmul, hm4] using hpSq.symm
    exact localS5_modEq_frobenius_power_lcm hp5 hrow hmod

/-- Exact order rows at every factor of the quartic skeleton.-/
def QuarticOrderRows (n : ℕ) : Prop :=
  ∀ p (hp : p ∈ n.primeFactors),
    @QuarticOrderRow p (n / p) ⟨Nat.prime_of_mem_primeFactors hp⟩

/-- Exact, residue-labelled order rows at every factor.-/
def DeterminedQuarticOrderRows (n : ℕ) : Prop :=
  ∀ p (hp : p ∈ n.primeFactors),
    @DeterminedQuarticOrderRow n p (n / p)
      ⟨Nat.prime_of_mem_primeFactors hp⟩

/-- The concrete quartic skeleton supplies all exact order rows.
@isnad1 id=quartico.2h1v.s3.33c8de942ca7 from=translated src=- shape=cbe5c5ba vocab=cf5a28a5
-/
theorem quarticOrderRows_of_skeleton {n : ℕ}
    (hn : SquarefreeCounterexampleCandidate n)
    (hskeleton : QuarticSkeleton n) :
    QuarticOrderRows n := by
  rcases hn with ⟨_hsq, _hnprime, h5, _hglobal, hbad⟩
  have hnInert : InertModFive n :=
    inertModFive_of_square_ne_one h5 hbad
  intro p hpmem
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hp5 : p ≠ 5 := by
    intro hp
    exact h5 (hp ▸ hpdvd)
  have hpInert : InertModFive p := (hskeleton p hpmem).1
  have hmSplit : SplitModFive (n / p) :=
    splitModFive_div_of_inertModFive hpdvd hpInert hnInert
  exact quarticOrderRow_of_local hp5 hpInert hmSplit
    (hskeleton p hpmem).2

/-- The skeleton determines the exponent branch at every factor.
@isnad1 id=determin.2h1v.s3.206297d5cda3 from=translated src=- shape=cbe5c5ba vocab=8b593db4
-/
theorem determinedQuarticOrderRows_of_skeleton {n : ℕ}
    (hn : SquarefreeCounterexampleCandidate n)
    (hskeleton : QuarticSkeleton n) :
    DeterminedQuarticOrderRows n := by
  rcases hn with ⟨_hsq, _hnprime, h5, _hglobal, hbad⟩
  have hnInert : InertModFive n :=
    inertModFive_of_square_ne_one h5 hbad
  intro p hpmem
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hp5 : p ≠ 5 := by
    intro hp
    exact h5 (hp ▸ hpdvd)
  exact determinedQuarticOrderRow_of_local hpdvd hp5
    (hskeleton p hpmem).1 hnInert rfl (hskeleton p hpmem).2

/-- Every nontrivial skeleton row bounds its concrete cyclotomic modulus by
the larger of the Frobenius representative and the complementary product.
@isnad1 id=ex.5h2v.s7.181c6f7f7b66 from=translated src=- shape=9f43d565 vocab=85e11903
-/
theorem quarticSkeleton_orderModulus_le_max {n p : ℕ}
    (hn : SquarefreeCounterexampleCandidate n)
    (hskeleton : QuarticSkeleton n) (hpmem : p ∈ n.primeFactors)
    (hquot : 1 < n / p) (hne : n / p ≠ p ^ 2) :
    ∃ hp5 : p ≠ 5,
      @quarticOrderModulus p ⟨Nat.prime_of_mem_primeFactors hpmem⟩ hp5
        ≤ max (p ^ 2) (n / p) := by
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
  rcases quarticOrderRows_of_skeleton hn hskeleton p hpmem with
    ⟨hp5, hrow⟩
  exact ⟨hp5, localRow_order_le_max hquot hne hrow⟩

/-- The sharp branch-sensitive gap bound used by the explicit CRT system.
@isnad1 id=ex.5h2v.s7.b600e2cba573 from=translated src=- shape=f2f84b49 vocab=52b08327
-/
theorem quarticSkeleton_orderModulus_le_gap {n p : ℕ}
    (hn : SquarefreeCounterexampleCandidate n)
    (hskeleton : QuarticSkeleton n) (hpmem : p ∈ n.primeFactors)
    (hquot : 1 < n / p) (hne : n / p ≠ p ^ 2) :
    ∃ hp5 : p ≠ 5,
      @quarticOrderModulus p ⟨Nat.prime_of_mem_primeFactors hpmem⟩ hp5
        ≤ max (n / p - 1) ((n / p - p ^ 2) + (p ^ 2 - n / p)) := by
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
  rcases determinedQuarticOrderRows_of_skeleton hn hskeleton p hpmem with
    ⟨hp5, ⟨_hsame, hrow⟩ | ⟨_hdiff, hrow⟩⟩
  · exact ⟨hp5, (pureRow_order_le_product_sub_one hquot hrow).trans
      (Nat.le_max_left _ _)⟩
  · exact ⟨hp5, (twistedRow_order_le_absGap hne hrow).trans
      (Nat.le_max_right _ _)⟩

/-- **Concrete final-row size exclusion.**

If the complementary product lies strictly below `p²`, while the concrete
quartic order modulus is at least `p²`, the skeleton row is impossible.
@isnad1 id=false.6h2v.s6.296f0d1a282b from=translated src=- shape=d97acf34 vocab=0c4e43b2
-/
theorem quarticSkeleton_factor_size_exclusion {n p : ℕ}
    (hn : SquarefreeCounterexampleCandidate n)
    (hskeleton : QuarticSkeleton n) (hpmem : p ∈ n.primeFactors)
    (hquot : 1 < n / p) (hlt : n / p < p ^ 2)
    (hlarge : ∀ hp5 : p ≠ 5,
      p ^ 2 ≤
        @quarticOrderModulus p ⟨Nat.prime_of_mem_primeFactors hpmem⟩ hp5) :
    False := by
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
  rcases quarticOrderRows_of_skeleton hn hskeleton p hpmem with
    ⟨hp5, hrow⟩
  exact threeFactor_finalRow_size_exclusion hquot hlt (hlarge hp5) hrow

/-- **Order-level concrete dichotomy.**

Every squarefree candidate either has a split order-four witness, or has
the odd inert quartic skeleton (at least three factors) together with all
of its exact order congruences.
@isnad1 id=or.1h1v.s5.79f95929c139 from=translated src=- shape=bc1e0aaf vocab=147864dd
-/
theorem squarefree_counterexample_order_dichotomy
    {n : ℕ} (hn : SquarefreeCounterexampleCandidate n) :
    SplitOrderFourWitness n ∨
      (QuarticSkeleton n ∧ QuarticOrderRows n
        ∧ DeterminedQuarticOrderRows n
        ∧ Odd n.primeFactors.card ∧ 3 ≤ n.primeFactors.card) := by
  rcases squarefree_counterexample_concrete_dichotomy hn with
    hsplit | ⟨hskeleton, hodd, hcard⟩
  · exact Or.inl hsplit
  · exact Or.inr
      ⟨hskeleton, quarticOrderRows_of_skeleton hn hskeleton,
        determinedQuarticOrderRows_of_skeleton hn hskeleton, hodd, hcard⟩

end AgrawalCore
