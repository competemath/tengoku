/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.CompleteLocalChevalley
import Tengoku.Seed.RingTheory.Filtration
import Tengoku.Seed.RingTheory.Finiteness.Basic
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.Localization.Ideal
import Tengoku.Seed.RingTheory.Localization.Submodule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Symbolic powers in the complete-local vanishing argument

The symbolic powers of a prime are the contractions of its powers after
localizing at that prime.  In a Noetherian domain their intersection is zero.
Finite generation also clears the denominators of an entire symbolic power
at once: a single element outside the prime sends it into the ordinary
power.  These two facts supply the separated filtration and the torsion
error terms used in the complete-local vanishing argument.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

/-- The `n`-th symbolic power of a prime ideal, defined by contraction from
the localization at that prime.-/
def primeSymbolicPower (P : Ideal R) [P.IsPrime] (n : ℕ) : Ideal R :=
  Ideal.comap (algebraMap R (Localization.AtPrime P))
    ((P ^ n).map (algebraMap R (Localization.AtPrime P)))

/-- Symbolic-power membership is ordinary-power membership after multiplying
by a denominator outside the prime.
@isnad1 id=iff.0h4v.s7.533374af6489 from=translated src=- shape=eb68a573 vocab=29575ba7
-/
theorem mem_primeSymbolicPower_iff
    (P : Ideal R) [P.IsPrime] (n : ℕ) (x : R) :
    x ∈ primeSymbolicPower P n ↔
      ∃ s : R, s ∉ P ∧ s * x ∈ P ^ n := by
  change algebraMap R (Localization.AtPrime P) x ∈
    (P ^ n).map (algebraMap R (Localization.AtPrime P)) ↔ _
  exact IsLocalization.algebraMap_mem_map_algebraMap_iff
    P.primeCompl (Localization.AtPrime P) (P ^ n) x

/-- The ordinary prime power is contained in its symbolic power.
@isnad1 id=le.0h3v.s6.82efeb5ef996 from=translated src=- shape=9191cf52 vocab=e92a5f65
-/
theorem pow_le_primeSymbolicPower (P : Ideal R) [P.IsPrime] (n : ℕ) :
    P ^ n ≤ primeSymbolicPower P n :=
  Ideal.le_comap_map

/-- Symbolic powers form a decreasing filtration.
@isnad1 id=antitone.0h2v.s6.8690ef5c90ec from=translated src=- shape=8014ec72 vocab=f10af405
-/
theorem primeSymbolicPower_antitone (P : Ideal R) [P.IsPrime] :
    Antitone (primeSymbolicPower P) := by
  intro n m hnm
  exact Ideal.comap_mono (Ideal.map_mono (Ideal.pow_le_pow_right hnm))

/-- The intersection of all symbolic powers of a prime in a Noetherian
domain is zero.  Krull intersection is applied in the localized ring.
@isnad1 id=eq.0h2v.s6.7a414d47b0f5 from=translated src=- shape=b182dac5 vocab=94b69cdb
-/
theorem iInf_primeSymbolicPower_eq_bot
    [IsDomain R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime] :
    (⨅ n : ℕ, primeSymbolicPower P n) = ⊥ := by
  simp only [primeSymbolicPower, Ideal.map_pow,
    IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
  rw [← Ideal.comap_iInf,
    Ideal.iInf_pow_eq_bot_of_isLocalRing
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top]
  exact Ideal.comap_bot_of_injective
    (algebraMap R (Localization.AtPrime P))
    (FaithfulSMul.algebraMap_injective R (Localization.AtPrime P))

private theorem exists_common_primeCompl_multiplier
    (P : Ideal R) [P.IsPrime] (I J : Ideal R) (hJfg : J.FG)
    (hJ : ∀ x : R, x ∈ J → ∃ s : R, s ∉ P ∧ s * x ∈ I) :
    ∃ s : R, s ∉ P ∧ ∀ x : R, x ∈ J → s * x ∈ I := by
  refine Submodule.fg_induction
    (motive := fun N _ ↦
      (∀ x : R, x ∈ N → ∃ s : R, s ∉ P ∧ s * x ∈ I) →
        ∃ s : R, s ∉ P ∧ ∀ x : R, x ∈ N → s * x ∈ I)
    ?_ ?_ J hJfg hJ
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := hx x (Submodule.mem_span_singleton_self x)
    refine ⟨s, hs, ?_⟩
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change s * (a * x) ∈ I
    simpa only [mul_left_comm] using I.mul_mem_left a hsx
  · intro J₁ J₂ _hJ₁ _hJ₂ ih₁ ih₂ h
    obtain ⟨s, hs, hsJ⟩ := ih₁ (fun x hx ↦ h x ((le_sup_left : J₁ ≤ J₁ ⊔ J₂) hx))
    obtain ⟨t, ht, htJ⟩ := ih₂ (fun x hx ↦ h x ((le_sup_right : J₂ ≤ J₁ ⊔ J₂) hx))
    refine ⟨s * t, (inferInstance : P.IsPrime).mul_notMem hs ht, ?_⟩
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add]
    apply I.add_mem
    · simpa only [mul_assoc, mul_left_comm] using I.mul_mem_left t (hsJ a ha)
    · simpa only [mul_assoc] using I.mul_mem_left s (htJ b hb)

/-- A single denominator outside the prime sends the entire symbolic power
into the corresponding ordinary power.
@isnad1 id=ex.0h3v.s7.e57c64c68906 from=translated src=- shape=a14b8743 vocab=4a10bf9d
-/
theorem exists_mul_primeSymbolicPower_mem_pow
    [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (n : ℕ) :
    ∃ s : R, s ∉ P ∧
      ∀ x : R, x ∈ primeSymbolicPower P n → s * x ∈ P ^ n := by
  apply exists_common_primeCompl_multiplier P (P ^ n) (primeSymbolicPower P n)
    (IsNoetherian.noetherian (primeSymbolicPower P n))
  intro x hx
  exact (mem_primeSymbolicPower_iff P n x).mp hx

/-- In a complete Noetherian local domain, symbolic powers eventually lie
in any prescribed power of the maximal ideal.
@isnad1 id=ex.0h3v.s7.181ab257ff40 from=translated src=- shape=0492e1f1 vocab=c694d9bd
-/
theorem exists_primeSymbolicPower_le_maximalIdeal_pow
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (P : Ideal R) [P.IsPrime] (k : ℕ) :
    ∃ n : ℕ, primeSymbolicPower P n ≤ IsLocalRing.maximalIdeal R ^ k :=
  EtaleFundamentalGroups.exists_le_maximalIdeal_pow_of_antitone_iInf_eq_bot
    (primeSymbolicPower P) (primeSymbolicPower_antitone P)
    (iInf_primeSymbolicPower_eq_bot P) k

end EtaleFundamentalGroups.Purity

end
