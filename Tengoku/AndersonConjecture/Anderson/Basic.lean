/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# Quasi-Complete Local Rings

Definitions of quasi-completeness and weak quasi-completeness for
local rings, following Anderson (2014). A local ring (R, M) is
quasi-complete if every descending chain of ideals eventually
stabilizes modulo powers of M. The weak variant restricts to
chains with zero intersection. We also define analytical
irreducibility (the M-adic completion is a domain).
-/

open scoped Pointwise

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- A local ring `R` is quasi-complete if for any antitone sequence of
ideals `A : ℕ → Ideal R` and each `k : ℕ`, there exists `s` such that
`A s ≤ (⨅ n, A n) ⊔ (IsLocalRing.maximalIdeal R) ^ k`.

This is Definition 1.1 of Anderson (2014). -/
def IsQuasiComplete : Prop :=
  ∀ (A : ℕ → Ideal R), Antitone A →
    ∀ (k : ℕ), ∃ s,
      A s ≤ (⨅ n, A n) ⊔ (IsLocalRing.maximalIdeal R) ^ k

/-- A local ring `R` is weakly quasi-complete if for any antitone sequence
of ideals `A : ℕ → Ideal R` with `⨅ n, A n = ⊥` and each `k : ℕ`,
there exists `s` such that `A s ≤ (IsLocalRing.maximalIdeal R) ^ k`.

Equivalently, this is `IsQuasiComplete` restricted to sequences whose
intersection is `⊥`. -/
def IsWeaklyQuasiComplete : Prop :=
  ∀ (A : ℕ → Ideal R), Antitone A → (⨅ n, A n) = ⊥ →
    ∀ (k : ℕ), ∃ s, A s ≤ (IsLocalRing.maximalIdeal R) ^ k

/-- A Noetherian local ring is **analytically irreducible** if its
maximal-ideal-adic completion is a domain. -/
def IsAnalyticallyIrreducible [IsNoetherianRing R] : Prop :=
  IsDomain (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- Quasi-completeness implies weak quasi-completeness. -/
theorem IsQuasiComplete.isWeaklyQuasiComplete
    (h : IsQuasiComplete R) : IsWeaklyQuasiComplete R := by
  intro A hA hInt k
  obtain ⟨s, hs⟩ := h A hA k
  exact ⟨s, by rwa [hInt, bot_sup_eq] at hs⟩
