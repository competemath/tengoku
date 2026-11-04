import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.Laurent
import Tengoku.Seed.Algebra.MonoidAlgebra.MapDomain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact target propositions and checked algebraic implications.
`MinimalNonvanishing` and `OriginInNewtonPowers` below are propositions, not
typeclass assumptions. `NewtonPowers` proves the latter and discharges that
premise in `infinite_of_minimal`; the minimal theorem remains open. Conditional
theorems are labeled as such. -/

namespace DuistermaatVanDerKallen

/-- The principal manuscript target, in every finite rank including rank zero.-/
def MinimalNonvanishing : Prop :=
  ∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 → (0 : Fin d → ℝ) ∈ newtonPolytope f →
    ∃ n : ℕ, 1 ≤ n ∧ constantTerm (f ^ n) ≠ 0

/-- The consequence of Newton-polytope homogeneity needed for infinite nonvanishing.
This proposition itself is not a proof of homogeneity. `NewtonPowers` proves
the full homogeneity identity and then supplies `origin_in_newton_powers`.-/
def OriginInNewtonPowers : Prop :=
  ∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 → (0 : Fin d → ℝ) ∈ newtonPolytope f →
    ∀ q : ℕ, 1 ≤ q → (0 : Fin d → ℝ) ∈ newtonPolytope (f ^ q)

/-- The exact arbitrary-rank headline target in unbounded-index form.-/
def InfiniteNonvanishing : Prop :=
  ∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 → (0 : Fin d → ℝ) ∈ newtonPolytope f →
    ∀ M : ℕ, ∃ n : ℕ, M < n ∧ constantTerm (f ^ n) ≠ 0

/-- Strict separation proves the vanishing direction of the classification.-/
theorem positive_powers_vanish_of_origin_not_mem {d : ℕ} (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∉ newtonPolytope f) :
    ∀ n : ℕ, 1 ≤ n → constantTerm (f ^ n) = 0 := by
  obtain ⟨w, δ, hδ, hw⟩ := support_strict_separation f hf
  intro n hn
  by_contra hne
  have h := support_pow_lower_bound w f δ hw n 0 (Finsupp.mem_support_iff.mpr hne)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [map_zero] at h
  nlinarith

/-- Conditional classification; the missing minimal theorem is an explicit premise.-/
theorem classification_of_minimal (hminimal : MinimalNonvanishing)
    {d : ℕ} (f : MultiLaurent d) (hf : f ≠ 0) :
    (∀ n : ℕ, 1 ≤ n → constantTerm (f ^ n) = 0) ↔
      (0 : Fin d → ℝ) ∉ newtonPolytope f := by
  refine ⟨?_, positive_powers_vanish_of_origin_not_mem f⟩
  intro hall hmem
  obtain ⟨n, hn, hne⟩ := hminimal d f hf hmem
  exact hne (hall n hn)

/-- Conditional Laurent Mathieu corollary, including the zero polynomial.-/
theorem mathieu_of_minimal (hminimal : MinimalNonvanishing)
    {d : ℕ} (f h : MultiLaurent d)
    (hf : ∀ n : ℕ, 1 ≤ n → constantTerm (f ^ n) = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → constantTerm (h * f ^ n) = 0 := by
  by_cases hzero : f = 0
  · refine ⟨1, fun n hn => ?_⟩
    simp [hzero, zero_pow (by omega : n ≠ 0), constantTerm]
  · exact eventual_constantTerm_zero_of_newton f h
      ((classification_of_minimal hminimal f hzero).mp hf)

/-- The two-input implication, retained for compatibility. `NewtonPowers`
discharges the second premise; minimal nonvanishing remains open.-/
theorem infinite_of_minimal_and_newton_powers (hminimal : MinimalNonvanishing)
    (hpowers : OriginInNewtonPowers) : InfiniteNonvanishing := by
  intro d f hf hnewton M
  have hpow : f ^ (M + 1) ≠ 0 := pow_ne_zero _ hf
  obtain ⟨k, hk, hct⟩ := hminimal d (f ^ (M + 1)) hpow
    (hpowers d f hf hnewton _ (by omega))
  refine ⟨(M + 1) * k, ?_, ?_⟩
  · nlinarith
  · simpa [pow_mul] using hct

/-- Every additive lattice automorphism preserves constant terms of all powers.-/
theorem constantTerm_pow_reindex {d : ℕ} (e : (Fin d → ℤ) ≃+ (Fin d → ℤ))
    (f : MultiLaurent d) (n : ℕ) :
    constantTerm ((AddMonoidAlgebra.mapDomainRingEquiv ℂ e f) ^ n) =
      constantTerm (f ^ n) := by
  rw [← map_pow]
  unfold constantTerm
  rw [AddMonoidAlgebra.coeff_mapDomainRingEquiv]
  simp

/-- Rank zero is unconditional: the only exponent is zero.-/
theorem minimal_nonvanishing_rank_zero (f : MultiLaurent 0) (hf : f ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ constantTerm (f ^ n) ≠ 0 := by
  refine ⟨1, le_rfl, ?_⟩
  simpa only [pow_one] using show constantTerm f ≠ 0 from by
    intro hc
    apply hf
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    simpa [ha, constantTerm] using hc

end DuistermaatVanDerKallen
