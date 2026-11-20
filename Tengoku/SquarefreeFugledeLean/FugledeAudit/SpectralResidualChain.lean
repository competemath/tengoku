import Tengoku.SquarefreeFugledeLean.FugledeAudit.ActualSparsePowers
import Tengoku.SquarefreeFugledeLean.FugledeAudit.ResidualEigenvalue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

/--
@isnad1 id=eq.1h4v.s14.e15581ee092f from=translated src=- shape=c33bfe13 vocab=d513b9a7
-/
theorem spectral_prime_unitary_order
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) :
    (spectralPrimeUnitary q H A Λ h).toLinearMap ^ q = 1 :=
  conjugated_phase_order _ _

/--
@isnad1 id=pairwise.0h3v.s9.c166a66e37fe from=translated src=- shape=ea1c9705 vocab=ba90b365
-/
theorem spectral_prime_levels_orthogonal
    (q H : ℕ) [NeZero q] [NeZero H] (Λ : Finset (ZMod (q * H))) :
    Pairwise fun j k => (spectralPrimeLevels q H Λ j).IsOrtho (spectralPrimeLevels q H Λ k) :=
  coordinate_levels_pairwise_orthogonal _

/--
@isnad1 id=eq.0h3v.s14.73c68a9bd52b from=translated src=- shape=a63f549f vocab=bb604fcd
-/
theorem spectral_prime_projections_sum
    (q H : ℕ) [NeZero q] [NeZero H] (Λ : Finset (ZMod (q * H))) :
    ∑ j, (spectralPrimeLevels q H Λ j).starProjection.toLinearMap = 1 :=
  coordinate_projections_sum _

/-- The residual-block conclusion now starts at a literal cyclic spectral pair.
In particular sparse powers, finite order, and the level decomposition are
derived rather than supplied as extra hypotheses.
@isnad1 id=other.4h4v.s19.3ae3cd73bf35 from=translated src=- shape=25c1fddf vocab=578e2dcc
-/
theorem spectral_pair_residual_chain
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) :
    let U := spectralPrimeUnitary q H A Λ h
    let L := spectralPrimeLevels q H Λ
    let ω := ZMod.stdAddChar (1 : ZMod q)
    (∀ j, unitaryCompression U (localResidual U.toLinearMap (L j) ω q) = 0) ∧
    (∀ j, Function.Bijective (residualPowerBlock U L ω q 1 j (j + 1)) ∧
      ∀ v, ‖residualPowerBlock U L ω q 1 j (j + 1) v‖ = ‖v‖) := by
  apply actual_residual_diagonal_zero_and_unitary_shifts
    (spectralPrimeUnitary q H A Λ h) q hq3 _ standard_character_primitive_root
    (spectral_prime_unitary_order q H A Λ h) (spectralPrimeLevels q H Λ)
    (spectral_prime_levels_orthogonal q H Λ) (spectral_prime_projections_sum q H Λ)
  intro r _ _ j k hkj hkr
  exact spectral_pair_sparse_powers q H hq hcop A Λ h r j k hkj hkr

/--
@isnad1 id=eq.5h7v.s15.54ebc8900190 from=translated src=- shape=356b6948 vocab=8e049161
-/
theorem spectral_pair_residual_averaged_eigenvector
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (c : Fin q → ℂ) (hc : c 0 = 1) (j : ZMod q)
    (v : localResidual (spectralPrimeUnitary q H A Λ h).toLinearMap
      (spectralPrimeLevels q H Λ j) (ZMod.stdAddChar (1 : ZMod q)) q) :
    (spectralPrimeLevels q H Λ j).starProjection
      (averagedPowers (spectralPrimeUnitary q H A Λ h).toLinearMap q c
        ((spectralPrimeLevels q H Λ j).starProjection (v : EuclideanSpace ℂ Λ))) =
      (q : ℂ)⁻¹ • (v : EuclideanSpace ℂ Λ) := by
  apply actual_residual_averaged_power_eigenvector
    (spectralPrimeUnitary q H A Λ h) q hq3 _ standard_character_primitive_root
    (spectral_prime_unitary_order q H A Λ h) (spectralPrimeLevels q H Λ)
    (spectral_prime_levels_orthogonal q H Λ) (spectral_prime_projections_sum q H Λ)
    (fun r _ _ j k hkj hkr => spectral_pair_sparse_powers q H hq hcop A Λ h r j k hkj hkr)
    c hc j v

end FugledeAudit
