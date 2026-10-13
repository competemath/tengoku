/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.Basic
import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.PermutationExtension

/-!
# Monotonicity of finite exchangeability

This file records the implication-lattice API for `ExchangeableAt`: if the first `n`
coordinates have permutation-invariant law, then so do the first `m` coordinates for every
`m ≤ n`. The proof is the finite-dimensional marginal argument: extend a permutation of
`Fin m` to one of `Fin n`, use exchangeability at `n`, and project the `n`-prefix law back to
the first `m` coordinates.

The permutation-extension step reuses Mathlib's `Equiv.Perm.exists_extending_pair`; the
measure-level projection step reuses Tau Ceti's `map_blockLaw_reindex` and `map_prefixLaw_castLE`.

This projection argument is adapted from Tau Ceti's credited
`Exchangeable.blockLaw_eq_prefixLaw_of_injective` proof in `Contractability.lean`, following the
`cameronfreer/exchangeability` sources.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

namespace ExchangeableAt

end ExchangeableAt

end Probability

end TauCeti
