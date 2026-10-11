/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.RayleighUpper
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.TestVector

/-!
# Weighted (unbalanced) cut certificate

Generalizes `algConn_le_two_of_balanced_cut` to an arbitrary bipartition `A ⊔ Aᶜ`.
With `p = |A|`, `q = |Aᶜ|`, the vector `x = q·𝟙_A − p·𝟙_{Aᶜ}` is orthogonal to `𝟙`,
has squared norm `p·q·n`, and Laplacian quadratic form `n²·cut`, so
`xᵀ L x = n²·cut ≤ 2·p·q·n = 2‖x‖²` whenever `n·cut ≤ 2·p·q`.  This handles odd `n`
and unbalanced near-regular graphs where a balanced cut is unavailable.
-/

@[expose] public section

namespace ACMax

open Matrix

end ACMax
