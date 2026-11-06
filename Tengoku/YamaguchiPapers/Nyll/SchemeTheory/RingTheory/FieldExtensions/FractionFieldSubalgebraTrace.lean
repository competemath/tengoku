/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.Flat.Localization
import Tengoku.Seed.RingTheory.Trace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Traces after localizing a subalgebra of a fraction field

For any subalgebra B of the fraction field K of a domain R, the actual
multiplication map K tensor B to K is an isomorphism. Flatness preserves the
inclusion B to K, and each element of K is the image of k tensor 1.
Consequently the trace of multiplication by b after base change is b itself.
The result does not assume that R is integrally closed.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace SchemeTheory

universe u v

variable (R : Type u) [CommRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

private def fractionFieldTensorSubalgebraHom (B : Subalgebra R K) :
    K ⊗[R] B →ₐ[K] K :=
  (AlgHom.liftEquiv R K B K) B.val

end SchemeTheory
