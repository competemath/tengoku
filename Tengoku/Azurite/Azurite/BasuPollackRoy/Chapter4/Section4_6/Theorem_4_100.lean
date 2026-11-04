/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.HermiteForm
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.Remark_4_99
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.Theorem_4_98
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_90
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Tengoku.Seed.LinearAlgebra.Vandermonde
import Tengoku.Seed.Algebra.CharP.Algebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.6, Theorem 4.100: `√(Ideal(𝒫, K)) = Rad(Her(𝒫))`

Let `K` be a field of characteristic zero, `C` an algebraically closed extension of `K`, and `𝒫`
a finite subset of `K[X₁, …, X_k]` with `A = K[X]/Ideal(𝒫, K)` finite dimensional and
`Zer(𝒫, Cᵏ)` finite. The radical `Rad(Her(𝒫))` of Hermite's quadratic form is the kernel of the
bilinear map `her(𝒫)`. Theorem 4.100 identifies it with the radical of `Ideal(𝒫, K)`: an element
`f ∈ K[X]` lies in `√(Ideal(𝒫, K))` iff its image in `A` lies in `Rad(Her(𝒫))`.

The bridge to the geometry is the trace formula (Stickelberger, Theorem 4.98) together with
Remark 4.99, which give, for `u, w ∈ A`,
\[
  \mathrm{her}(\mathcal{P})(u, w) \longmapsto
    \sum_{x \in \mathrm{Zer}(\mathcal{P}, C^k)} \mu(x)\, u(x)\, w(x)
\]
after applying the inclusion `K ↪ C` (`hermite_bridge`). With a separating element `a`
(Lemma 4.90) the values `a(x)` are distinct, and a Vandermonde argument forces `u(x) = 0` at every
zero whenever `her(𝒫)(u, ·)` vanishes; nilpotency of the image of `u` in `Ā` (Proposition 4.92)
then descends to `f ∈ √(Ideal(𝒫, K))`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]
  {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

/-- `Rad(Her(𝒫))`, the radical of Hermite's quadratic form: the kernel of `her(𝒫)`.-/
noncomputable def radHermite (Ps : Finset (MvPolynomial (Fin k) K)) :
    Submodule K (quotPolys Ps) := LinearMap.ker (hermiteBilinOne Ps)

omit [CharZero K] in
/--
@isnad1 id=iff.0h4v.s11.185c373b3b66 from=translated src=- shape=e0698d1c vocab=13d192b8
-/
theorem mem_radHermite (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps) :
    f ∈ radHermite Ps ↔ ∀ g, hermiteBilinOne Ps f g = 0 := by
  rw [radHermite, LinearMap.mem_ker]; constructor
  · intro h g; rw [h]; rfl
  · intro h; exact LinearMap.ext fun g => h g

end Azurite.BPR.Chapter4
