/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.CoveringMap
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `x ↦ xⁿ` on the nonzero elements of a proper normed field is closed with finite fibres

Material for `Mathlib/Analysis/Complex/CoveringMap.lean`; see `README.md` on the mirror tree.
That file's import closure already contains everything these need — including
`Mathlib.Algebra.Polynomial.Roots` — so upstreaming them costs it **no** new imports.
That file proves `isCoveringMap_npow`: for `n ≠ 0` in `𝕜`, the map
`x ↦ xⁿ` from `{x : 𝕜 // x ≠ 0}` to itself is a covering map. These are the two remaining
properties of that map that a *finiteness* statement needs and that being a covering map does not
give: it is a **closed** map, and its fibres are **finite** rather than merely discrete.

Both are stated at the generality of `isCoveringMap_npow`'s second half — a
`NontriviallyNormedField` — because `Mathlib/Analysis/Complex/CoveringMap.lean` already has a
section at exactly that generality. Neither uses `isCoveringMap_npow`. **`ProperSpace` is needed
only for the closedness**, which is where `isClosedMap_pow` enters; the fibre statement omits it,
and the `omit` on it is not tidiness but a claim: the fibres are finite for a reason that has
nothing to do with the topology.

* **Closedness** is `isClosedMap_pow` on the whole field, restricted along
  `(· ^ n) ⁻¹' {0}ᶜ = {0}ᶜ`. The restriction step is the standard one — if `f` is closed and
  `T = f ⁻¹' S`, then `f` restricted to `T → S` is closed, because for `C = D ∩ T` with `D`
  closed one has `f '' C = f '' D ∩ S` — and it is done by hand here rather than through
  `IsClosedMap.restrictPreimage`, whose domain is `↥((· ^ n) ⁻¹' {0}ᶜ)` and needs transporting
  along `Homeomorph.setCongr` to `{x // x ≠ 0}`. **That transport is not free**: the
  `Homeomorph.setCongr` route left a goal `↑z * ↑z = ↑(e z) * ↑(e z)` that `rw` refused with a
  transparency complaint about the subtype instance. The direct proof is twelve lines and has no
  such seam.
* **Finiteness of the fibres** is `Polynomial.finite_setOf_isRoot` at `X ^ n - C w`, which is
  nonzero exactly because `n ≠ 0`.

## Main results

- `isClosedMap_npow`
- `finite_fiber_npow`
-/

open Set Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/-- **`x ↦ xⁿ` is a closed map from the nonzero elements of a proper normed field to
themselves.**

`isClosedMap_pow` gives it on the whole field; what is added here is that the restriction to the
nonzero elements is again closed, which holds because the nonzero elements are exactly the
preimage of themselves. -/
theorem isClosedMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsClosedMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  intro C hC
  rw [isClosed_induced_iff] at hC
  obtain ⟨D, hD, rfl⟩ := hC
  rw [isClosed_induced_iff]
  refine ⟨(fun x : 𝕜 ↦ x ^ n) '' D, isClosedMap_pow 𝕜 n D hD, ?_⟩
  ext w
  constructor
  · rintro ⟨d, hdD, hdw⟩
    have hd : d ≠ 0 := by
      rintro rfl
      exact w.2 (by simpa [hn] using hdw.symm)
    exact ⟨⟨d, hd⟩, hdD, Subtype.ext hdw⟩
  · rintro ⟨c, hcD, rfl⟩
    exact ⟨c.1, hcD, rfl⟩

omit [ProperSpace 𝕜] in
/-- **The fibres of `x ↦ xⁿ` on the nonzero elements of a proper normed field are finite.**

Being a covering map (`isCoveringMap_npow`) makes the fibres *discrete*, which over a
non-compact base is not finiteness. This is the polynomial statement instead: the fibre injects
into the roots of `X ^ n - C w`, and that polynomial is nonzero exactly because `n ≠ 0`. -/
theorem finite_fiber_npow (n : ℕ) (hn : n ≠ 0)
    (w : {x : 𝕜 // x ≠ 0}) :
    Finite ((fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0})) ⁻¹'
      {w}) := by
  have hp : (X ^ n - C (w : 𝕜)) ≠ 0 := by
    intro h
    have hc := congrArg (Polynomial.coeff · n) h
    simp [coeff_X_pow, coeff_C, hn] at hc
  haveI := (finite_setOfPred_isRoot hp).to_subtype
  have hmem : ∀ p : ((fun x : {x : 𝕜 // x ≠ 0} ↦
      (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0})) ⁻¹' {w}),
      (p.1 : 𝕜) ∈ {x : 𝕜 | (X ^ n - C (w : 𝕜)).IsRoot x} := by
    rintro ⟨p, hp'⟩
    have hpw : (p : 𝕜) ^ n = (w : 𝕜) := congrArg Subtype.val hp'
    simpa [Set.mem_ofPred_eq, IsRoot.def, sub_eq_zero] using hpw
  refine Finite.of_injective (fun p ↦ (⟨(p.1 : 𝕜), hmem p⟩ : {x : 𝕜 | _})) ?_
  intro a b hab
  simp only [Subtype.mk.injEq] at hab
  exact Subtype.ext (Subtype.ext hab)
