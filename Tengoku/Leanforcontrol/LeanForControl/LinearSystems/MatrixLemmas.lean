import Tengoku

/-!
# `LinearSystems.MatrixLemmas`

Reusable matrix-level facts that bridge

* the kernel-of-`*ᵥ` formulation,
* the linear-map-`ker = ⊥` formulation,
* and the `Matrix.rank` / full-column-rank formulation.

This file is project-internal plumbing for `LinearSystems.Observability` and
`LinearSystems.Controllability`. It carries no `@[blueprint]` annotations and
intentionally exposes no LaTeX nodes — control-level statements belong in the
two `Observability` / `Controllability` files.

The file is `Field`-scoped: `Matrix.rank` requires `[CommRing 𝕜]`, and the
column or row independence bridges to `rank = card ...` need `[Field 𝕜]`.
-/

namespace LinearSystems.MatrixLemmas

open Matrix

section Field

variable {𝕜 : Type*} [Field 𝕜]
variable {m n : Type*}

end Field

end LinearSystems.MatrixLemmas
