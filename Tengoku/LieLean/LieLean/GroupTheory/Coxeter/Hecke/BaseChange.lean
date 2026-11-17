/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.GroupTheory.Coxeter.Hecke.Specialization
import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of Iwahori–Hecke algebras

For an `R`-algebra `S`, the base change `S ⊗[R] 𝓗_q(W)` of the Iwahori–Hecke algebra is the
Iwahori–Hecke algebra `𝓗_{q'}(W)` over `S` with parameter `q'` the image of `q`
(`IwahoriHeckeAlgebra.baseChangeEquiv`). In particular, if `q` maps to `1` in `S`, then
`S ⊗[R] 𝓗_q(W) ≃ S[W]` (`IwahoriHeckeAlgebra.baseChangeEquivMonoidAlgebra`); for
`R = A[v, v⁻¹]`, `q = v²` and `S = A` with `v ↦ 1` this is the specialization `𝓗 ⊗ A ≃ A[W]`
at `v = 1` ([GP] 8.1.2, Remark 8.1.5).

## Main definitions

* `IwahoriHeckeAlgebra.equivOfEq`: `𝓗_q(W) ≃ 𝓗_{q'}(W)` for `q = q'`.
* `IwahoriHeckeAlgebra.baseChangeEquiv`: `S ⊗[R] 𝓗_q(W) ≃ₐ[S] 𝓗_{q'}(W)`.
* `IwahoriHeckeAlgebra.baseChangeEquivMonoidAlgebra`: `S ⊗[R] 𝓗_q(W) ≃ₐ[S] S[W]` if `q ↦ 1`.

## References

* [GP] M. Geck, G. Pfeiffer, *Characters of finite Coxeter groups and Iwahori–Hecke algebras*,
  LMS Monographs 21, OUP 2000, §8.1.
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
open Module
open scoped TensorProduct

namespace Tengoku.LieLean.IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {R : Type*} [CommRing R] (q : R)

/-- The Iwahori–Hecke algebras for equal parameters are isomorphic, `T_w ↦ T_w`.-/
noncomputable def equivOfEq {q' : R} (h : q = q') :
    IwahoriHeckeAlgebra cs q ≃ₐ[R] IwahoriHeckeAlgebra cs q' := by
  subst h
  exact AlgEquiv.refl

variable (S : Type*) [CommRing S] [Algebra R S]

end Tengoku.LieLean.IwahoriHeckeAlgebra
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
