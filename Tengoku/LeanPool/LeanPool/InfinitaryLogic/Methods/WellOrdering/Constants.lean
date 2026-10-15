/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Methods.ConstantSupport

/-!
# Constant coding for the undefinability of well-ordering (issue #12, commit 1)

The `L[[ℕ]]` kernel indexes its constants by `ℕ`.  Marker's construction needs two disjoint
countable families — the rational constants `d_q` (`q : ℚ`) carrying the positive order
diagram, and the Henkin constants `c_n` consumed by the fair enumeration's witness requests.
Per the frozen audit (D3): rationals at `2 * Encodable.encode q`, Henkin constants at
`2 * n + 1` — parity keeps the families disjoint without choosing an arbitrary `ℚ ≃ ℕ`.

This commit is the coding layer only: the two index functions, their injectivity, their
disjointness, and the term/sentence-level wrappers over the kernel's `constTerm`/`constTermS`.
-/

@[expose] public section

namespace FirstOrder.Language

/-- The kernel index of the rational constant `d_q`. -/
def ratConstIdx (q : ℚ) : ℕ := 2 * Encodable.encode q

/-- The kernel index of the `n`-th Henkin constant. -/
def henkinConstIdx (n : ℕ) : ℕ := 2 * n + 1

/--
@isnad1 id=injectiv.0h0v.s2.68e9a5fba90a from=translated src=- shape=54c8eceb vocab=278ea9ec
-/
theorem ratConstIdx_injective : Function.Injective ratConstIdx := by
  intro q r h
  unfold ratConstIdx at h
  exact Encodable.encode_injective (by omega)

/--
@isnad1 id=injectiv.0h0v.s2.9117e695cf95 from=translated src=- shape=e3d48bcb vocab=345fed4d
-/
theorem henkinConstIdx_injective : Function.Injective henkinConstIdx := by
  intro m n h
  unfold henkinConstIdx at h
  omega

/-- The two constant families are disjoint (even vs odd indices).
@isnad1 id=ne.0h2v.s3.d61ab0daef00 from=translated src=- shape=4d848fbc vocab=369ea40b
-/
theorem ratConstIdx_ne_henkinConstIdx (q : ℚ) (n : ℕ) :
    ratConstIdx q ≠ henkinConstIdx n := by
  unfold ratConstIdx henkinConstIdx
  omega

variable {L : Language.{0, 0}}

/-- The rational constant `d_q` as a closed `L[[ℕ]]`-term. -/
def ratConstTerm (q : ℚ) : L[[ℕ]].Term Empty := constTerm (ratConstIdx q)

end FirstOrder.Language
