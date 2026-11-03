/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.NumberTheory.Zsqrtd.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemmas for Mathlib's `Zsqrtd`

Material destined for mathlib.
-/

namespace Zsqrtd

variable {d : ℤ}

/-- The fundamental identity for `re + im` of a product in mathlib's `ℤ√d`.
@isnad1 id=eq.0h3v.s6.b13b7e414410 from=translated src=- shape=5c6cb42e vocab=c7309185
-/
-- Repository use: `Zsqrtd/Ideals.lean` uses this in the proof that
-- `(p, 1 - √d)` is prime.
lemma mul_re_add_im_eq (a b : Zsqrtd d) :
    (a * b).re + (a * b).im =
      (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

/-- The fundamental identity for `re - im` of a product in mathlib's `ℤ√d`.
@isnad1 id=eq.0h3v.s6.0c8c64a607c1 from=translated src=- shape=c40ec24f vocab=c7309185
-/
-- Repository use: `Zsqrtd/Ideals.lean` uses this in the proof that
-- `(p, 1 + √d)` is prime.
lemma mul_re_sub_im_eq (a b : Zsqrtd d) :
    (a * b).re - (a * b).im =
      (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

end Zsqrtd
