/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Tengoku

/-!
# LeanPool.EcTateLean.Init.Data.Int.Lemmas

Imported Lean Pool material for `LeanPool.EcTateLean.Init.Data.Int.Lemmas`.
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
/--
@isnad1 id=eq.0h2v.s4.e673ea38df1c from=translated src=- shape=ac2a7734 vocab=880e9439
-/
lemma _root_.Tengoku.LeanPool.mod_neg_right (m k : Int) : m % (-k) = m % k := by simp
/--
@isnad1 id=eq.0h2v.s4.46bfbc1a36b7 from=translated src=- shape=48fe9248 vocab=20e3e41d
-/
lemma _root_.Tengoku.LeanPool.div_neg_right (m k : Int) : m / (-k) = -(m / k) := by simp

namespace Int

/--
@isnad1 id=eq.0h0v.s3.6a918aed2f6f from=translated src=- shape=b0ae1d2b vocab=5276cee2
-/
@[simp] lemma ofNat_zero_eq_zero : ofNat Nat.zero = 0 := rfl

end Int
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
