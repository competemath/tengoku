/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Tengoku

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

-- TODO upstream
namespace Rat

open NumberField

/--
@isnad1 id=isreal.0h1v.s3.2e4712f674e6 from=translated src=- shape=9f4b6427 vocab=e8b60d6a
-/
lemma infinitePlace_isReal (v : InfinitePlace ℚ) : v.IsReal :=
  Subsingleton.elim v infinitePlace ▸ isReal_infinitePlace

end Rat
