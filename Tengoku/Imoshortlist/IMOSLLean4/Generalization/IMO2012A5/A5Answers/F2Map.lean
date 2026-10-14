/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5Defs
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.Extra.ExplicitRings.F2

/-!
# IMO 2012 A5 (`𝔽₂Map`)

We define `𝔽₂Map : 𝔽₂ → ℤ` and prove that it is a good map.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

open 𝔽₂

def 𝔽₂Map : 𝔽₂ → ℤ
  | O => -1
  | I => 0

/-- The map `𝔽₂Map` is good.
@isnad1 id=good.0h0v.s3.5c85fa174da1 from=translated src=- shape=54c8eceb vocab=234364f2
-/
theorem 𝔽₂Map_is_good : good 𝔽₂Map
  | O, O => rfl
  | O, I => rfl
  | I, O => rfl
  | I, I => rfl

/-- The map `𝔽₂Map` is non-trivial good.
@isnad1 id=nontrivi.0h0v.s4.47e7534feb4a from=translated src=- shape=54c8eceb vocab=ea689dd2
-/
theorem 𝔽₂Map_is_NontrivialGood : NontrivialGood 𝔽₂Map :=
  ⟨𝔽₂Map_is_good, rfl⟩
