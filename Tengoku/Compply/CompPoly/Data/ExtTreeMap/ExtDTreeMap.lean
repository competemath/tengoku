/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Tengoku.Compply.CompPoly.Data.ExtTreeMap.DTreeMap
public import Std.Data.ExtDTreeMap.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auxiliary lemmas for `Std.ExtDTreeMap`

Bridge lemma lifting `DTreeMap.get?_filter_with_getKey_pfilter` to
`Std.ExtDTreeMap`, used in turn by the `Std.ExtTreeMap` layer.

Vendored from
[`Verified-zkEVM/ExtTreeMapLemmas`](https://github.com/Verified-zkEVM/ExtTreeMapLemmas)
(tag `v4.29.1`, commit `3fee686227f18dca03bb7fc42ca5a9275d6cfda6`).
-/

@[expose] public section

namespace Std

attribute [local instance low] beqOfOrd

end Std
