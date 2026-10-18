/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Engine.TaylorModel.Core
import Tengoku.Leancert.LeanCert.Engine.TaylorModel.Functions
import Tengoku.Leancert.LeanCert.Engine.TaylorModel.Expr
import Tengoku.Leancert.LeanCert.Engine.TaylorModel.Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Taylor Models

This file re-exports all Taylor model functionality. The implementation is split into:

* `TaylorModel.Core` - Core data structure, polynomial helpers, basic operations
* `TaylorModel.Functions` - Function-specific Taylor series (sin, cos, exp, etc.)
* `TaylorModel.Expr` - Composition operations and expression integration
* `TaylorModel.Integral` - Definite-integral enclosures from Taylor-model bounds
-/

open scoped LeanCert.Core.Expr
