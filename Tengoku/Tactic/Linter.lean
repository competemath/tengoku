/-
This is the `Linter`s file: it imports files defining linters.
Most syntax linters, in particular the ones enabled by default, are imported in `Mathlib.Init`;
this file contains all linters not imported in that file.

This file is ignored by `shake`:
* it is in `ignoreAll`, meaning that all its imports are considered necessary;
* it is in `ignoreImport`, meaning that where it is imported, it is considered necessary.
-/
module

public import Tengoku.Tactic.Linter.HaveLetLinter
public import Tengoku.Tactic.Linter.MinImports
public import Tengoku.Tactic.Linter.PPRoundtrip
public import Tengoku.Tactic.Linter.PrivateModule
public import Tengoku.Tactic.Linter.UnusedInstancesInType
public import Tengoku.Tactic.Linter.UpstreamableDecl

set_option linter.style.header false
