import Tengoku.All

/-!
# Known open: the same kind of failure as Canary.lean, in libraries that are not fixed yet.

Not a gate: scripts/ci/canary/leak_canary.py and the queue step report these and do not fail on them. equational-theories is a generated library
(scripts/generate.py), outside the scope-fix class; its global `elab` and `macro` commands reserve these words for the whole tree.
Each line goes into Canary.lean the day its example compiles.
-/

set_option Elab.async false
set_option linter.unusedVariables false

example (resolve : ℕ) : True := trivial
example (superpose : ℕ) : True := trivial
example (Facts : ℕ) : True := trivial
example (memoFinOp : ℕ) : True := trivial
example (finOpTable : ℕ) : True := trivial
example (mod_symm : ℕ) : True := trivial
