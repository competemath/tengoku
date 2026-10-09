/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku

/-!
# Completeness of the De Morgan basis

Every Boolean function has a De Morgan circuit, by the Lupanov construction with no data
bits, so the basis is complete and `complexity interpretation f` is the circuit complexity of
`f` over it, for any number of outputs. This agrees with the standard measure of
[Jukna, Chapter 1][Jukna2012] up to the counting of constants and negations; see
`Cslib.Computability.Circuit.Boolean.Basic`.

Ported from `Cslib.Computability.Circuit.Boolean.Complexity` at commit `2a4389b` of the author's
CSLib fork (branch `complexitylib-integration`); upstream CSLib does not have this module. It
keeps its `Cslib.Circuits.Boolean` namespace as a candidate for upstreaming.

## References

* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

public section

namespace Cslib.Circuits.Boolean

end Cslib.Circuits.Boolean
