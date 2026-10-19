/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingHeat
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.DerivativeAdjoint
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import Tengoku.Seed.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Tengoku.Seed.Analysis.Real.Pi.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The first-order Newtonian adjoint and the smooth pairing

The singular identity `∫ ∂ᵢN(x - y) ∂ⱼψ(x) dx = -∫ N(x - y) ∂ᵢ∂ⱼψ(x) dx` is
obtained by heat subordination: at each positive time the Gaussian kernel is
smooth, so the identity is the ordinary compactly supported integration by
parts, and the time integral of the Gaussian family reproduces the Newtonian
kernel and its first derivative.  Fubini in the time variable is legitimate
because the test function has compact support.

Combining this with the Fubini pairing for potentials and with two classical
integrations by parts gives, for smooth compactly supported data `G`,

`∫ Pᵢ(G) ∂ⱼψ = ∫ ∂ᵢ∂ⱼ(N * G) ψ`,

which is the smooth case of the distributional adjointness used for the
`L^(6/5)` Calderón--Zygmund endpoint.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

end CKN.Foundation.Euclidean
