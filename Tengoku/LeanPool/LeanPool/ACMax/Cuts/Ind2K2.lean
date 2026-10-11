/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.SignedCut

/-!
# Induced-`2K₂` certificate

An **induced `2K₂`** — two disjoint edges `a–b`, `c–d` with no edges between `{a,b}`
and `{c,d}` — whose four endpoints have total degree `≤ 12` certifies `algConn G ≤ 2`.

This is the `{-1,0,1}` signed certificate with `P = {a,b}`, `N = {c,d}`: there are no
`P`–`N` edges (`e(P,N)=0`), and the boundary to the neutral set is
`e(P,Z) + e(N,Z) = (deg a + deg b − 2) + (deg c + deg d − 2) = degsum − 4 ≤ 8 = 4|P|`.

Equivalently (Cauchy interlacing on the complement): the four vertices induce a `C₄`
in `Gᶜ`, whose `4×4` Laplacian block `dI − A(C₄)` has `λ_max = d + 2`, forcing
`λ_max(L(Gᶜ)) ≥ n − 2`, i.e. `λ₂(G) ≤ 2`.  For four degree-3 vertices the bound is
tight (`degsum = 12`), which is exactly what certifies the `n = 9` Fiedler-eigenvector
graphs that no `±1` cut can.
-/

@[expose] public section

namespace ACMax

end ACMax
