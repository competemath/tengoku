/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Language

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The 21-point witness Ψ and the geometric definition of Q

The witness structure of Gismatullin's explicit form of the
Evans–Hrushovski configuration (blueprint §geometric definition of Q):

* `QWitness`: the twenty-one points, with named fields rather than a
  21-tuple, so the intersection equations stay readable and permutation
  errors are impossible;
* `QWitness.A`, `.B`, `.C`: the three rank-two joins `A = A₁ ∨ A₂`, …;
* `QWitness.Psi`: the conjunction of clauses (i)–(vii) — the rank-four
  clauses, the incidences of `X, Z`, the genericity of `X, Y, Z` over
  `A ∨ B ∨ C`, the universal atom clauses, the dependent triple `(S, T, U)`
  inside `A, B, C`, the partial quadrangle, and the seven meet equations;
* `QWitness.PsiCore`: precisely clauses (i)–(iv), the input of the supporting
  group-configuration proposition; `Psi.toCore` retains these clauses;
* `QGeom P D Y I`: the geometric relation — some witness satisfying `Ψ`
  has `(P, D, Y, I)` as its four free outputs.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G2).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

variable (k K) in
/-- The twenty-one points of the `Q`-configuration witness (blueprint
§geometric definition of Q). The four *free outputs* of the relation are
`P`, `D`, `Y`, `I`; everything else is existentially quantified in
`QGeom`.-/
structure QWitness where
  /-- First generator of the rank-two element `A`.-/
  A₁ : Point k K
  /-- Second generator of the rank-two element `A`.-/
  A₂ : Point k K
  /-- First generator of the rank-two element `B`.-/
  B₁ : Point k K
  /-- Second generator of the rank-two element `B`.-/
  B₂ : Point k K
  /-- First generator of the rank-two element `C`.-/
  C₁ : Point k K
  /-- Second generator of the rank-two element `C`.-/
  C₂ : Point k K
  /-- The second free output: semantically `[v]`.-/
  D : Point k K
  /-- Auxiliary intersection point (semantically `[c(ax+b)]`).-/
  E : Point k K
  /-- Auxiliary intersection point (semantically `[acx]`).-/
  F : Point k K
  /-- Auxiliary intersection point (semantically `[bc]`).-/
  G : Point k K
  /-- Auxiliary intersection point (semantically `[a/b]`).-/
  H : Point k K
  /-- The fourth free output: semantically `[u/v]`.-/
  I : Point k K
  /-- The first free output: semantically `[u]`.-/
  P : Point k K
  /-- Auxiliary point (semantically `[d]`).-/
  Q : Point k K
  /-- Auxiliary intersection point (semantically `[bc+d]`).-/
  R : Point k K
  /-- The `A`-entry of the dependent triple (semantically `[a]`).-/
  S : Point k K
  /-- The `B`-entry of the dependent triple (semantically `[c]`).-/
  T : Point k K
  /-- The `C`-entry of the dependent triple (semantically `[ac]`).-/
  U : Point k K
  /-- The generic direction (semantically `[x]`).-/
  X : Point k K
  /-- The third free output: semantically `[u+v]`.-/
  Y : Point k K
  /-- Auxiliary point on two lines (semantically `[c(ax+b)+d]`).-/
  Z : Point k K

namespace QWitness

variable (w : QWitness k K)

/-- The rank-two element `A = A₁ ∨ A₂`.-/
def A : ClosedIF k K := w.A₁.1 ⊔ w.A₂.1

/-- The rank-two element `B = B₁ ∨ B₂`.-/
def B : ClosedIF k K := w.B₁.1 ⊔ w.B₂.1

/-- The rank-two element `C = C₁ ∨ C₂`.-/
def C : ClosedIF k K := w.C₁.1 ⊔ w.C₂.1

/-- Exactly clauses (i)–(iv) of Ψ. Named consumer: the six-point group
configuration proposition in the supporting blueprint (`prop:psi-gc`).-/
structure PsiCore : Prop where
  /-- Clause (i): the total join has rank four.-/
  rank_ABC : RankEq 4 (w.A ⊔ w.B ⊔ w.C)
  /-- Clause (i): `A ∨ B` has rank four.-/
  rank_AB : RankEq 4 (w.A ⊔ w.B)
  /-- Clause (i): `B ∨ C` has rank four.-/
  rank_BC : RankEq 4 (w.B ⊔ w.C)
  /-- Clause (i): `A ∨ C` has rank four.-/
  rank_AC : RankEq 4 (w.A ⊔ w.C)
  /-- Clause (ii): `X ≤ A ∨ Y`.-/
  X_le : w.X.1 ≤ w.A ⊔ w.Y.1
  /-- Clause (ii): `Z ≤ (B ∨ Y) ∧ (C ∨ X)`.-/
  Z_le : w.Z.1 ≤ (w.B ⊔ w.Y.1) ⊓ (w.C ⊔ w.X.1)
  /-- Clause (iii): `X` lies outside the parameter join.-/
  X_notLe : ¬ w.X.1 ≤ w.A ⊔ w.B ⊔ w.C
  /-- Clause (iii): `Y` lies outside the parameter join.-/
  Y_notLe : ¬ w.Y.1 ≤ w.A ⊔ w.B ⊔ w.C
  /-- Clause (iii): `Z` lies outside the parameter join.-/
  Z_notLe : ¬ w.Z.1 ≤ w.A ⊔ w.B ⊔ w.C
  /-- Clause (iv): no atom of `A` captures `X` over `Y`.-/
  X_free : ∀ A' : Point k K, A'.1 ≤ w.A → ¬ w.X.1 ≤ A'.1 ⊔ w.Y.1
  /-- Clause (iv): no atom of `B` captures `Z` over `Y`.-/
  Z_freeB : ∀ B' : Point k K, B'.1 ≤ w.B → ¬ w.Z.1 ≤ B'.1 ⊔ w.Y.1
  /-- Clause (iv): no atom of `C` captures `Z` over `X`.-/
  Z_freeC : ∀ C' : Point k K, C'.1 ≤ w.C → ¬ w.Z.1 ≤ C'.1 ⊔ w.X.1

/-- The conjunction Ψ of the seven clauses of the `Q`-configuration
(blueprint §geometric definition of Q).-/
structure Psi : Prop where
  /-- Clause (i): the total join has rank four.-/
  rank_ABC : RankEq 4 (w.A ⊔ w.B ⊔ w.C)
  /-- Clause (i): `A ∨ B` has rank four.-/
  rank_AB : RankEq 4 (w.A ⊔ w.B)
  /-- Clause (i): `B ∨ C` has rank four.-/
  rank_BC : RankEq 4 (w.B ⊔ w.C)
  /-- Clause (i): `A ∨ C` has rank four.-/
  rank_AC : RankEq 4 (w.A ⊔ w.C)
  /-- Clause (ii): `X ≤ A ∨ Y`.-/
  X_le : w.X.1 ≤ w.A ⊔ w.Y.1
  /-- Clause (ii): `Z ≤ (B ∨ Y) ∧ (C ∨ X)`.-/
  Z_le : w.Z.1 ≤ (w.B ⊔ w.Y.1) ⊓ (w.C ⊔ w.X.1)
  /-- Clause (iii): `X` is not below `A ∨ B ∨ C`.-/
  X_notLe : ¬ w.X.1 ≤ w.A ⊔ w.B ⊔ w.C
  /-- Clause (iii): `Y` is not below `A ∨ B ∨ C`.-/
  Y_notLe : ¬ w.Y.1 ≤ w.A ⊔ w.B ⊔ w.C
  /-- Clause (iii): `Z` is not below `A ∨ B ∨ C`.-/
  Z_notLe : ¬ w.Z.1 ≤ w.A ⊔ w.B ⊔ w.C
  /-- Clause (iv): no atom of `A` captures the correspondence from `Y`
  to `X`.-/
  X_free : ∀ A' : Point k K, A'.1 ≤ w.A → ¬ w.X.1 ≤ A'.1 ⊔ w.Y.1
  /-- Clause (iv): no atom of `B` captures the correspondence from `Y`
  to `Z`.-/
  Z_freeB : ∀ B' : Point k K, B'.1 ≤ w.B → ¬ w.Z.1 ≤ B'.1 ⊔ w.Y.1
  /-- Clause (iv): no atom of `C` captures the correspondence from `X`
  to `Z`.-/
  Z_freeC : ∀ C' : Point k K, C'.1 ≤ w.C → ¬ w.Z.1 ≤ C'.1 ⊔ w.X.1
  /-- Clause (v): `S ≤ A`.-/
  S_le : w.S.1 ≤ w.A
  /-- Clause (v): `T ≤ B`.-/
  T_le : w.T.1 ≤ w.B
  /-- Clause (v): `U ≤ C`.-/
  U_le : w.U.1 ≤ w.C
  /-- Clause (v): the triple `(S, T, U)` is dependent.-/
  rank_STU : RankEq 2 (w.S.1 ⊔ (w.T.1 ⊔ w.U.1))
  /-- Clause (vi): `(S, T, U)` extends to a partial quadrangle.-/
  quad : ∃ S' T' U' : Point k K,
    IsPartialQuadrangle ![w.S, w.T, w.U, S', T', U']
  /-- Clause (vii): `(P ∨ Y) ∧ (S ∨ X) = D`.-/
  meet_D : (w.P.1 ⊔ w.Y.1) ⊓ (w.S.1 ⊔ w.X.1) = w.D.1
  /-- Clause (vii): `(T ∨ Y) ∧ (Q ∨ Z) = E`.-/
  meet_E : (w.T.1 ⊔ w.Y.1) ⊓ (w.Q.1 ⊔ w.Z.1) = w.E.1
  /-- Clause (vii): `(U ∨ X) ∧ (T ∨ D) = F`.-/
  meet_F : (w.U.1 ⊔ w.X.1) ⊓ (w.T.1 ⊔ w.D.1) = w.F.1
  /-- Clause (vii): `(P ∨ T) ∧ (Q ∨ R) = G`.-/
  meet_G : (w.P.1 ⊔ w.T.1) ⊓ (w.Q.1 ⊔ w.R.1) = w.G.1
  /-- Clause (vii): `(H ∨ X) ∧ (P ∨ Y) = I`.-/
  meet_I : (w.H.1 ⊔ w.X.1) ⊓ (w.P.1 ⊔ w.Y.1) = w.I.1
  /-- Clause (vii): `(U ∨ G) ∧ A = H`.-/
  meet_H : (w.U.1 ⊔ w.G.1) ⊓ w.A = w.H.1
  /-- Clause (vii): `(F ∨ Z) ∧ C = R`.-/
  meet_R : (w.F.1 ⊔ w.Z.1) ⊓ w.C = w.R.1

end QWitness

/-- The geometric relation `Q` (blueprint §geometric definition of Q):
`(P, D, Y, I)` are the four free outputs of some witness satisfying `Ψ`.-/
def QGeom (P D Y I : Point k K) : Prop :=
  ∃ w : QWitness k K, w.Psi ∧ w.P = P ∧ w.D = D ∧ w.Y = Y ∧ w.I = I

end

end AclGeom
