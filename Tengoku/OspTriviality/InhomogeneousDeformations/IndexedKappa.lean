import Tengoku.OspTriviality.InhomogeneousDeformations.IndexedCoboundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# R2-E -- the `kappa` extension and the trivializing map `T_beta` (P3)

For every rank `n >= 1`, on `g_R = g_P + kappa g_P` (`kappa` odd, `kappa^2 =
0`), with the undeformed bracket extended by `eq:scalar-rule` and the
deformed bracket `[X,Y]_beta = [X,Y]_0 + kappa Gamma_beta(X,Y)` extended the
same way, the map `T_beta = id + kappa (f_beta)_R` and its inverse
`T_beta^{-1} = id - kappa (f_beta)_R` are exactly (no truncation) mutually
inverse, even, `R`-linear maps satisfying the intertwining
`[T_beta X, T_beta Y]_0 = T_beta([X,Y]_beta)` -- `eq:intertwining` --
**unconditionally**, for arbitrary (not just homogeneous) `X,Y : g_R`.
Together with the frozen, accepted P2 (`Gamma_beta = delta f_beta`, in
`IndexedCoboundary.lean`), this is `thm:main` **for the coordinate-defined
`Gamma_beta`**: the deformation is trivialized by an explicit even change of
generators, exactly, at every rank.

**H1.3 (verbatim), what this establishes and what it does not.** This
completes **P3**. It does NOT establish the identification of this
`Gamma_beta` with the coefficient recovered from the oscillator source
(`prop:recovery`, P4) -- the single remaining declared gap to `thm:main` as
the manuscript states it. It does NOT establish `lem:source-isomorphism`,
the maps `Phi,Psi,U`, anything about `A_beta`/`A_B`, `cor:complex`, or
`f_beta = h - ad(2F(v))` (recovery machinery). It is NOT a formalization of
the manuscript's own proof, which derives `Gamma_beta` from the source
rather than defining it; the Lean development remains a deliberately
different route to the same theorem.

## Section T -- the transcription, term by term

Every sign below is transcribed directly from
`aoi2026_triviality_osp1_2n_revised.tex` (20137 bytes, SHA256
`68e8575797f041f25edf9c8a37c3d82c0e06f918f1acecebdb585e11459e6142`), the
same identity R2-D transcribed from. `Gamma_beta` and `f_beta` are NOT
re-transcribed here: they are the frozen, accepted `GammaBetaN`/`fBetaN`.

| manuscript | lines | Lean |
|---|---|---|
| `R = P + kappa P`, `kappa^2 = 0`, `kappa` odd, `R` supercommutative | 57-62 | the `RBasis n =
IndexedBasis n x Bool`/`RMod n` model; `true` is the `kappa` slot |
| coefficients written on the left | 63 | `eR`, `bracketRBasis`'s four-row table below |
| `eq:scalar-rule`: `[rX,sY]_0 = (-1)^{p(X)p(s)} rs [X,Y]_0` | 205-206 | `bracketRBasis`'s rows 2/3:
sign `gsignN n (parity i) 1` when the RIGHT slot carries `kappa`, unsigned when the LEFT slot does |
| `eq:deformed-bracket`: `[X,Y]_beta = [X,Y]_0 + kappa Gamma_beta(X,Y)` | 216-217 |
`bracketRBetaBasis`'s row 1 (`bracketRBasis`'s row 1 plus `kappaEmbed (GammaBetaBasis n i j)`) |
| `g_R = g_P + kappa g_P`; no `kappa`-injectivity claimed | 270-272 | `iotaR`/`kappaEmbed`
decomposition (`decompose`); `kappaMulR_not_injective` (K0c) |
| `(f_beta)_R(rX) = (-1)^{p(r)} r f_beta(X)` | 298-299 | `fBetaR`; `fBetaR_iotaR` (`r=1`) and
`fBetaR_kappaEmbed` (`r=kappa`, sign `-1`) both proved, not assumed |
| `eq:splitting`: `T_beta = id + kappa (f_beta)_R`, `T_beta^{-1} = id - kappa (f_beta)_R` | 300-302
| `TBeta`, `TBetaInv`, literal; `TBetaInv_TBeta`/`TBeta_TBetaInv` exact |
| `eq:intertwining`: `[T_beta X, T_beta Y]_0 = T_beta([X,Y]_beta)` | 305-306 | `intertwining_basis`
(basis level, cites `G4`), `intertwining` (arbitrary elements, unconditional) |

**Two named hazards, both resolved by direct computation, not by tuning
towards the target.** (i) `eq:scalar-rule`'s sign depends on the LEFT
argument and the RIGHT coefficient -- `bracketRBasis`'s rows 2/3 are
asymmetric exactly this way (`K1c`, `bracketRBasis_super_skew`, verifies
this pins super-skew symmetry and that the two named wrong variants break
it). (ii) the odd extension's sign depends on the COEFFICIENT's parity, not
the argument's -- `fBetaR`'s definition (via `falsePart`/`truePart`) signs
only the `kappa`-slot contribution, proved (not assumed) in `fBetaR_kappaEmbed`.

## Deliverable table

- **K0** (the model): `RBasis`, `RMod`, `parityR`, `IsHomogR`; `iotaR`,
  `kappaEmbed`, `decompose` (the embedding and the `R`-coefficient
  decomposition); `kappaMulR`, **K0c**: `kappaMulR_sq` (`kappa^2=0`) and
  `kappaMulR_not_injective` (the manuscript's own disclaimer, not an
  oversight).
- **K1** (the extended undeformed bracket): `bracketRBasis`/`bracketR`,
  transcribed (`eq:scalar-rule`); **K1a** `bracketR_iotaR_iotaR` (restricts
  to `bracketN`); **K1b** `bracketR_add_left/right`,
  `bracketR_smul_left/right`; **K1c** `bracketRBasis_super_skew` (basis
  level, the convention-pinning check, proved BEFORE K5 is attempted) and
  `bracketR_super_skew_homog` (homogeneous elements).
- **K2** (the odd extension): `fBetaR`, with `fBetaR_iotaR`/
  `fBetaR_kappaEmbed` (the two extension-rule cases, proved) and
  `fBetaR_add`/`fBetaR_smul` (`Pn n`-linearity).
- **K3** (`T_beta`): `TBeta`/`TBetaInv` (literal `eq:splitting`);
  `TBetaInv_TBeta`/`TBeta_TBetaInv` (exact inverses, no truncation);
  `TBeta_add`/`TBeta_smul` (`P`-linear) and `TBeta_kappaMulR` (the other
  half of `R`-linearity); `TBeta_isHomogR` (even).
- **K4** (the deformed bracket): `bracketRBetaBasis`/`bracketRBeta`,
  transcribed; `bracketRBeta_iotaR_iotaR` restricts to
  `bracketN + kappa GammaBetaN`, as required.
- **K5** (the intertwining, the stage's theorem): `intertwining_basis`
  (every basis pair; the substantive `(false,false)` case cites `G4` by
  name -- the residue after expanding both sides is EXACTLY `G4`'s
  statement, `GammaBetaBasis n i j = deltaFBasis n (fBetaN n) i j`);
  `intertwining` (arbitrary elements of `g_R`, **unconditional**, no
  homogeneity hypothesis needed -- `T_beta` is `Pn n`-linear so it commutes
  with the basis expansion, and `bracketR`/`bracketRBeta` are both
  bilinear, exactly as `GammaBetaN_eq_deltaFN` was unconditional for G5).
- **K6** (optional, not attempted): transport of the Lie superalgebra
  structure along `T_beta`. Not required for P3 and not held against this
  round.

Agent1c's hand analysis (design section 4) held in every substantive point:
the mixed basis cases reduce to a single term or `0`, and the coordinate
case's residue is literally `G4`.
-/

namespace InhomogeneousDeformations
namespace Indexed

/-! ## K0 -/

abbrev RBasis (n : ℕ) : Type := IndexedBasis n × Bool

def parityR {n : ℕ} (p : RBasis n) : ZMod 2 := parity p.1 + (if p.2 then 1 else 0)

abbrev RMod (n : ℕ) : Type := RBasis n → Pn n

/--
@isnad1 id=eq.0h2v.s7.ca60f2c8353e from=translated src=- shape=8540b0cc vocab=d9c00853
-/
@[simp] lemma rMod_zero_apply {n : ℕ} (k : RBasis n) : (0 : RMod n) k = 0 := rfl
/--
@isnad1 id=eq.0h4v.s7.c23640ba29e4 from=translated src=- shape=f672e01d vocab=9b393222
-/
@[simp] lemma rMod_add_apply {n : ℕ} (x y : RMod n) (k : RBasis n) : (x + y) k = x k + y k := rfl
/--
@isnad1 id=eq.0h4v.s7.1e6b8b213b2f from=translated src=- shape=3f7c90a2 vocab=892d67e1
-/
@[simp] lemma rMod_smul_apply {n : ℕ} (c : Pn n) (x : RMod n) (k : RBasis n) :
    (c • x) k = c * x k := rfl
/--
@isnad1 id=eq.0h3v.s6.a27ae0f27ae4 from=translated src=- shape=6d41ab76 vocab=18f80983
-/
@[simp] lemma rMod_neg_apply {n : ℕ} (x : RMod n) (k : RBasis n) : (-x) k = -x k := rfl

noncomputable def eR {n : ℕ} (b : RBasis n) : RMod n := fun k => if k = b then 1 else 0

/-- The embedding `iota_R : g_P -> g_R` into the `false` (un-scaled) slot.-/
noncomputable def iotaR {n : ℕ} (x : IndexedMod n) : RMod n := fun p => if p.2 then 0 else x p.1

/-- Embeds `x` scaled by `kappa`, directly into the `true` slot.-/
noncomputable def kappaEmbed {n : ℕ} (x : IndexedMod n) : RMod n := fun p => if p.2
  then x p.1 else 0

/-- The `false`-slot coordinate function of an `R`-module element.-/
def falsePart {n : ℕ} (r : RMod n) : IndexedMod n := fun i => r (i, false)

/-- The `true`-slot coordinate function of an `R`-module element.-/
def truePart {n : ℕ} (r : RMod n) : IndexedMod n := fun i => r (i, true)

/--
@isnad1 id=eq.0h2v.s3.07675c676d18 from=translated src=- shape=6ddf6d3e vocab=7aedae50
-/
@[simp] theorem falsePart_iotaR {n : ℕ} (x : IndexedMod n) : falsePart (iotaR x) = x := by
  funext i; simp [falsePart, iotaR]

/--
@isnad1 id=eq.0h2v.s6.d5dcfeaf6f48 from=translated src=- shape=75a20f26 vocab=78f47c70
-/
@[simp] theorem truePart_iotaR {n : ℕ} (x : IndexedMod n) : truePart (iotaR x) = 0 := by
  funext i; simp [truePart, iotaR]

/--
@isnad1 id=eq.0h2v.s6.ce3f7bffe4b1 from=translated src=- shape=75a20f26 vocab=bc3f4fb3
-/
@[simp] theorem falsePart_kappaEmbed {n : ℕ} (x : IndexedMod n) : falsePart (kappaEmbed x) = 0 := by
  funext i; simp [falsePart, kappaEmbed]

/--
@isnad1 id=eq.0h2v.s3.854fcb60cbf9 from=translated src=- shape=6ddf6d3e vocab=8bed4b12
-/
@[simp] theorem truePart_kappaEmbed {n : ℕ} (x : IndexedMod n) : truePart (kappaEmbed x) = x := by
  funext i; simp [truePart, kappaEmbed]

/-- Every `r : RMod n` decomposes exactly as its `false` part plus `kappa`
times its `true` part.
@isnad1 id=eq.0h2v.s6.49a2372e7e43 from=translated src=- shape=f43f91c9 vocab=13c7f08f
-/
theorem decompose {n : ℕ} (r : RMod n) : r = iotaR (falsePart r) + kappaEmbed (truePart r) := by
  funext p
  rcases p with ⟨i, b⟩
  cases b <;> simp [iotaR, kappaEmbed, falsePart, truePart]

/--
@isnad1 id=eq.0h3v.s7.db9e70243247 from=translated src=- shape=f0f972c8 vocab=15507c30
-/
theorem iotaR_add {n : ℕ} (x y : IndexedMod n) : iotaR (x + y) = iotaR x + iotaR y := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [iotaR]

/--
@isnad1 id=eq.0h3v.s7.2e719be60b18 from=translated src=- shape=dd71b015 vocab=f35566b9
-/
theorem iotaR_smul {n : ℕ} (c : Pn n) (x : IndexedMod n) : iotaR (c • x) = c • iotaR x := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [iotaR]

/--
@isnad1 id=eq.0h3v.s7.25a8dd06d7b2 from=translated src=- shape=f0f972c8 vocab=6f4f8b86
-/
theorem kappaEmbed_add {n : ℕ} (x y : IndexedMod n) :
    kappaEmbed (x + y) = kappaEmbed x + kappaEmbed y := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

/--
@isnad1 id=eq.0h3v.s7.f69163528918 from=translated src=- shape=dd71b015 vocab=c0f401ed
-/
theorem kappaEmbed_smul {n : ℕ} (c : Pn n) (x : IndexedMod n) :
    kappaEmbed (c • x) = c • kappaEmbed x := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

/--
@isnad1 id=injectiv.0h1v.s3.69c4cc02823f from=translated src=- shape=ca92e646 vocab=be2f1f84
-/
theorem iotaR_injective {n : ℕ} : Function.Injective (iotaR (n := n)) := by
  intro x y hxy
  funext i
  have := congrFun hxy (i, false)
  simpa [iotaR] using this

/--
@isnad1 id=injectiv.0h1v.s3.407efca27555 from=translated src=- shape=ca92e646 vocab=99c4beba
-/
theorem kappaEmbed_injective {n : ℕ} : Function.Injective (kappaEmbed (n := n)) := by
  intro x y hxy
  funext i
  have := congrFun hxy (i, true)
  simpa [kappaEmbed] using this

/--
@isnad1 id=iff.0h2v.s7.27812fd43377 from=translated src=- shape=365e7cd8 vocab=3a124dd3
-/
theorem iotaR_ne_zero_iff {n : ℕ} (x : IndexedMod n) : iotaR x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h heq; apply h; rw [heq]; funext p; rcases p with ⟨i, b⟩; cases b <;> simp [iotaR]
  · intro h heq; apply h
    have := congrFun heq
    funext i
    have h2 := this (i, false)
    simpa [iotaR] using h2

/-- `kappa`-multiplication on `g_R`: `kappa * (x0 + kappa x1) = kappa x0`.-/
noncomputable def kappaMulR {n : ℕ} (r : RMod n) : RMod n := fun p => if p.2 then r
  (p.1, false) else 0

/--
@isnad1 id=eq.0h2v.s4.c98b6889f207 from=translated src=- shape=42e1a9d0 vocab=86328c29
-/
theorem kappaMulR_eq {n : ℕ} (r : RMod n) : kappaMulR r = kappaEmbed (falsePart r) := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR, kappaEmbed, falsePart]

/-- **K0c**: `kappa^2 = 0` on `g_R`, as a stated theorem.
@isnad1 id=eq.0h2v.s6.d63a8245eb61 from=translated src=- shape=c1e57397 vocab=6e62933f
-/
theorem kappaMulR_sq (n : ℕ) (r : RMod n) : kappaMulR (kappaMulR r) = 0 := by
  funext p; rcases p with ⟨i, b⟩
  cases b <;> simp [kappaMulR]

/-- **K0c**: multiplication by `kappa` is not claimed, and is not, injective
on `g_R` -- the manuscript's own explicit disclaimer (lines 270-272),
witnessed concretely: `0` and `kappa e_i` (for any fixed even-pair basis
element, hence nonzero) have the same image `0`.
@isnad1 id=not.1h1v.s4.ce2ac6af0a83 from=translated src=- shape=64ad049d vocab=8b77448c
-/
theorem kappaMulR_not_injective (n : ℕ) (hn : 0 < n) :
    ¬ Function.Injective (kappaMulR (n := n)) := by
  intro hinj
  have h0 : ∃ v : Fin (2 * n), True := ⟨⟨0, by omega⟩, trivial⟩
  obtain ⟨v, -⟩ := h0
  have key : kappaMulR (n := n) (eR (Fof v, true)) = kappaMulR (n := n) (0 : RMod n) := by
    funext p; rcases p with ⟨i, b⟩
    cases b with
    | false => simp [kappaMulR]
    | true =>
      have hc : ((i, false) : RBasis n) ≠ (Fof v, true) :=
        fun h => Bool.false_ne_true (congrArg Prod.snd h)
      change eR (Fof v, true) (i, false) = kappaMulR (0 : RMod n) (i, true)
      simp [eR, kappaMulR, hc]
  have := hinj key
  have hne : (eR (n := n) (Fof v, true)) ≠ (0 : RMod n) := by
    intro h
    have := congrFun h (Fof v, true)
    simp [eR] at this
  exact hne this

def IsHomogR {n : ℕ} (r : RMod n) (d : ZMod 2) : Prop := ∀ p : RBasis n, r p ≠ 0 → parityR p = d

/-! ## K1 -- the extended undeformed bracket, `eq:scalar-rule` -/

/-- The four-row table of `eq:scalar-rule` applied to basis pairs of `g_R`:
`(e_i,e_j)` unsigned in the `false` slot; `(e_i,kappa e_j)` signed
`(-1)^{p(i)}`, `kappa` in the `true` slot; `(kappa e_i,e_j)` unsigned,
`kappa` in the `true` slot; `(kappa e_i,kappa e_j)` `0` (`kappa^2=0`).-/
noncomputable def bracketRBasis (n : ℕ) : RBasis n → RBasis n → RMod n
  | (i, false), (j, false) => iotaR (bracketBasisN n i j)
  | (i, false), (j, true) => kappaEmbed (gsignN n (parity i) 1 • bracketBasisN n i j)
  | (i, true), (j, false) => kappaEmbed (bracketBasisN n i j)
  | (_, true), (_, true) => 0

noncomputable def bracketR (n : ℕ) (x y : RMod n) : RMod n :=
  ∑ p : RBasis n, ∑ q : RBasis n, (x p * y q) • bracketRBasis n p q

/--
@isnad1 id=eq.0h2v.s5.fc8c4eca2d62 from=translated src=- shape=9d51bff9 vocab=f9924c36
-/
theorem sum_bool_eq {M : Type*} [AddCommMonoid M] (f : Bool → M) :
    ∑ b : Bool, f b = f true + f false := by
  rw [Fintype.univ_bool, Finset.sum_insert (by decide), Finset.sum_singleton]

/--
@isnad1 id=eq.0h1v.s7.c0fbd83d0fd0 from=translated src=- shape=771c46e9 vocab=3a124dd3
-/
theorem iotaR_zero (n : ℕ) : iotaR (0 : IndexedMod n) = 0 := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [iotaR]

/-! ## K1c -- super-skew symmetry on `g_R`, the convention-pinning check -/

/--
@isnad1 id=or.0h1v.s6.1da7024d097e from=translated src=- shape=a99d14a3 vocab=c87b9854
-/
theorem zmod2_cases : ∀ q : ZMod 2, q = 0 ∨ q = 1 := by decide

/--
@isnad1 id=eq.0h3v.s4.0e3709af97db from=translated src=- shape=fd3216e6 vocab=2c2a96f7
-/
theorem gsignN_comm (n : ℕ) (a b : ZMod 2) : gsignN n a b = gsignN n b a := by
  unfold gsignN; congr 1; rw [and_comm]

/--
@isnad1 id=eq.0h3v.s7.3bf4376e351e from=translated src=- shape=63a91017 vocab=ba993eb0
-/
theorem gsignN_mul_one_left (n : ℕ) (p q : ZMod 2) :
    gsignN n p 1 * gsignN n p q = gsignN n p (q + 1) := by
  have e01 : (0 : ZMod 2) + 1 = 1 := by decide
  have e11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq <;>
    simp [e01, e11, gsignN_00, gsignN_01, gsignN_10, gsignN_11]

/--
@isnad1 id=eq.0h3v.s7.46250d1d17c0 from=translated src=- shape=848d5369 vocab=ba993eb0
-/
theorem gsignN_succ_left_mul (n : ℕ) (p q : ZMod 2) :
    gsignN n (p + 1) q * gsignN n q 1 = gsignN n p q := by
  have e01 : (0 : ZMod 2) + 1 = 1 := by decide
  have e11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq <;>
    simp [e01, e11, gsignN_00, gsignN_01, gsignN_10, gsignN_11]

/--
@isnad1 id=eq.0h2v.s4.4881fb589e73 from=translated src=- shape=3648cb73 vocab=ed6ac8b2
-/
@[simp] theorem parityR_false {n : ℕ} (i : IndexedBasis n) : parityR ((i, false) : RBasis n)
  = parity i := by
  unfold parityR; simp

/--
@isnad1 id=eq.0h2v.s7.6f1274f3812d from=translated src=- shape=50a64ebc vocab=e3b1a049
-/
@[simp] theorem parityR_true {n : ℕ} (i : IndexedBasis n) : parityR ((i, true) : RBasis n) =
  parity i + 1 := by
  unfold parityR; simp

/-! ## K2 -- the odd extension `(f_beta)_R` -/

/--
@isnad1 id=eq.0h3v.s7.ba71d638aacb from=translated src=- shape=f0f972c8 vocab=e8605ba3
-/
theorem falsePart_add {n : ℕ} (r1 r2 : RMod n) :
    falsePart (r1 + r2) = falsePart r1 + falsePart r2 := by
  funext i; simp [falsePart]

/--
@isnad1 id=eq.0h3v.s7.82db25e7ebcf from=translated src=- shape=f0f972c8 vocab=1973f433
-/
theorem truePart_add {n : ℕ} (r1 r2 : RMod n) :
    truePart (r1 + r2) = truePart r1 + truePart r2 := by
  funext i; simp [truePart]

/--
@isnad1 id=eq.0h3v.s7.965dbc62c46d from=translated src=- shape=dd71b015 vocab=704465cc
-/
theorem falsePart_smul {n : ℕ} (c : Pn n) (r : RMod n) :
    falsePart (c • r) = c • falsePart r := by
  funext i; simp [falsePart]

/--
@isnad1 id=eq.0h3v.s7.a3479163ef85 from=translated src=- shape=dd71b015 vocab=c5f1aec2
-/
theorem truePart_smul {n : ℕ} (c : Pn n) (r : RMod n) :
    truePart (c • r) = c • truePart r := by
  funext i; simp [truePart]

/-- The odd extension of `fBetaN`: on `r = x0 + kappa x1`
(`x0 = falsePart r`, `x1 = truePart r`), `(f_beta)_R(r) = f_beta(x0) -
kappa f_beta(x1)`, matching `(f_beta)_R(rX) = (-1)^{p(r)} r f_beta(X)` for
`r in {1,kappa}` (K2).-/
noncomputable def fBetaR (n : ℕ) (r : RMod n) : RMod n :=
  iotaR (fBetaN n (falsePart r)) + kappaEmbed (-(fBetaN n (truePart r)))

/-! ## K3 -- `TBeta` and its inverse, `eq:splitting` -/

/--
@isnad1 id=eq.0h2v.s6.2127b4175a3d from=translated src=- shape=772b7836 vocab=d400e1bc
-/
theorem falsePart_neg {n : ℕ} (r : RMod n) : falsePart (-r) = -falsePart r := by
  funext i; simp [falsePart]

/--
@isnad1 id=eq.0h3v.s7.a56813fd0d5f from=translated src=- shape=5b842ceb vocab=f98bf597
-/
theorem kappaMulR_add (n : ℕ) (r1 r2 : RMod n) :
    kappaMulR (r1 + r2) = kappaMulR r1 + kappaMulR r2 := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR]

/--
@isnad1 id=eq.0h2v.s4.d0c318e2a718 from=translated src=- shape=d6576abc vocab=f0b40b61
-/
theorem kappaMulR_iotaR (n : ℕ) (x : IndexedMod n) : kappaMulR (iotaR x) = kappaEmbed x := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR, iotaR, kappaEmbed]

/--
@isnad1 id=eq.0h2v.s6.cd9f3fe8fb6a from=translated src=- shape=69eaf491 vocab=6f32d683
-/
theorem kappaMulR_kappaEmbed (n : ℕ) (x : IndexedMod n) : kappaMulR (kappaEmbed x) = 0 := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR, kappaEmbed]

/-- `T_beta = id + kappa (f_beta)_R` -- `eq:splitting`, literal.-/
noncomputable def TBeta (n : ℕ) (r : RMod n) : RMod n := r + kappaMulR (fBetaR n r)

/-- `T_beta^{-1} = id - kappa (f_beta)_R` -- `eq:splitting`, literal.-/
noncomputable def TBetaInv (n : ℕ) (r : RMod n) : RMod n := r - kappaMulR (fBetaR n r)

/--
@isnad1 id=eq.0h2v.s6.148c7b8664ce from=translated src=- shape=516a9646 vocab=3b1a6221
-/
theorem TBetaInv_eq (n : ℕ) (r : RMod n) : TBetaInv n r = r - kappaEmbed
  (fBetaN n (falsePart r)) := by
  unfold TBetaInv fBetaR
  rw [kappaMulR_add, kappaMulR_iotaR, kappaMulR_kappaEmbed, add_zero]

/--
@isnad1 id=eq.0h2v.s4.a76593631b3e from=translated src=- shape=dc061f59 vocab=73846d75
-/
theorem falsePart_TBetaInv (n : ℕ) (r : RMod n) : falsePart (TBetaInv n r) = falsePart r := by
  rw [TBetaInv_eq, sub_eq_add_neg, falsePart_add, falsePart_neg, falsePart_kappaEmbed,
    neg_zero, add_zero]

/--
@isnad1 id=ishomogn.1h3v.s4.c9910700d31a from=translated src=- shape=0d762085 vocab=4c418555
-/
theorem IsHomogR_falsePart {n : ℕ} {r : RMod n} {d : ZMod 2} (hr : IsHomogR r d) :
    IsHomogN (falsePart r) d := by
  intro i hi
  rw [← parityR_false]
  exact hr (i, false) (by simpa [falsePart] using hi)

/-! ## K4 -- the deformed bracket, `eq:deformed-bracket` -/

/-- The four-row table, identical to `bracketRBasis` except row 1 (both
coordinate slots) also carries `kappa Gamma_beta` -- `eq:deformed-bracket`
on coordinate elements, extended by the same scalar rule.-/
noncomputable def bracketRBetaBasis (n : ℕ) : RBasis n → RBasis n → RMod n
  | (i, false), (j, false) => iotaR (bracketBasisN n i j) + kappaEmbed (GammaBetaBasis n i j)
  | (i, false), (j, true) => kappaEmbed (gsignN n (parity i) 1 • bracketBasisN n i j)
  | (i, true), (j, false) => kappaEmbed (bracketBasisN n i j)
  | (_, true), (_, true) => 0

noncomputable def bracketRBeta (n : ℕ) (x y : RMod n) : RMod n :=
  ∑ p : RBasis n, ∑ q : RBasis n, (x p * y q) • bracketRBetaBasis n p q

/--
@isnad1 id=eq.0h1v.s7.8d99149c1c92 from=translated src=- shape=771c46e9 vocab=f416b80a
-/
theorem kappaEmbed_zero (n : ℕ) : kappaEmbed (0 : IndexedMod n) = 0 := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

/-! ## K5 -- the intertwining, `eq:intertwining` -/

/--
@isnad1 id=eq.0h2v.s4.c717e00202bc from=translated src=- shape=16203681 vocab=80ea42a1
-/
theorem falsePart_eR_false (n : ℕ) (i : IndexedBasis n) :
    falsePart ((eR ((i, false) : RBasis n))) = eN i := by
  funext k
  unfold falsePart eR eN
  simp [Prod.ext_iff]

/--
@isnad1 id=eq.0h2v.s6.6ca539ec70e8 from=translated src=- shape=078d84e9 vocab=0787ef0f
-/
theorem falsePart_eR_true (n : ℕ) (i : IndexedBasis n) :
    falsePart ((eR ((i, true) : RBasis n))) = 0 := by
  funext k
  unfold falsePart eR
  simp

end Indexed
end InhomogeneousDeformations
