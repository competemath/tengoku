import Tengoku.OspTriviality.InhomogeneousDeformations.IndexedJacobi
import Tengoku.Seed.Logic.Equiv.Fin.Basic
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# R2-D (G0-G5) — the coefficient/coboundary identity `Gamma_beta = delta f_beta`

`H1.2`: every declaration here is stated for general `n : ℕ`, with indices
in `Fin (2 * n)`; no `n = 1` specialization, `Fin 2` instance, or literal
five-element basis appears anywhere. `Indexed.lean`, `IndexedLaws.lean` and
`IndexedJacobi.lean` (all three frozen) are never reopened; the freeze is
three layers deep and deliberate -- G4 rests on U0's `Jn_antisymm` and
`Lof_comm` and on P1's bracket formulas, and none of them are restated to
ease this proof. Any new lemma about `Jn`/`Lof` needed here lives in this
module, never retroactively in an accepted one.

`H1.3` (verbatim, do not upgrade): a successful R2-D establishes **P2**:
for every `n ≥ 1`, the coordinate-specified `Gamma_beta` equals the
coboundary `delta f_beta` of the coordinate-specified primitive, on the
free `P`-module. It does **not** establish that this coordinate
`Gamma_beta` is the coefficient actually recovered from the oscillator
source (that identification is **P4**, the declared gap of this stage);
the `T_beta` intertwining, and therefore not that the deformation is
*trivialized* (P2 says the coefficient is a coboundary; the step from
"coboundary" to "trivialized by an explicit even change of generators" is
**P3**); nor the manuscript's `thm:main`, nor a formalization of the
manuscript's own proof, which *derives* `Gamma_beta` from the source
rather than defining it.

## Transcription (Section T)

`Gamma_beta`'s basis values are transcribed from `eq:gamma-ll`,
`eq:gamma-lf`, `eq:gamma-ff`; `f_beta`'s values from `eq:primitive`; all
from `aoi2026_triviality_osp1_2n_revised.tex`. Neither is derived,
adjusted or "simplified" from the other. `eq:primitive` is 1-based
(`f_beta(F_u) = sum_{j=1}^n (beta_{2j-1} L_{2j,u} - beta_{2j} L_{2j-1,u})`);
its 0-based form, used throughout below, is
`sum_{j=0}^{n-1} (beta_{2j} L_{2j+1,u} - beta_{2j+1} L_{2j,u})`
(`fBetaBasis`'s `.inr` case, via `evenIdx`/`oddIdx`). `Gamma_beta`'s FL
sector has no manuscript formula: it is fixed by the declared convention
`Gamma_beta(Y,X) = -(-1)^{p(X)p(Y)} Gamma_beta(X,Y)`
(`GammaBetaBasis`'s `.inr, .inl` case, literally `-gammaLFn`), and G4's FL
proof is reported as corroboration of that convention, not as an
independent check.

## Sector table (G4)

All three substantive sectors close on `Jn_antisymm`, `Lof_comm` and G0's
contraction identity alone, exactly as Agent1's hand analysis predicted:

* `G4_LL` -- `f_beta` vanishes on the even part, so all three terms of
  `delta f_beta` vanish, matching `eq:gamma-ll`.
* `G4_LF` -- expanding `f_beta(F_w)` via G0's contraction identity and the
  accepted `LL` bracket formula reduces the `[L_{uv}, f_beta(F_w)]_0`
  term to `eq:gamma-lf` plus exactly `f_beta([L_{uv},F_w]_0)`, which then
  cancels against `delta`'s own third term.
* `G4_FF` -- the two `[f_beta(F_u),F_v]_0`/`[f_beta(F_v),F_u]_0` terms'
  `J`-parts cancel by `Jn_antisymm`, leaving `eq:gamma-ff`; the third term
  vanishes since `bracketFFn` lands purely in the (`f_beta`-killed) even
  part.
* `G4_FL` -- corroboration of the declared convention: computed the same
  way as `G4_LF`/`G4_LL`'s methods combined, and found to match.

`G4` assembles all four sectors into one statement on all ordered basis
pairs; `G5` extends it, unconditionally, to arbitrary elements of
`IndexedMod n` via the same `bilinearExtend` combinator both `GammaBetaN`
and `deltaFN` are built from -- since both sides are literally the
bilinear extension of basis functions that agree pointwise (G4), equality
on all of `IndexedMod n` follows with no separate homogeneous-expansion
argument, and in particular subsumes the homogeneous-hypothesis form the
design/packet describes.
-/

namespace InhomogeneousDeformations
namespace Indexed

/-! ## G0 -- `beta`, the vector `v`, and the contraction identity -/

/-- `beta_u`, the polynomial generator of `Pn n` at index `u`.-/
noncomputable def betaN (n : ℕ) (u : Fin (2 * n)) : Pn n := MvPolynomial.X u

/-- The index-`t` partner under `Jn`: `t+1` if `t` is even, `t-1` if odd.
Bounds proved by `omega` from `t.isLt` alone -- linear in `n`, never
multiplying two unknowns (the rank-nonlinearity trap named in every
earlier round).-/
noncomputable def partnerN (n : ℕ) (t : Fin (2 * n)) : Fin (2 * n) :=
  if h : (t : ℕ) % 2 = 0 then ⟨(t : ℕ) + 1, by have := t.isLt; omega⟩
  else ⟨(t : ℕ) - 1, by have := t.isLt; omega⟩

/-- The vector `v = sum_{j=0}^{n-1} (beta_{2j+1} e_{2j} - beta_{2j} e_{2j+1})`
(0-based `eq:v`), given componentwise via the partner index: `v_t =
beta_{t+1}` for `t` even, `-beta_{t-1}` for `t` odd -- the unique closed
form matching that sum termwise.-/
noncomputable def vN (n : ℕ) (t : Fin (2 * n)) : Pn n :=
  if (t : ℕ) % 2 = 0 then betaN n (partnerN n t) else -betaN n (partnerN n t)

/-- The 0-based even/odd index pair for loop variable `j : Fin n`:
`evenIdx n j = 2*j`, `oddIdx n j = 2*j+1`.-/
noncomputable def evenIdx (n : ℕ) (j : Fin n) : Fin (2 * n) :=
  ⟨2 * (j : ℕ), by have := j.isLt; omega⟩
noncomputable def oddIdx (n : ℕ) (j : Fin n) : Fin (2 * n) :=
  ⟨2 * (j : ℕ) + 1, by have := j.isLt; omega⟩

/--
@isnad1 id=eq.1h3v.s6.119fb9a144f9 from=translated src=- shape=fbbd275f vocab=d1e47ceb
-/
theorem Jn_ne_zero_iff_partner (n : ℕ) (t u : Fin (2 * n)) (h : Jn n t u ≠ 0) :
    t = partnerN n u := by
  unfold Jn at h
  split_ifs at h with h1 h2
  · obtain ⟨he, hs⟩ := h1
    apply Fin.ext
    unfold partnerN
    rw [dite_eq_right (show ¬ (u : ℕ) % 2 = 0 by omega)]
    dsimp only
    omega
  · obtain ⟨he, hs⟩ := h2
    apply Fin.ext
    unfold partnerN
    rw [dite_eq_left he]
    dsimp only
    omega
  · exact absurd (cratN_zero n) h

/-- The interleaving equivalence `Fin n × Fin 2 ≃ Fin (2*n)`, `(j,p) ↦
2*j+p`, used to split a `Fin (2*n)` sum into its even and odd parts.-/
noncomputable def pairEquivN (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

/--
@isnad1 id=eq.0h3v.s6.171f5da8b1dd from=translated src=- shape=22e69733 vocab=d560d069
-/
theorem sum_split_even_odd {M : Type*} [AddCommMonoid M] (n : ℕ) (g : Fin (2 * n) → M) :
    ∑ t : Fin (2 * n), g t
      = ∑ j : Fin n, (g (evenIdx n j) + g (oddIdx n j)) := by
  rw [← Equiv.sum_comp (pairEquivN n) g]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two]
  congr 2
  · apply Fin.ext; simp [pairEquivN, finProdFinEquiv, finCongr, evenIdx]
  · apply Fin.ext; simp [pairEquivN, finProdFinEquiv, finCongr, oddIdx]; omega

/-! ## G1 -- the primitive `f_beta` -/

/-- `f_beta` on the basis: `0` on `L`'s, and `eq:primitive`'s 0-based form
on `F_u` (`H1` in `T`'s two hazards, converted from the manuscript's
1-based `sum_{j=1}^n`).-/
noncomputable def fBetaBasis (n : ℕ) : IndexedBasis n → IndexedMod n
  | .inl _ => 0
  | .inr u => ∑ j : Fin n,
      (betaN n (evenIdx n j) • eN (Lof (oddIdx n j) u) - betaN n (oddIdx n j) • eN
        (Lof (evenIdx n j) u))

/-- `f_beta` extended `P`-linearly to all of `IndexedMod n`.-/
noncomputable def fBetaN (n : ℕ) (x : IndexedMod n) : IndexedMod n :=
  ∑ i : IndexedBasis n, x i • fBetaBasis n i

/-! ## A generic `P`-bilinear extension from a basis pairing

Shared by `GammaBetaN` (G2) and `deltaFN` (G3): both are `∑∑ (x i * y j) •
F i j` for their own basis function `F`, so this one combinator and its
bilinearity toolkit serve both, instead of duplicating `bracketN`'s own
toolkit (frozen, `Indexed.lean`) for each new pairing. -/

noncomputable def bilinearExtend {n : ℕ} (F : IndexedBasis n → IndexedBasis n → IndexedMod n)
    (x y : IndexedMod n) : IndexedMod n :=
  ∑ i : IndexedBasis n, ∑ j : IndexedBasis n, (x i * y j) • F i j

/-! ## Finite-sum bilinearity toolkit for `bracketN`, general `n`

`IndexedJacobi.lean`'s own toolkit is specific to `IndexedBasis n`-indexed
sums (U5's own need); G4 needs the analogue for `Fin (2*n)`-indexed sums
(over `v`'s components), plus `bracketN_neg_left` (only the right-argument
form was needed before), plus the trivial `bracketN_zero_left/right`. -/

/-! ## G2 -- the coefficient `Gamma_beta`, all four sectors -/

/-- `eq:gamma-lf`: `Gamma_beta(L_uv,F_w) = (1/2)(beta_u L_vw + beta_v L_uw)`.-/
noncomputable def gammaLFn (n : ℕ) (u v w : Fin (2 * n)) : IndexedMod n :=
  cratN n (1 / 2) • (betaN n u • eN (Lof v w) + betaN n v • eN (Lof u w))

/-- `eq:gamma-ff`: `Gamma_beta(F_u,F_v) = -(1/2)(beta_u F_v + beta_v F_u)`.-/
noncomputable def gammaFFn (n : ℕ) (u v : Fin (2 * n)) : IndexedMod n :=
  -(cratN n (1 / 2) • (betaN n u • eN (Fof v) + betaN n v • eN (Fof u)))

/-- `Gamma_beta` on all four basis sectors: `eq:gamma-ll` (`0`),
`gammaLFn` (LF, transcribed), `-gammaLFn` (FL, the declared convention of
G2 -- `Gamma_beta(Y,X) = -(-1)^{p(X)p(Y)} Gamma_beta(X,Y)` specialized to
`X=L_uv,Y=F_w`, giving `-(1/2)(beta_uL_vw+beta_vL_uw)` exactly), and
`gammaFFn` (FF, transcribed).-/
noncomputable def GammaBetaBasis (n : ℕ) : IndexedBasis n → IndexedBasis n → IndexedMod n
  | .inl ⟨(_, _), _⟩, .inl ⟨(_, _), _⟩ => 0
  | .inl ⟨(u, v), _⟩, .inr w => gammaLFn n u v w
  | .inr w, .inl ⟨(u, v), _⟩ => -gammaLFn n u v w
  | .inr u, .inr v => gammaFFn n u v

noncomputable def GammaBetaN (n : ℕ) (x y : IndexedMod n) : IndexedMod n :=
  bilinearExtend (GammaBetaBasis n) x y

/-! ## G3 -- the coboundary operator, for a general odd `P`-linear map `f` -/

/-- `(delta f)(X,Y) = [f(X),Y]_0 + (-1)^{p(X)}[X,f(Y)]_0 - f([X,Y]_0)` on
basis pairs, using the accepted `bracketN` and `gsignN n (parity X) 1 =
(-1)^{p(X)}` (`gsignN`'s own `q=1` slice).-/
noncomputable def deltaFBasis (n : ℕ) (f : IndexedMod n → IndexedMod n) (X Y : IndexedBasis n) :
    IndexedMod n :=
  bracketN n (f (eN X)) (eN Y) + gsignN n (parity X) 1 • bracketN n (eN X) (f (eN Y))
    - f (bracketN n (eN X) (eN Y))

noncomputable def deltaFN (n : ℕ) (f : IndexedMod n → IndexedMod n) (x y : IndexedMod n) :
    IndexedMod n :=
  bilinearExtend (deltaFBasis n f) x y

/-! ## G4, LL sector -/

/-! ## Helper facts feeding the LF, FF and FL sectors -/

/-- The manuscript's `F(v) = sum_t v_t F_t`, notation-hazard-checked
(`T`'s second named hazard: `v` is a vector here, never an index).-/
noncomputable def FVecBeta (n : ℕ) : IndexedMod n := ∑ t : Fin (2 * n), vN n t • eN (Fof t)

/-! ## G4, LF sector -/

/-! ## G4, FF sector -/

/-! ## G4, FL sector: corroboration of the declared convention, not an
independent check -/

/-! ## G4: assembled on all basis pairs -/

/-! ## G5: extension to arbitrary elements of `IndexedMod n`

Unconditional -- since `GammaBetaN` and `deltaFN` are both the
`bilinearExtend` of basis functions agreeing pointwise (`G4`), functional
equality on all of `IndexedMod n` follows directly (`Finset.sum_congr`
twice), with no separate homogeneous-decomposition argument needed. This
subsumes the homogeneous-hypothesis shape the design/packet describes
(`bracketN_super_skew_homog`/`jacobiN_homog`'s own shape), stated below as
a direct corollary. -/

end Indexed
end InhomogeneousDeformations
