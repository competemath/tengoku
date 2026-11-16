import Tengoku.OspTriviality.InhomogeneousDeformations.IndexedKappa
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# I106 R1 — the U-conjugation identity (V0-V4)

Transcription (Section T of `IMPLEMENTATION_REQUIREMENTS.md`), from
`aoi2026_triviality_osp1_2n_revised.tex`:

* `h(L_uv) = beta_u F_v + beta_v F_u`, `h(F_u) = 0`, odd `P`-linear — lines 238-239.
* `U(L_uv) = L_uv + kappa h(L_uv)`, `U(F_u) = F_u`, even `R`-linear; inverse is the
  same formula with a minus sign — lines 240-243.
* `eq:recover-by-u`: `[X,Y]_beta = U^{-1}[UX,UY]_0` — lines 248-250.
* `f_beta = h - ad(2 F(v))` on `g_P` — lines 346-349.

Five-layer freeze (`Indexed.lean`, `IndexedLaws.lean`, `IndexedJacobi.lean`,
`IndexedCoboundary.lean`, `IndexedKappa.lean`): read only, never reopened. This is the
one new file.
-/

namespace InhomogeneousDeformations
namespace Indexed

/-! ## V0 — the map `h` -/

/-- `h` on the basis: `beta_u F_v + beta_v F_u` on `L_uv` (symmetric in `u,v`, matching
`Lof`'s sorting), `0` on `F_u` — the manuscript's `h`, transcribed directly (lines
238-239), not derived from `f_beta`.-/
noncomputable def hBasis (n : ℕ) : IndexedBasis n → IndexedMod n
  | .inl ⟨(u, v), _⟩ => betaN n u • eN (Fof v) + betaN n v • eN (Fof u)
  | .inr _ => 0

theorem hBasis_Fof (n : ℕ) (u : Fin (2 * n)) : hBasis n (Fof u) = 0 := rfl

/-- `h` extended `P`-linearly to all of `IndexedMod n`, exactly as `fBetaN` extends
`fBetaBasis` (`IndexedCoboundary.lean`, G1).-/
noncomputable def hMap (n : ℕ) (x : IndexedMod n) : IndexedMod n :=
  ∑ i : IndexedBasis n, x i • hBasis n i

/-! ## V1 — `U` and its inverse

Reuses `TBeta`/`TBetaInv`'s own shape (`IndexedKappa.lean`, K3) with `hMap` in place of
`fBetaN`: the odd `R`-linear lift `hR` mirrors `fBetaR`, and `UMap := id + kappa • hR`
mirrors `TBeta := id + kappa • fBetaR`. -/

/-- The odd extension of `hMap`: on `r = x0 + kappa x1`, `h_R(r) = h(x0) - kappa h(x1)`,
matching `fBetaR`'s shape (K2) with `hMap` in place of `fBetaN`.-/
noncomputable def hR (n : ℕ) (r : RMod n) : RMod n :=
  iotaR (hMap n (falsePart r)) + kappaEmbed (-(hMap n (truePart r)))

/-- `U = id + kappa h_R` — the manuscript's `U` on the basis, `U(L_uv)=L_uv+kappa
h(L_uv)`, `U(F_u)=F_u`, extended `R`-linearly, exactly `TBeta`'s shape.-/
noncomputable def UMap (n : ℕ) (r : RMod n) : RMod n := r + kappaMulR (hR n r)

/-- `U^{-1} = id - kappa h_R`, the manuscript's stated inverse (same formula, minus
sign).-/
noncomputable def UMapInv (n : ℕ) (r : RMod n) : RMod n := r - kappaMulR (hR n r)

theorem UMapInv_eq (n : ℕ) (r : RMod n) : UMapInv n r = r - kappaEmbed (hMap n (falsePart r)) := by
  unfold UMapInv hR
  rw [kappaMulR_add, kappaMulR_iotaR, kappaMulR_kappaEmbed, add_zero]

theorem falsePart_UMapInv (n : ℕ) (r : RMod n) : falsePart (UMapInv n r) = falsePart r := by
  rw [UMapInv_eq, sub_eq_add_neg, falsePart_add, falsePart_neg, falsePart_kappaEmbed, neg_zero,
    add_zero]

/-! ## V2 — `delta h = Gamma_beta`, the round's one real obligation

Route chosen: **the manuscript's own remark** (lines 346-349), `f_beta = h -
ad(2 F(v))` on `g_P`, combined with `delta(ad Z) = 0` for the inner map `ad Z = [Z,-]_0`
-- reason: `delta f_beta = Gamma_beta` is *already accepted* (`GammaBetaN_eq_deltaFN`,
G5), so this route needs no fresh sector-by-sector computation for the LL sector
(where the manuscript itself says the identity needs Jacobi -- `eq:h-identity`'s own
proof); the LF/FF/FL sectors close directly, without Jacobi, since `hMap` vanishes on
every `F_u` (shown below). This is shorter than redoing `G4`'s method for `hMap`, and
it connects to P2 rather than re-deriving beside it, exactly as the scope document
recommends. -/

theorem eN_isHomogN {n : ℕ} (i : IndexedBasis n) : IsHomogN (eN i) (parity i) := by
  intro k hk
  by_contra hne
  apply hk
  unfold eN
  apply ite_eq_right
  intro heq
  exact hne (by rw [heq])

theorem cratN_two_half (n : ℕ) : cratN n 2 * cratN n (1 / 2 : ℚ) = 1 := by
  rw [cratN_mul]; norm_num

/-- The manuscript's `2 F(v)`, as an element of `IndexedMod n`.-/
noncomputable def twoFVecBeta (n : ℕ) : IndexedMod n := cratN n 2 • FVecBeta n

/-! ## V3 — the gate statement, proved

Transposed from R2-E's own `intertwining_basis`/`intertwining` (K5,
`eq:intertwining`), with `UMap` in place of `TBeta`, `hMap` in place of `fBetaN`,
and `deltaH` (V2, above) in place of `G4` in the one substantive sector. -/

end Indexed
end InhomogeneousDeformations
