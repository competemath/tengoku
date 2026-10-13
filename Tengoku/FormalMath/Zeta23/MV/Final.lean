/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Tengoku.FormalMath.Zeta23.MV.Eigen
import Tengoku.FormalMath.Zeta23.MV.Duality

/-!
# The Montgomery–Vaughan weighted Hilbert inequality

`eigen_bound` (`Zeta23/MV/Eigen.lean`) is exactly `EigenBound 13`; the spectral reduction of
`Duality.lean` turns it into `MVDiag 13` and, via polarization (`Zeta23/MV.lean`), into the
bilinear `∃ C > 0, MVHilbert C` of `Hypotheses.lean` (C = 26) — discharging `PaperInputs.MV`.
-/

noncomputable section

namespace Zeta23
namespace MV

/--
@isnad1 id=eigenbou.0h0v.s3.1914439eff14 from=translated src=- shape=e590c3e1 vocab=21386575
-/
theorem eigenBound_thirteen : EigenBound 13 :=
  fun _ι _ _ _freq _δ h u hu μ heig => eigen_bound h u hu μ heig

/-- **`MVDiag 13`** — the weighted Hilbert inequality, literature (diagonal) form.
@isnad1 id=mvdiag.0h0v.s3.8c7c881b5684 from=translated src=- shape=e590c3e1 vocab=4ccf553d
-/
theorem mvDiag_thirteen : MVDiag 13 := mvDiag_of_eigenBound eigenBound_thirteen

/-- **H-MV:** `∃ C > 0, MVHilbert C` (the field `PaperInputs.MV`).
@isnad1 id=ex.0h0v.s4.8ac3857c64ad from=translated src=- shape=8b03eb04 vocab=16bf103f
-/
theorem mv_hilbert : ∃ C : ℝ, 0 < C ∧ MVHilbert C :=
  mvHilbert_of_eigenBound (by norm_num) eigenBound_thirteen

end MV
end Zeta23

end
