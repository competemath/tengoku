import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_AtkinLehnerDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
noncomputable section
open Matrix UpperHalfPlane CongruenceSubgroup ModularForm OnePoint
open scoped MatrixGroups ModularForm Manifold

namespace FreyPackage.ModMCarrier

section Cocycle
variable {R M d : ℕ}

def diagMatInt (d : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(d : ℤ), 0; 0, 1]

end Cocycle

section Cusps
variable {R M d : ℕ}

def heckeDiagMatrixQ (hd : d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hd)

end Cusps

section Rescale
variable {R M d : ℕ} [NeZero M]

end Rescale

section AtkinLehnerSpecialization
variable {M q' : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q')

end AtkinLehnerSpecialization

end FreyPackage.ModMCarrier
