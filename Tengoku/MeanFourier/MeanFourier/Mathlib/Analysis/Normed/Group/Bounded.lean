module

public import Tengoku
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Topology.Bornology.Basic

public section

open Bornology

variable {α E : Type*} [NormedGroup E] {f : α → E}

/--
@isnad1 id=iff.0h3v.s5.d328f8f42c18 from=translated src=- shape=ef0f5255 vocab=00128187
-/
@[to_additive isBddFun_iff_exists_forall_norm_le]
lemma isBddFun_iff_exists_forall_norm_le' : IsBddFun f ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simp [IsBddFun, isBounded_iff_forall_norm_le']

/--
@isnad1 id=ex.1h3v.s5.deb7df945ea4 from=translated src=- shape=05000060 vocab=cd930e57
-/
alias ⟨Bornology.IsBddFun.exists_forall_norm_le, _⟩ := isBddFun_iff_exists_forall_norm_le

/--
@isnad1 id=ex.1h3v.s5.ec7098c14606 from=translated src=- shape=05000060 vocab=00128187
-/
@[to_additive existing Bornology.IsBddFun.exists_forall_norm_le]
alias ⟨Bornology.IsBddFun.exists_forall_norm_le', _⟩ := isBddFun_iff_exists_forall_norm_le'

/--
@isnad1 id=iff.0h2v.s4.2cceabfe51bd from=translated src=- shape=f705df84 vocab=88fbc2b5
-/
lemma isBddFun_iff_exists_forall_abs_le {f : α → ℝ} : IsBddFun f ↔ ∃ C, ∀ x, |f x| ≤ C :=
  isBddFun_iff_exists_forall_norm_le

/--
@isnad1 id=ex.1h2v.s4.677a2c219a78 from=translated src=- shape=62bc8c91 vocab=88fbc2b5
-/
alias ⟨Bornology.IsBddFun.exists_forall_abs_le, _⟩ := isBddFun_iff_exists_forall_abs_le
