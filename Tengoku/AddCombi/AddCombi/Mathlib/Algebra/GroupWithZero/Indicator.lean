module

public import Tengoku.AddCombi.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Tengoku

public section

open scoped Indicator

variable {F α β M₀ N₀ : Type*}

namespace Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

/--
@isnad1 id=eq.0h5v.s6.3cd6cfedc40c from=translated src=- shape=0e0b77ab vocab=d969854e
-/
lemma indicator_one_inter_apply (s t : Set α) (x : α) : 𝟭_[s ∩ t, M₀] x = 𝟭_[s] x * 𝟭_[t] x := by
  classical simp [indicator_apply, ← ite_and, and_comm]

/--
@isnad1 id=eq.0h4v.s7.5804ee858487 from=translated src=- shape=cec7bc19 vocab=d969854e
-/
lemma indicator_one_inter (s t : Set α) : 𝟭_[s ∩ t, M₀] = 𝟭_[s] * 𝟭_[t] :=
  funext <| indicator_one_inter_apply _ _

/--
@isnad1 id=eq.0h7v.s6.ee5378b91c8d from=translated src=- shape=b1b9a8ff vocab=9ff2c342
-/
lemma map_indicator_one [FunLike F M₀ N₀] [MonoidWithZeroHomClass F M₀ N₀] (f : F) (s : Set α)
    (x : α) : f (𝟭_[s] x) = 𝟭_[s] x := by classical exact MonoidWithZeroHom.map_ite_one_zero ..

variable (M₀) in
/--
@isnad1 id=eq.0h6v.s6.5a6f6fd03bc5 from=translated src=- shape=e2f1d51c vocab=8e657780
-/
@[simp] lemma indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    𝟭_[e '' s, M₀] b = 𝟭_[s] (e.symm b) := by classical simp [indicator_apply, ← e.eq_symm_apply]

variable [Nontrivial M₀] {a : α}

/--
@isnad1 id=iff.0h4v.s6.63c4729750d6 from=translated src=- shape=ff5b4ce1 vocab=8003e2a8
-/
@[local simp high] lemma indicator_one_apply_eq_zero : 𝟭_[s, M₀] a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff

/--
@isnad1 id=iff.0h4v.s6.c9fb7147e4c6 from=translated src=- shape=7b039207 vocab=8003e2a8
-/
lemma indicator_one_apply_ne_zero : 𝟭_[s, M₀] a ≠ 0 ↔ a ∈ s := by
  classical exact one_ne_zero.ite_ne_right_iff

/--
@isnad1 id=iff.0h3v.s6.b437322755b2 from=translated src=- shape=426342c8 vocab=3bb15f4c
-/
@[local simp high] lemma indicator_one_eq_zero : 𝟭_[s, M₀] = 0 ↔ s = ∅ := by
  simp [funext_iff, eq_empty_iff_forall_notMem]

/--
@isnad1 id=iff.0h3v.s6.9f4e0b082bfc from=translated src=- shape=b92c641c vocab=382d7913
-/
lemma indicator_one_ne_zero : 𝟭_[s, M₀] ≠ 0 ↔ s.Nonempty := by simp [nonempty_iff_ne_empty]

variable (M₀) in
/--
@isnad1 id=eq.0h3v.s5.c888d04d39c3 from=translated src=- shape=cc622632 vocab=1b213ceb
-/
@[local simp high] lemma support_indicator_one : 𝟭_[s, M₀].support = s := by
  ext; exact indicator_one_apply_ne_zero

end Set
-- Tengoku: 3 registration(s) of this module made local so they do not change other libraries (generated)
