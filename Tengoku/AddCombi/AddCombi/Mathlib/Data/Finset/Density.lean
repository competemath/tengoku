module

public import Tengoku

import Tengoku.AddCombi.AddCombi.Mathlib.Algebra.Order.Ring.NNRat

public section
attribute [local simp] NNRat.cast_sub


namespace Finset
variable {K α β : Type*} [DivisionRing K] [CharZero K] [Fintype α] [Fintype β]
  {s t : Finset α} {a : α}

/--
@isnad1 id=eq.0h4v.s6.d6414bc3a49f from=translated src=- shape=dcfe0eb8 vocab=dd08ce36
-/
@[simp] lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [dens, mul_div_mul_comm]

variable [DecidableEq α]

/--
@isnad1 id=iff.0h3v.s5.a281a5fc58c3 from=translated src=- shape=c5d021f7 vocab=66477e49
-/
lemma dens_union_eq_dens_add_dens : (s ∪ t).dens = s.dens + t.dens ↔ Disjoint s t := by
  rw [← dens_union_add_dens_inter]; simp [disjoint_iff_inter_eq_empty]

/--
@isnad1 id=eq.1h3v.s5.eb8efdcd8e4c from=translated src=- shape=8158e452 vocab=28e6a1b5
-/
@[grind =]
lemma dens_sdiff_of_subset (h : s ⊆ t) : (t \ s).dens = t.dens - s.dens := by
  suffices (t \ s).dens = (t \ s ∪ s).dens - s.dens by rwa [sdiff_union_of_subset h] at this
  rw [dens_union_of_disjoint sdiff_disjoint, add_tsub_cancel_right]

/--
@isnad1 id=eq.0h4v.s6.e461ca39b3c3 from=translated src=- shape=5b5b86c2 vocab=a38878f4
-/
lemma cast_dens_inter : ((s ∩ t).dens : K) = s.dens + t.dens - (s ∪ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact dens_inter_add_dens_union ..

/--
@isnad1 id=eq.0h4v.s6.410e6d5dd274 from=translated src=- shape=5b5b86c2 vocab=a38878f4
-/
lemma cast_dens_union : ((s ∪ t).dens : K) = s.dens + t.dens - (s ∩ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact dens_union_add_dens_inter ..

/--
@isnad1 id=eq.1h4v.s6.4a5be29db555 from=translated src=- shape=ee119ed2 vocab=6110c1e0
-/
lemma cast_dens_sdiff (h : s ⊆ t) : ((t \ s).dens : K) = t.dens - s.dens := by
  rw [dens_sdiff_of_subset h, NNRat.cast_sub (dens_mono h)]

end Finset
