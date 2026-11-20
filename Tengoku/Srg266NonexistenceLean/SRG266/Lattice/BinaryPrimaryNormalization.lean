/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimarySpan
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.OddPrimaryNorm
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.AnisotropicDiscriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W} {u v : W}

/--
@isnad1 id=not.6h6v.s10.d47cd0de69c3 from=translated src=- shape=f3626734 vocab=26ba9d52
-/
theorem IsMaximalIntegral.not_integral_norm_add_smul
    (hmax : IsMaximalIntegral B N) (hs : B.IsSymm)
    (hu : u ∈ B.dualSubmodule N) (hv : v ∈ B.dualSubmodule N)
    (hcross : B u v ∈ (1 : Submodule ℤ ℚ))
    (hunit : B u u ∉ (1 : Submodule ℤ ℚ)) (a : ℤ) :
    B (u + a • v) (u + a • v) ∉ (1 : Submodule ℤ ℚ) := by
  intro hnorm
  have hm := hmax.mem_of_dual_of_integral_norm hs
    ((B.dualSubmodule N).add_mem hu ((B.dualSubmodule N).smul_mem a hv)) hnorm
  have hpair := hu _ hm
  have heq : a • v = (a : ℚ) • v := by module
  rw [map_add, heq, map_smul, smul_eq_mul] at hpair
  have hc : (a : ℚ) * B u v ∈ (1 : Submodule ℤ ℚ) := by
    simpa only [zsmul_eq_mul] using (1 : Submodule ℤ ℚ).smul_mem a hcross
  exact hunit ((congrArg (fun q : ℚ => q ∈ (1 : Submodule ℤ ℚ))
    (add_sub_cancel_right (B u u) ((a : ℚ) * B u v))).mp (sub_mem hpair hc))

private theorem unit_norm_not_integral {p r k : ℤ} (hp : p ≠ 0)
    (hpn : ¬ p ∣ 1) (hcop : IsCoprime p r)
    (hn : B u u = (r : ℚ) / (p : ℚ) + 2 * (k : ℚ)) :
    B u u ∉ (1 : Submodule ℤ ℚ) := by
  intro h
  exact hpn (norm_denominator_unit hp hcop hn 1 (by simpa using h))

private theorem norm_add_smul (hs : B.IsSymm) (a : ℤ) :
    B (u + a • v) (u + a • v) =
      B u u + (a : ℚ)^2 * B v v + 2 * a * B u v := by
  have heq : a • v = (a : ℚ) • v := by module
  rw [heq]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hs.eq v u]
  ring

/--
@isnad1 id=ex.9h5v.s11.a5c1efe298a4 from=translated src=- shape=e008fd5c vocab=207fd38f
-/
theorem normalized_three_pair (hs : B.IsSymm) (hmax : IsMaximalIntegral B N)
    (hu : u ∈ B.dualSubmodule N) (hv : v ∈ B.dualSubmodule N)
    (hpu : (3 : ℤ) • u ∈ N) (hpv : (3 : ℤ) • v ∈ N)
    (hcross : B u v ∈ (1 : Submodule ℤ ℚ))
    (hnu : ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧ B u u = (r : ℚ) / 3 + 2 * (k : ℚ))
    (hnv : ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧ B v v = (r : ℚ) / 3 + 2 * (k : ℚ)) :
    ∃ x y : W, N ⊔ Submodule.span ℤ {x, y} = N ⊔ Submodule.span ℤ {u, v} ∧
      B x y ∈ (1 : Submodule ℤ ℚ) ∧
      (∃ k : ℤ, B x x = 2 / 3 + 2 * (k : ℚ)) ∧
      (∃ k : ℤ, B y y = 2 / 3 + 2 * (k : ℚ)) := by
  obtain ⟨r, k, hr, hru⟩ := hnu
  obtain ⟨s, l, hS, hsv⟩ := hnv
  obtain ⟨c, hc⟩ := mem_one_iff.mp hcross
  have hcop : IsCoprime (3 : ℤ) r := by
    rcases hr with rfl | rfl
    · exact ⟨1, -1, by norm_num⟩
    · exact ⟨-1, 1, by norm_num⟩
  have hnot := hmax.not_integral_norm_add_smul hs hu hv hcross
    (unit_norm_not_integral (by norm_num) (by norm_num) hcop hru) 1
  have hrs : r = s := by
    by_contra hne
    have hrS : r + s = 6 := by omega
    have hrSQ : (r : ℚ) + s = 6 := by exact_mod_cast hrS
    apply hnot
    refine mem_one_iff.mpr ⟨2 + 2 * k + 2 * l + 2 * c, ?_⟩
    rw [norm_add_smul hs, hru, hsv, ← hc]
    push_cast
    norm_num
    linarith
  subst s
  rcases hr with rfl | rfl
  · exact ⟨u, v, rfl, hcross, ⟨k, hru⟩, ⟨l, hsv⟩⟩
  · refine ⟨u + v, u - v,
      sup_span_pair_hadamard_eq ⟨-1, 1, by norm_num⟩ hpu hpv, ?_,
      ⟨k + l + c + 1, ?_⟩, ⟨k + l - c + 1, ?_⟩⟩
    · refine mem_one_iff.mpr ⟨2 * (k - l), ?_⟩
      simp only [map_add, LinearMap.add_apply, map_sub]
      rw [hs.eq v u, hru, hsv]
      push_cast
      ring
    · simp only [map_add, LinearMap.add_apply]
      rw [hs.eq v u, hru, hsv, ← hc]
      push_cast
      ring
    · simp only [map_sub, LinearMap.sub_apply]
      rw [hs.eq v u, hru, hsv, ← hc]
      push_cast
      ring

/--
@isnad1 id=ex.7h5v.s11.8f0f4c3e5f34 from=translated src=- shape=e0bcdbea vocab=a81c07ec
-/
theorem normalized_five_pair_of_unary (hs : B.IsSymm) (hmax : IsMaximalIntegral B N)
    (hu : u ∈ B.dualSubmodule N) (hv : v ∈ B.dualSubmodule N)
    (hcross : B u v ∈ (1 : Submodule ℤ ℚ))
    (hnu : ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧ B u u = (r : ℚ) / 5 + 2 * (k : ℚ))
    (hnv : ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧ B v v = (r : ℚ) / 5 + 2 * (k : ℚ)) :
    ∃ x y : W, N ⊔ Submodule.span ℤ {x, y} = N ⊔ Submodule.span ℤ {u, v} ∧
      B x y ∈ (1 : Submodule ℤ ℚ) ∧
      (∃ k : ℤ, B x x = 2 / 5 + 2 * (k : ℚ)) ∧
      (∃ k : ℤ, B y y = 4 / 5 + 2 * (k : ℚ)) := by
  obtain ⟨r, k, hr, hru⟩ := hnu
  obtain ⟨s, l, hS, hsv⟩ := hnv
  obtain ⟨c, hc⟩ := mem_one_iff.mp hcross
  have hcop : IsCoprime (5 : ℤ) r := by
    rcases hr with rfl | rfl
    · exact ⟨1, -2, by norm_num⟩
    · exact ⟨1, -1, by norm_num⟩
  have hnot := hmax.not_integral_norm_add_smul hs hu hv hcross
    (unit_norm_not_integral (by norm_num) (by norm_num) hcop hru) 2
  have hrs : r ≠ s := by
    intro hrs
    subst s
    apply hnot
    refine mem_one_iff.mpr ⟨r + 2 * k + 8 * l + 4 * c, ?_⟩
    rw [norm_add_smul hs, hru, hsv, ← hc]
    push_cast
    ring
  rcases hr with rfl | rfl
  · have hs4 : s = 4 := by omega
    subst s
    exact ⟨u, v, rfl, hcross, ⟨k, hru⟩, ⟨l, hsv⟩⟩
  · have hs2 : s = 2 := by omega
    subst s
    exact ⟨v, u, by rw [Set.pair_comm v u], by rwa [hs.eq], ⟨l, hsv⟩, ⟨k, hru⟩⟩

/--
@isnad1 id=ex.9h5v.s11.9ae1d836f452 from=translated src=- shape=f27d63dc vocab=140dbd43
-/
theorem normalized_five_pair (hs : B.IsSymm) (hmax : IsMaximalIntegral B N)
    (hu : u ∈ B.dualSubmodule N) (hv : v ∈ B.dualSubmodule N)
    (hpu : (5 : ℤ) • u ∈ N) (hpv : (5 : ℤ) • v ∈ N)
    (hcross : B u v ∈ (1 : Submodule ℤ ℚ))
    (hnu : ∃ m : ℤ, Even m ∧ ¬ (5 : ℤ) ∣ m ∧ 5 * B u u = (m : ℚ))
    (hnv : ∃ m : ℤ, Even m ∧ ¬ (5 : ℤ) ∣ m ∧ 5 * B v v = (m : ℚ)) :
    ∃ x y : W, N ⊔ Submodule.span ℤ {x, y} = N ⊔ Submodule.span ℤ {u, v} ∧
      B x y ∈ (1 : Submodule ℤ ℚ) ∧
      (∃ k : ℤ, B x x = 2 / 5 + 2 * (k : ℚ)) ∧
      (∃ k : ℤ, B y y = 4 / 5 + 2 * (k : ℚ)) := by
  obtain ⟨m, hm, hmu, hmq⟩ := hnu
  obtain ⟨n, hn, hnu, hnq⟩ := hnv
  obtain ⟨a, r, k, ha, hr, hru⟩ := normalized_norm_five hm hmu hmq
  obtain ⟨b, s, l, hb, hS, hsv⟩ := normalized_norm_five hn hnu hnq
  have hau : a • u = (a : ℚ) • u := by module
  have hbv : b • v = (b : ℚ) • v := by module
  have hnormu : B (a • u) (a • u) = (r : ℚ) / 5 + 2 * (k : ℚ) := by
    rw [hau]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    nlinarith [hru]
  have hnormv : B (b • v) (b • v) = (s : ℚ) / 5 + 2 * (l : ℚ) := by
    rw [hbv]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    nlinarith [hsv]
  have hcross' : B (a • u) (b • v) ∈ (1 : Submodule ℤ ℚ) := by
    rw [hau, hbv]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    simpa only [zsmul_eq_mul] using
      (1 : Submodule ℤ ℚ).smul_mem b ((1 : Submodule ℤ ℚ).smul_mem a hcross)
  obtain ⟨x, y, hspan, hxy, hxx, hyy⟩ := normalized_five_pair_of_unary hs hmax
    ((B.dualSubmodule N).smul_mem a hu) ((B.dualSubmodule N).smul_mem b hv)
    hcross' ⟨r, k, hr, hnormu⟩ ⟨s, l, hS, hnormv⟩
  refine ⟨x, y, hspan.trans ?_, hxy, hxx, hyy⟩
  have haB : ∃ d e : ℤ, a * d + 5 * e = 1 := by
    rcases ha with rfl | rfl
    · exact ⟨1, 0, by norm_num⟩
    · exact ⟨3, -1, by norm_num⟩
  have hbB : ∃ d e : ℤ, b * d + 5 * e = 1 := by
    rcases hb with rfl | rfl
    · exact ⟨1, 0, by norm_num⟩
    · exact ⟨3, -1, by norm_num⟩
  obtain ⟨d, e, hde⟩ := haB
  obtain ⟨f, g, hfg⟩ := hbB
  exact sup_span_pair_smul_eq hpu hpv hde hfg

/--
@isnad1 id=ex.4h4v.s10.c40d04eee776 from=translated src=- shape=5a597a07 vocab=e1c12e6e
-/
theorem GlueBasis.normalized_binary_three (S : GlueBasis B N 3) (hR : S.rank = 2)
    (hs : B.IsSymm) (hmax : IsMaximalIntegral B N) (he : IsEven B N) :
    ∃ x y : W, torsionPart B N 3 = N ⊔ Submodule.span ℤ {x, y} ∧
      B x y ∈ (1 : Submodule ℤ ℚ) ∧
      (∃ k : ℤ, B x x = 2 / 3 + 2 * (k : ℚ)) ∧
      (∃ k : ℤ, B y y = 2 / 3 + 2 * (k : ℚ)) := by
  rcases S with ⟨rank, hle, vec, hmem, hspan, hortho, hdiag, hind⟩
  dsimp at hR
  subst rank
  have hn (i : Fin 2) : ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧
      B (vec i) (vec i) = (r : ℚ) / 3 + 2 * (k : ℚ) := by
    obtain ⟨m, hm, hmq⟩ := hdiag i
    have heven : Even m := even_numerator_of_odd_multiple (by decide : Odd (3 : ℤ)) he
      (mem_torsionPart.mp (hmem i)).2 hmq
    exact norm_mod_two_three heven hm hmq
  obtain ⟨x, y, hxyspan, hxy, hxx, hyy⟩ := normalized_three_pair hs hmax
    (mem_torsionPart.mp (hmem 0)).1 (mem_torsionPart.mp (hmem 1)).1
    (mem_torsionPart.mp (hmem 0)).2 (mem_torsionPart.mp (hmem 1)).2
    (hortho 0 1 (by decide)) (hn 0) (hn 1)
  refine ⟨x, y, ?_, hxy, hxx, hyy⟩
  rw [hxyspan]
  simpa only [range_fin_two_eq_pair] using hspan

/--
@isnad1 id=ex.4h4v.s10.ae85bb553973 from=translated src=- shape=5a597a07 vocab=e1c12e6e
-/
theorem GlueBasis.normalized_binary_five (S : GlueBasis B N 5) (hR : S.rank = 2)
    (hs : B.IsSymm) (hmax : IsMaximalIntegral B N) (he : IsEven B N) :
    ∃ x y : W, torsionPart B N 5 = N ⊔ Submodule.span ℤ {x, y} ∧
      B x y ∈ (1 : Submodule ℤ ℚ) ∧
      (∃ k : ℤ, B x x = 2 / 5 + 2 * (k : ℚ)) ∧
      (∃ k : ℤ, B y y = 4 / 5 + 2 * (k : ℚ)) := by
  rcases S with ⟨rank, hle, vec, hmem, hspan, hortho, hdiag, hind⟩
  dsimp at hR
  subst rank
  have hn (i : Fin 2) : ∃ m : ℤ, Even m ∧ ¬ (5 : ℤ) ∣ m ∧
      5 * B (vec i) (vec i) = (m : ℚ) := by
    obtain ⟨m, hm, hmq⟩ := hdiag i
    exact ⟨m, even_numerator_of_odd_multiple (by decide : Odd (5 : ℤ)) he
      (mem_torsionPart.mp (hmem i)).2 hmq, hm, hmq⟩
  obtain ⟨x, y, hxyspan, hxy, hxx, hyy⟩ := normalized_five_pair hs hmax
    (mem_torsionPart.mp (hmem 0)).1 (mem_torsionPart.mp (hmem 1)).1
    (mem_torsionPart.mp (hmem 0)).2 (mem_torsionPart.mp (hmem 1)).2
    (hortho 0 1 (by decide)) (hn 0) (hn 1)
  refine ⟨x, y, ?_, hxy, hxx, hyy⟩
  rw [hxyspan]
  simpa only [range_fin_two_eq_pair] using hspan

end SRG266.Lattice
