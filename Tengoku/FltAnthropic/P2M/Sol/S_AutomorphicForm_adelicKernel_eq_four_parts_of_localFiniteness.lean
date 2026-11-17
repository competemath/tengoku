import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness

set_option autoImplicit false

open Matrix Polynomial AutomorphicForm

open scoped NumberField

noncomputable section

namespace M4aP3B
namespace Rows

variable {K : Type*} [Field K]

/--
@isnad1 id=eq.0h2v.s8.9ba425349303 from=translated src=- shape=aa3f0239 vocab=6eb9b9f2
-/
theorem charpoly_smul_one (c : K) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)).charpoly = (X - C c) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp only [Matrix.trace_smul, Matrix.trace_one, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, smul_eq_mul, mul_one, Nat.cast_ofNat, map_mul, map_pow, map_ofNat]
  ring

/--
@isnad1 id=iff.1h4v.s8.e760baa2f4b9 from=translated src=- shape=551f1f22 vocab=111847b9
-/
theorem isRoot_iff_of_sq {p : K[X]} {a : K} (h : p = (X - C a) ^ 2) (x : K) :
    p.IsRoot x ↔ x = a := by
  subst h
  simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_C, sq_eq_zero_iff, sub_eq_zero]

/--
@isnad1 id=iff.1h5v.s8.92e5df8eb1b9 from=translated src=- shape=f6dd6c8b vocab=1e493e8b
-/
theorem isRoot_iff_of_pair {p : K[X]} {a b : K} (h : p = (X - C a) * (X - C b)) (x : K) :
    p.IsRoot x ↔ x = a ∨ x = b := by
  subst h
  simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero]

/--
@isnad1 id=or.0h2v.s5.00bdec19b9a9 from=translated src=- shape=cc2fd8e0 vocab=5f000b44
-/
theorem classification_charpoly (M : Matrix (Fin 2) (Fin 2) K) :
    IsCentralType M ∨ IsEllipticType M ∨ IsHyperbolicType M ∨ IsUnipotentType M := by
  by_cases hroot : ∀ a : K, ¬M.charpoly.IsRoot a
  · exact Or.inr (Or.inl hroot)
  · push Not at hroot
    obtain ⟨a, ha⟩ := hroot
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha
    have hmonic : M.charpoly.Monic := Matrix.charpoly_monic M
    have hdeg : M.charpoly.natDegree = 2 := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hXa : (X - C a).Monic := monic_X_sub_C a
    have hqmonic : q.Monic := by
      have hm := hmonic
      rw [hq] at hm
      exact hXa.of_mul_monic_left hm
    have hqdeg : q.natDegree = 1 := by
      have h2 : ((X - C a) * q).natDegree = 2 := by rw [← hq]; exact hdeg
      rw [hXa.natDegree_mul hqmonic, natDegree_X_sub_C] at h2
      omega
    obtain ⟨b, hqb⟩ : ∃ b : K, q = X - C b :=
      ⟨-(q.coeff 0), by rw [map_neg, sub_neg_eq_add]; exact hqmonic.eq_X_add_C hqdeg⟩
    have hfact : M.charpoly = (X - C a) * (X - C b) := by rw [hq, hqb]
    by_cases hab : a = b
    · rw [← hab] at hfact
      have hsq : M.charpoly = (X - C a) ^ 2 := by rw [hfact, sq]
      by_cases hc : IsCentralType M
      · exact Or.inl hc
      · exact Or.inr (Or.inr (Or.inr ⟨hc, a, hsq⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, hab, hfact⟩))

/--
@isnad1 id=not.1h2v.s4.ea2a7821ecfe from=translated src=- shape=3f004897 vocab=4e4cf9f7
-/
theorem not_isUnipotentType_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsCentralType M) : ¬IsUnipotentType M := fun hu => hu.1 h

/--
@isnad1 id=not.1h2v.s4.65a62caa40bf from=translated src=- shape=3f004897 vocab=0a5d952b
-/
theorem not_isHyperbolicType_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsCentralType M) : ¬IsHyperbolicType M := by
  rintro ⟨a, b, hab, hfact⟩
  obtain ⟨c, hc⟩ := h
  have hsq : M.charpoly = (X - C c) ^ 2 := by rw [hc]; exact charpoly_smul_one c
  have ha : a = c := (isRoot_iff_of_sq hsq a).mp ((isRoot_iff_of_pair hfact a).mpr (Or.inl rfl))
  have hb : b = c := (isRoot_iff_of_sq hsq b).mp ((isRoot_iff_of_pair hfact b).mpr (Or.inr rfl))
  exact hab (ha.trans hb.symm)

/--
@isnad1 id=not.1h2v.s4.ce15301dd77d from=translated src=- shape=3f004897 vocab=d6826a28
-/
theorem not_isEllipticType_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsCentralType M) : ¬IsEllipticType M := by
  intro he
  obtain ⟨c, hc⟩ := h
  have hsq : M.charpoly = (X - C c) ^ 2 := by rw [hc]; exact charpoly_smul_one c
  exact he c ((isRoot_iff_of_sq hsq c).mpr rfl)

/--
@isnad1 id=not.1h2v.s4.2719bb7c3880 from=translated src=- shape=3f004897 vocab=b586c90c
-/
theorem not_isHyperbolicType_of_isUnipotentType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsUnipotentType M) : ¬IsHyperbolicType M := by
  rintro ⟨a, b, hab, hfact⟩
  obtain ⟨-, c, hsq⟩ := h
  have ha : a = c := (isRoot_iff_of_sq hsq a).mp ((isRoot_iff_of_pair hfact a).mpr (Or.inl rfl))
  have hb : b = c := (isRoot_iff_of_sq hsq b).mp ((isRoot_iff_of_pair hfact b).mpr (Or.inr rfl))
  exact hab (ha.trans hb.symm)

/--
@isnad1 id=not.1h2v.s4.661913bf88cb from=translated src=- shape=3f004897 vocab=158d7055
-/
theorem not_isEllipticType_of_isUnipotentType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsUnipotentType M) : ¬IsEllipticType M := by
  intro he
  obtain ⟨-, a, hsq⟩ := h
  exact he a ((isRoot_iff_of_sq hsq a).mpr rfl)

/--
@isnad1 id=not.1h2v.s4.c52f45348106 from=translated src=- shape=3f004897 vocab=81c8d498
-/
theorem not_isEllipticType_of_isHyperbolicType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsHyperbolicType M) : ¬IsEllipticType M := by
  intro he
  obtain ⟨a, b, -, hfact⟩ := h
  exact he a ((isRoot_iff_of_pair hfact a).mpr (Or.inl rfl))

/--
@isnad1 id=eq.0h1v.s7.8c235bc1dc48 from=translated src=- shape=96e40c64 vocab=067cc313
-/
theorem union_cells_eq_univ :
    centralCell K ∪ (ellipticCell K ∪ (hyperbolicCell K ∪ unipotentCell K)) = Set.univ := by
  ext γ
  simp only [Set.mem_union, Set.mem_univ, iff_true, centralCell, ellipticCell,
    hyperbolicCell, unipotentCell, Set.mem_ofPred_eq]
  exact classification_charpoly _

/--
@isnad1 id=disjoint.0h1v.s8.f81c71071439 from=translated src=- shape=95e328d4 vocab=04cc2275
-/
theorem disjoint_central_rest :
    Disjoint (centralCell K) (ellipticCell K ∪ (hyperbolicCell K ∪ unipotentCell K)) := by
  rw [Set.disjoint_left]
  rintro γ hc (he | hh | hu)
  · exact not_isEllipticType_of_isCentralType hc he
  · exact not_isHyperbolicType_of_isCentralType hc hh
  · exact not_isUnipotentType_of_isCentralType hc hu

/--
@isnad1 id=disjoint.0h1v.s8.d73e26f80753 from=translated src=- shape=abcba7a8 vocab=303e0e60
-/
theorem disjoint_elliptic_rest :
    Disjoint (ellipticCell K) (hyperbolicCell K ∪ unipotentCell K) := by
  rw [Set.disjoint_left]
  rintro γ he (hh | hu)
  · exact not_isEllipticType_of_isHyperbolicType hh he
  · exact not_isEllipticType_of_isUnipotentType hu he

/--
@isnad1 id=disjoint.0h1v.s8.2ac2b420db73 from=translated src=- shape=d088da8d vocab=510fb1b8
-/
theorem disjoint_hyperbolic_unipotent :
    Disjoint (hyperbolicCell K) (unipotentCell K) := by
  rw [Set.disjoint_left]
  exact fun γ hh hu => not_isHyperbolicType_of_isUnipotentType hu hh

section Split

variable (F : Type) [Field F] [NumberField F] {M : Type*} [AddCommMonoid M]

/--
@isnad1 id=eq.3h6v.s8.8c7311c52132 from=translated src=- shape=16b008f4 vocab=8b0c64df
-/
theorem adelicKernel_eq_four_parts_impl
    (h : AdelicKernelLocalFiniteness F)
    {f : AdelicGL2 (𝓞 F) F → M} {C : Set (AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) (hsupp : Function.support f ⊆ C)
    (x y : AdelicGL2 (𝓞 F) F) :
    adelicKernel F f x y
      = adelicKernelCentralPart F f x y + adelicKernelEllipticPart F f x y
        + adelicKernelHyperbolicPart F f x y + adelicKernelUnipotentPart F f x y := by
  have hfin : (Function.support fun γ : GL (Fin 2) F =>
      f (x⁻¹ * globalPoints (𝓞 F) F γ * y)).Finite := by
    apply Set.Finite.subset (h C hC x y)
    intro γ hγ
    exact hsupp hγ
  unfold adelicKernel adelicKernelCentralPart adelicKernelEllipticPart
    adelicKernelHyperbolicPart adelicKernelUnipotentPart
  rw [← finsum_mem_univ, ← union_cells_eq_univ (K := F),
    finsum_mem_union' (disjoint_central_rest (K := F)) (hfin.inter_of_right _)
      (hfin.inter_of_right _),
    finsum_mem_union' (disjoint_elliptic_rest (K := F)) (hfin.inter_of_right _)
      (hfin.inter_of_right _),
    finsum_mem_union' (disjoint_hyperbolic_unipotent (K := F)) (hfin.inter_of_right _)
      (hfin.inter_of_right _)]
  abel

end Split

end M4aP3B.Rows

set_option autoImplicit false
open Matrix
open scoped NumberField

/--
@isnad1 id=eq.3h6v.s8.8c7311c52132 from=translated src=- shape=16b008f4 vocab=8b0c64df
-/
theorem solution
    (F : Type) [Field F] [NumberField F] {M : Type*} [AddCommMonoid M]
    (h : AutomorphicForm.AdelicKernelLocalFiniteness F)
    {f : AutomorphicForm.AdelicGL2 (𝓞 F) F → M}
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) (hsupp : Function.support f ⊆ C)
    (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.adelicKernel F f x y
      = AutomorphicForm.adelicKernelCentralPart F f x y
        + AutomorphicForm.adelicKernelEllipticPart F f x y
        + AutomorphicForm.adelicKernelHyperbolicPart F f x y
        + AutomorphicForm.adelicKernelUnipotentPart F f x y := by
  exact M4aP3B.Rows.adelicKernel_eq_four_parts_impl F h hC hsupp x y
