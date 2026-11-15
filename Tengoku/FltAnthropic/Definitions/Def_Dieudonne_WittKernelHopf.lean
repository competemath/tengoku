import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittGroupHopf
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfIdealQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

omit hp in
@[simp] theorem coeff_frobeniusFun_iterate (c : ℕ) (x : TruncatedWittVector p n R) (i : Fin n) :
    (frobeniusFun^[c] x).coeff i = x.coeff i ^ p ^ c := by
  induction c generalizing x with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply', coeff_frobeniusFun, ih, ← pow_mul, ← pow_succ]

omit hp in
theorem frobeniusFun_iterate_mk (c : ℕ) (g : Fin n → R) :
    frobeniusFun^[c] (TruncatedWittVector.mk p g) = TruncatedWittVector.mk p fun i => g i ^ p ^ c :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_frobeniusFun_iterate, TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_mk]

theorem map_frobeniusFun_iterate (f : R →+* S) (c : ℕ) (x : TruncatedWittVector p n R) :
    map f (frobeniusFun^[c] x) = frobeniusFun^[c] (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, coeff_frobeniusFun_iterate, map_pow]

theorem frobeniusFun_iterate_add (hR : (p : R) = 0) (c : ℕ) (x y : TruncatedWittVector p n R) :
    frobeniusFun^[c] (x + y) = frobeniusFun^[c] x + frobeniusFun^[c] y := by
  induction c generalizing x y with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, frobeniusFun_add hR]

theorem frobeniusFun_iterate_zero (c : ℕ) : frobeniusFun^[c] (0 : TruncatedWittVector p n R) = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Function.iterate_succ_apply', ih, frobeniusFun_zero]

theorem frobeniusFun_iterate_neg (hR : (p : R) = 0) (c : ℕ) (x : TruncatedWittVector p n R) :
    frobeniusFun^[c] (-x) = -frobeniusFun^[c] x := by
  have h := frobeniusFun_iterate_add hR c (-x) x
  rw [neg_add_cancel, frobeniusFun_iterate_zero] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

end TruncWitt

namespace WittKernel

open WittGroup TruncWitt

variable (k : Type u) [CommRing k] (p : ℕ) (n a b : ℕ) (J : Type v)

noncomputable def relation (j : J) (i : Fin n) : WittGroup.Coord k p n J :=
  X j i ^ p ^ b - X j i ^ p ^ a

noncomputable def ideal : Ideal (WittGroup.Coord k p n J) :=
  Ideal.span (Set.range fun ji : J × Fin n => relation k p n a b J ji.1 ji.2)

variable {k p n a b J}

theorem relation_mem_ideal (j : J) (i : Fin n) : relation k p n a b J j i ∈ ideal k p n a b J :=
  Ideal.subset_span ⟨(j, i), rfl⟩

theorem ideal_le_iff {I : Ideal (WittGroup.Coord k p n J)} :
    ideal k p n a b J ≤ I ↔ ∀ j i, relation k p n a b J j i ∈ I := by
  constructor
  · exact fun h j i => h (relation_mem_ideal j i)
  · intro h
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact h j i

variable [hp : Fact p.Prime]

theorem ringHom_X_pow {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) (j : J)
    (i : Fin n) (c : ℕ) :
    g (X j i) ^ p ^ c = (frobeniusFun^[c] (TruncWitt.map (p := p) g (univ k p n j))).coeff i := by
  rw [coeff_frobeniusFun_iterate, coeff_map, coeff_univ]

theorem ringHom_relation {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) (j : J)
    (i : Fin n) :
    g (relation k p n a b J j i) =
      (frobeniusFun^[b] (TruncWitt.map (p := p) g (univ k p n j))).coeff i -
        (frobeniusFun^[a] (TruncWitt.map (p := p) g (univ k p n j))).coeff i := by
  rw [relation, map_sub, map_pow, map_pow, ringHom_X_pow, ringHom_X_pow]

theorem ideal_le_ker_iff {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) :
    ideal k p n a b J ≤ RingHom.ker g ↔
      ∀ j, frobeniusFun^[b] (TruncWitt.map (p := p) g (univ k p n j)) =
        frobeniusFun^[a] (TruncWitt.map (p := p) g (univ k p n j)) := by
  rw [ideal_le_iff]
  simp only [RingHom.mem_ker, ringHom_relation, sub_eq_zero]
  exact ⟨fun h j => TruncatedWittVector.ext fun i => h j i,
    fun h j i => congrArg (TruncatedWittVector.coeff i) (h j)⟩

section HopfIdeal

variable [CharP k p]

variable (k p n a b J)

local notation "𝒪" => WittGroup.Coord k p n J
local notation "I" => ideal k p n a b J
local notation "πI" => (Ideal.Quotient.mk (ideal k p n a b J))

omit [CharP k p] in

theorem frobeniusFun_iterate_map_mk_univ (j : J) :
    frobeniusFun^[b] (TruncWitt.map (p := p) πI (univ k p n j)) =
      frobeniusFun^[a] (TruncWitt.map (p := p) πI (univ k p n j)) :=
  (ideal_le_ker_iff (πI : 𝒪 →+* 𝒪 ⧸ I)).1 (by rw [Ideal.mk_ker]) j

instance isHopfIdeal : (ideal k p n a b J).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero := by

    let h : 𝒪 →ₐ[k] (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).comp
        (Bialgebra.comulAlgHom k 𝒪)
    suffices hle : I ≤ RingHom.ker h.toRingHom by
      intro x hx
      exact hle hx
    rw [ideal_le_iff]
    intro j i
    rw [RingHom.mem_ker]

    set y : TruncatedWittVector p n (𝒪 ⧸ I) := TruncWitt.map (p := p) πI (univ k p n j) with hy
    let iL : (𝒪 ⧸ I) →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.includeLeft : (𝒪 ⧸ I) →ₐ[k] _).toRingHom
    let iR : (𝒪 ⧸ I) →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.includeRight : (𝒪 ⧸ I) →ₐ[k] _).toRingHom
    have hX : ∀ i, h.toRingHom (X j i) = (TruncWitt.map iL y + TruncWitt.map iR y).coeff i := by
      intro i
      let g : 𝒪 ⊗[k] 𝒪 →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).toRingHom
      have h1 : h.toRingHom (X j i) = g (WittGroup.comul k p n J (X j i)) := rfl
      rw [h1, ringHom_comul_X]
      congr 2
      · refine TruncatedWittVector.ext fun i => ?_
        rw [TruncatedWittVector.coeff_mk, coeff_map, hy, coeff_map, coeff_univ]
        rfl
      · refine TruncatedWittVector.ext fun i => ?_
        rw [TruncatedWittVector.coeff_mk, coeff_map, hy, coeff_map, coeff_univ]
        rfl
    have hp0 : (p : (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I)) = 0 := natCast_eq_zero_of_algebra k p _
    have hpow : ∀ c : ℕ, h.toRingHom (X j i) ^ p ^ c =
        (TruncWitt.map iL (frobeniusFun^[c] y) + TruncWitt.map iR (frobeniusFun^[c] y)).coeff i := by
      intro c
      rw [hX i, ← coeff_frobeniusFun_iterate, frobeniusFun_iterate_add hp0,
        map_frobeniusFun_iterate, map_frobeniusFun_iterate]
    change h.toRingHom (relation k p n a b J j i) = 0
    rw [relation, map_sub, map_pow, map_pow, hpow, hpow, hy, frobeniusFun_iterate_map_mk_univ,
      sub_self]
  counit_eq_zero := by
    suffices hle : I ≤ RingHom.ker (Bialgebra.counitAlgHom k 𝒪).toRingHom by
      intro x hx
      exact hle hx
    rw [ideal_le_iff]
    intro j i
    rw [RingHom.mem_ker]
    change Coalgebra.counit (R := k) (relation k p n a b J j i) = 0
    rw [relation, counit_def, map_sub, map_pow, map_pow, counit_X,
      zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_pow (pow_ne_zero _ hp.out.ne_zero), sub_self]
  antipode_mem := by
    suffices hle : I ≤ (ideal k p n a b J).comap (WittGroup.antipode k p n J) by
      intro x hx
      have := hle hx
      rwa [Ideal.mem_comap, ← antipode_def] at this
    rw [ideal_le_iff]
    intro j i
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    set g : 𝒪 →+* 𝒪 ⧸ I := (πI).comp (WittGroup.antipode k p n J).toRingHom with hg
    set y : TruncatedWittVector p n (𝒪 ⧸ I) := TruncWitt.map (p := p) πI (univ k p n j) with hy
    have hX : ∀ i, g (X j i) = (-y).coeff i := by
      intro i
      rw [hg, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, antipode_X,
        ← coeff_map (p := p), map_neg, hy]
    have hp0 : (p : 𝒪 ⧸ I) = 0 := natCast_eq_zero_of_algebra k p _
    have hpow : ∀ c : ℕ, g (X j i) ^ p ^ c = (-(frobeniusFun^[c] y)).coeff i := by
      intro c
      rw [hX i, ← coeff_frobeniusFun_iterate, frobeniusFun_iterate_neg hp0]
    change g (relation k p n a b J j i) = 0
    rw [relation, map_sub, map_pow, map_pow, hpow, hpow, hy, frobeniusFun_iterate_map_mk_univ,
      sub_self]

end HopfIdeal

variable (k p n a b J)

abbrev Coord : Type (max u v) := WittGroup.Coord k p n J ⧸ ideal k p n a b J

variable [CharP k p]

noncomputable def π : WittGroup.Coord k p n J →ₐc[k] Coord k p n a b J :=
  HopfAlgebra.quotientBialgHom k (ideal k p n a b J)

variable {k p n a b J}

@[simp] theorem π_apply (x : WittGroup.Coord k p n J) :
    π k p n a b J x = Ideal.Quotient.mk (ideal k p n a b J) x := rfl

variable (k p n a b J)

noncomputable def tauto (j : J) : wittHom k p n (Coord k p n a b J) :=
  wittHomMap p n (π k p n a b J) (univHom j)

variable {k p n a b J}

@[simp] theorem coe_tauto (j : J) :
    (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)) =
      TruncWitt.map (p := p) (Ideal.Quotient.mk (ideal k p n a b J)) (univ k p n j) := rfl

@[simp] theorem coeff_tauto (j : J) (i : Fin n) :
    (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)).coeff i =
      π k p n a b J (X j i) := by
  rw [coe_tauto, coeff_map, coeff_univ, π_apply]

theorem frobenius_iterate_tauto (j : J) :
    (wittHomFrobenius k p n (Coord k p n a b J))^[b] (tauto k p n a b J j) =
      (wittHomFrobenius k p n (Coord k p n a b J))^[a] (tauto k p n a b J j) := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (((wittHomFrobenius k p n (Coord k p n a b J))^[c] x : wittHom k p n (Coord k p n a b J)) :
        TruncatedWittVector p n (Coord k p n a b J)) = frobeniusFun^[c] (x : TruncatedWittVector p n _) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_wittHomFrobenius, ih]
  apply Subtype.ext
  rw [key, key, coe_tauto]
  exact frobeniusFun_iterate_map_mk_univ k p n a b J j

theorem verschiebung_iterate_tauto (j : J) :
    (wittHomVerschiebung k p n (Coord k p n a b J))^[n] (tauto k p n a b J j) = 0 :=
  wittHomVerschiebung_iterate_eq_zero _

variable (k p n a b J) in

noncomputable def tautoClass (j : J) : DieudonneModule k p (Coord k p n a b J) :=
  DieudonneModule.of k p (Coord k p n a b J) n (tauto k p n a b J j)

theorem tautoClass_def (j : J) :
    tautoClass k p n a b J j = DieudonneModule.of k p (Coord k p n a b J) n (tauto k p n a b J j) :=
  rfl

theorem frobenius_iterate_tautoClass (j : J) :
    (DieudonneModule.frobenius k p (Coord k p n a b J))^[b] (tautoClass k p n a b J j) =
      (DieudonneModule.frobenius k p (Coord k p n a b J))^[a] (tautoClass k p n a b J j) := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (DieudonneModule.frobenius k p (Coord k p n a b J))^[c] (DieudonneModule.of k p _ n x) =
        DieudonneModule.of k p _ n ((wittHomFrobenius k p n (Coord k p n a b J))^[c] x) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        DieudonneModule.frobenius_of]
  rw [tautoClass_def, key, key, frobenius_iterate_tauto]

theorem verschiebung_iterate_tautoClass (j : J) :
    (DieudonneModule.verschiebung k p (Coord k p n a b J))^[n] (tautoClass k p n a b J j) = 0 := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (DieudonneModule.verschiebung k p (Coord k p n a b J))^[c] (DieudonneModule.of k p _ n x) =
        DieudonneModule.of k p _ n ((wittHomVerschiebung k p n (Coord k p n a b J))^[c] x) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        DieudonneModule.verschiebung_of]
  rw [tautoClass_def, key, verschiebung_iterate_tauto, map_zero]

section Points

variable {T : Type w} [CommRing T] [Algebra k T]

end Points

end WittKernel

end Deformation
