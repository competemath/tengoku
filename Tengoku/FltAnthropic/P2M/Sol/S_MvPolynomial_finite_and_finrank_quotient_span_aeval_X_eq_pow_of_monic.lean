import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic

set_option autoImplicit false

universe u v

noncomputable section

open Polynomial

namespace MonogenicTensorPower

variable {k : Type u} [Field k] (f : Polynomial k)

def I (σ : Type*) : Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range fun i : σ => Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ k) f)

abbrev Q (σ : Type*) : Type _ := MvPolynomial σ k ⧸ I f σ

variable {f}

/--
@isnad1 id=mem.0h4v.s8.a6c594a01ddd from=translated src=- shape=2b5ca221 vocab=2efcb285
-/
theorem aeval_X_mem (σ : Type*) (i : σ) :
    Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ k) f ∈ I f σ :=
  Ideal.subset_span ⟨i, rfl⟩

/--
@isnad1 id=eq.0h4v.s10.e4caff17c968 from=translated src=- shape=c0c66b68 vocab=21459ea0
-/
theorem mk_aeval_X (σ : Type*) (i : σ) :
    Ideal.Quotient.mk (I f σ) (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ k) f) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (aeval_X_mem σ i)

/--
@isnad1 id=le.1h5v.s9.7a3ff520b094 from=translated src=- shape=f94815df vocab=2486d206
-/
theorem I_le_ker {σ : Type*} {S : Type*} [CommRing S] [Algebra k S] (φ : MvPolynomial σ k →ₐ[k] S)
    (h : ∀ i, Polynomial.aeval (φ (MvPolynomial.X i)) f = 0) : I f σ ≤ RingHom.ker φ := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  change φ (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ k) f) = 0
  rw [← Polynomial.aeval_algHom_apply, h i]

/--
@isnad1 id=eq.0h5v.s9.fe90a2e3a70a from=translated src=- shape=fd7c2736 vocab=17a71022
-/
theorem I_eq_map_rename {σ τ : Type*} (e : σ ≃ τ) :
    I f τ = (I f σ).map ((MvPolynomial.renameEquiv k e : MvPolynomial σ k ≃ₐ[k] MvPolynomial τ k) :
      MvPolynomial σ k →+* MvPolynomial τ k) := by
  unfold I
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Polynomial.aeval (MvPolynomial.X (e.symm t) : MvPolynomial σ k) f, ⟨e.symm t, rfl⟩, ?_⟩
    change MvPolynomial.rename e (Polynomial.aeval (MvPolynomial.X (e.symm t) : MvPolynomial σ k) f) = _
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.rename_X, Equiv.apply_symm_apply]
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨e s, ?_⟩
    change _ = MvPolynomial.rename e (Polynomial.aeval (MvPolynomial.X s : MvPolynomial σ k) f)
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.rename_X]

def equivOfEquiv {σ τ : Type*} (e : σ ≃ τ) : Q f σ ≃ₐ[k] Q f τ :=
  Ideal.quotientEquivAlg (I f σ) (I f τ) (MvPolynomial.renameEquiv k e) (I_eq_map_rename e)

/--
@isnad1 id=eq.0h3v.s7.8d65d1ba4037 from=translated src=- shape=6def2b0d vocab=3cffda04
-/
theorem I_eq_bot_of_isEmpty (σ : Type*) [IsEmpty σ] : I f σ = ⊥ := by
  unfold I
  rw [Set.range_eq_empty, Ideal.span_empty]

def equivOfIsEmpty (σ : Type*) [IsEmpty σ] : Q f σ ≃ₐ[k] k :=
  have hker : I f σ = RingHom.ker (MvPolynomial.isEmptyAlgEquiv k σ : MvPolynomial σ k →ₐ[k] k) := by
    rw [I_eq_bot_of_isEmpty]
    exact ((RingHom.injective_iff_ker_eq_bot _).1 (MvPolynomial.isEmptyAlgEquiv k σ).injective).symm
  (Ideal.quotientEquivAlgOfEq k hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (MvPolynomial.isEmptyAlgEquiv k σ).surjective)

section OptionStep

variable (f) (σ : Type*)

abbrev R : Type _ := Q f σ

def g : Polynomial (R f σ) := f.map (algebraMap k (R f σ))

abbrev S : Type _ := AdjoinRoot (g f σ)

variable {σ}

/--
@isnad1 id=monic.1h3v.s6.1033b1e71141 from=translated src=- shape=2e356c2c vocab=9225b486
-/
theorem g_monic (hf : f.Monic) : (g f σ).Monic := hf.map _

/--
@isnad1 id=eq.0h3v.s10.211633bcad77 from=translated src=- shape=b4368a01 vocab=26f2eefa
-/
theorem aeval_root_eq_zero : Polynomial.aeval (AdjoinRoot.root (g f σ)) f = 0 := by
  rw [← Polynomial.aeval_map_algebraMap (R f σ), ← g.eq_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

def ψ₀ : R f σ →ₐ[k] S f σ := IsScalarTower.toAlgHom k (R f σ) (S f σ)

/--
@isnad1 id=eq.0h4v.s10.742e6aca4252 from=translated src=- shape=06a0c12b vocab=322b7f94
-/
theorem ψ₀_apply (r : R f σ) : ψ₀ f r = AdjoinRoot.of (g f σ) r := rfl

def φ : MvPolynomial (Option σ) k →ₐ[k] S f σ :=
  MvPolynomial.aeval fun o => Option.elim o (AdjoinRoot.root (g f σ))
    fun i => ψ₀ f (Ideal.Quotient.mk (I f σ) (MvPolynomial.X i))

/--
@isnad1 id=eq.0h3v.s9.1e8244fd3669 from=translated src=- shape=b68fe50c vocab=5d5318cb
-/
theorem φ_X_none : φ f (σ := σ) (MvPolynomial.X none) = AdjoinRoot.root (g f σ) := by
  rw [φ, MvPolynomial.aeval_X]; rfl

/--
@isnad1 id=eq.0h4v.s10.a4a4ade97543 from=translated src=- shape=a831a286 vocab=c33011d8
-/
theorem φ_X_some (i : σ) :
    φ f (MvPolynomial.X (some i)) = ψ₀ f (Ideal.Quotient.mk (I f σ) (MvPolynomial.X i)) := by
  rw [φ, MvPolynomial.aeval_X]; rfl

/--
@isnad1 id=eq.0h3v.s9.bbb9890f90cd from=translated src=- shape=0f94db70 vocab=c54336b8
-/
theorem φ_comp_rename :
    (φ f).comp (MvPolynomial.rename (some : σ → Option σ)) =
      (ψ₀ f).comp (Ideal.Quotient.mkₐ k (I f σ)) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, φ_X_some]
  rfl

/--
@isnad1 id=le.0h3v.s9.fe6d1b61b12e from=translated src=- shape=b5bb6b86 vocab=0cbc37ad
-/
theorem I_le_ker_φ : I f (Option σ) ≤ RingHom.ker (φ f (σ := σ)) := by
  refine I_le_ker _ fun o => ?_
  cases o with
  | none => rw [φ_X_none]; exact aeval_root_eq_zero f
  | some i =>
    rw [φ_X_some]
    change Polynomial.aeval (((ψ₀ f).comp (Ideal.Quotient.mkₐ k (I f σ))) (MvPolynomial.X i)) f = 0
    rw [Polynomial.aeval_algHom_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mk_aeval_X, map_zero]

def φbar : Q f (Option σ) →ₐ[k] S f σ :=
  Ideal.Quotient.liftₐ (I f (Option σ)) (φ f) fun _ hx => I_le_ker_φ f hx

/--
@isnad1 id=eq.0h4v.s10.b156806f8ec0 from=translated src=- shape=36bf504b vocab=e845caa1
-/
theorem φbar_mk (x : MvPolynomial (Option σ) k) :
    φbar f (Ideal.Quotient.mk (I f (Option σ)) x) = φ f x := rfl

def j : R f σ →ₐ[k] Q f (Option σ) :=
  Ideal.Quotient.liftₐ (I f σ)
    ((Ideal.Quotient.mkₐ k (I f (Option σ))).comp (MvPolynomial.rename (some : σ → Option σ)))
    fun x hx => I_le_ker _ (fun i => by
      rw [AlgHom.comp_apply, MvPolynomial.rename_X, Polynomial.aeval_algHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, mk_aeval_X]) hx

/--
@isnad1 id=eq.0h4v.s11.f7b4856c1b33 from=translated src=- shape=0b1b6b3a vocab=3f01b5ef
-/
theorem j_mk (x : MvPolynomial σ k) :
    j f (Ideal.Quotient.mk (I f σ) x) = Ideal.Quotient.mk (I f (Option σ)) (MvPolynomial.rename some x) := rfl

/--
@isnad1 id=eq.0h3v.s10.56ce66a74007 from=translated src=- shape=415da241 vocab=84c2a21b
-/
theorem eval₂_j_g :
    Polynomial.eval₂ (j f (σ := σ)).toRingHom (Ideal.Quotient.mk (I f (Option σ)) (MvPolynomial.X none))
      (g f σ) = 0 := by
  rw [g, Polynomial.eval₂_map]
  have hcomp : (j f (σ := σ)).toRingHom.comp (algebraMap k (R f σ)) = algebraMap k (Q f (Option σ)) :=
    RingHom.ext fun r => (j f).commutes r
  rw [hcomp]
  change Polynomial.aeval (Ideal.Quotient.mk (I f (Option σ)) (MvPolynomial.X none)) f = 0
  have := mk_aeval_X (f := f) (Option σ) none
  rwa [← Ideal.Quotient.mkₐ_eq_mk k, ← Polynomial.aeval_algHom_apply] at this

def ψring : S f σ →+* Q f (Option σ) :=
  AdjoinRoot.lift (j f (σ := σ)).toRingHom (Ideal.Quotient.mk (I f (Option σ)) (MvPolynomial.X none))
    (eval₂_j_g f)

def ψ : S f σ →ₐ[k] Q f (Option σ) :=
  { ψring f (σ := σ) with
    commutes' := fun r => by
      change ψring f (algebraMap k (S f σ) r) = _
      rw [IsScalarTower.algebraMap_apply k (R f σ) (S f σ), AdjoinRoot.algebraMap_eq, ψring,
        AdjoinRoot.lift_of]
      exact (j f).commutes r }

/--
@isnad1 id=eq.0h3v.s10.2d1ad0e15ee1 from=translated src=- shape=00b0116d vocab=672ce7cd
-/
theorem ψ_root : ψ f (AdjoinRoot.root (g f σ)) = Ideal.Quotient.mk (I f (Option σ)) (MvPolynomial.X none) :=
  AdjoinRoot.lift_root (eval₂_j_g f)

/--
@isnad1 id=eq.0h4v.s10.3ac8257ad51d from=translated src=- shape=99f99622 vocab=842e83c3
-/
theorem ψ_of (r : R f σ) : ψ f (AdjoinRoot.of (g f σ) r) = j f r :=
  AdjoinRoot.lift_of (eval₂_j_g f)

/--
@isnad1 id=eq.0h3v.s9.04659bbb4919 from=translated src=- shape=d5e83e95 vocab=d6fb2e2a
-/
theorem ψ_comp_φbar : (ψ f).comp (φbar f (σ := σ)) = AlgHom.id k (Q f (Option σ)) := by
  refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun o => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply,
    Ideal.Quotient.mkₐ_eq_mk, φbar_mk]
  cases o with
  | none => rw [φ_X_none, ψ_root]
  | some i => rw [φ_X_some, ψ₀_apply, ψ_of, j_mk, MvPolynomial.rename_X]

/--
@isnad1 id=injectiv.0h3v.s9.fdc95f83a2b0 from=translated src=- shape=16a67860 vocab=19ba623a
-/
theorem φbar_injective : Function.Injective (φbar f (σ := σ)) := by
  intro x y hxy
  have h := congrArg (ψ f) hxy
  have hx := AlgHom.congr_fun (ψ_comp_φbar f (σ := σ)) x
  have hy := AlgHom.congr_fun (ψ_comp_φbar f (σ := σ)) y
  rw [AlgHom.comp_apply, AlgHom.id_apply] at hx hy
  rwa [hx, hy] at h

/--
@isnad1 id=surjecti.0h3v.s9.0aad0efd625a from=translated src=- shape=54fa33e7 vocab=0b427bbe
-/
theorem φ_surjective : Function.Surjective (φ f (σ := σ)) := by
  intro s
  induction s using AdjoinRoot.induction_on with
  | ih q =>
    change AdjoinRoot.mk (g f σ) q ∈ Set.range (φ f)
    rw [← AlgHom.coe_range]
    induction q using Polynomial.induction_on with
    | C r =>
      obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [AdjoinRoot.mk_C]
      refine ⟨MvPolynomial.rename some r₀, ?_⟩
      have := AlgHom.congr_fun (φ_comp_rename f (σ := σ)) r₀
      rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
      change φ f (MvPolynomial.rename some r₀) = _
      rw [this]
      rfl
    | add q₁ q₂ h₁ h₂ =>
      rw [map_add]
      exact Subalgebra.add_mem _ h₁ h₂
    | monomial m r h =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      refine Subalgebra.mul_mem _ h ⟨MvPolynomial.X none, ?_⟩
      change φ f (MvPolynomial.X none) = _
      exact φ_X_none f

/--
@isnad1 id=surjecti.0h3v.s9.f79ba7c1ab64 from=translated src=- shape=16a67860 vocab=c1c27a43
-/
theorem φbar_surjective : Function.Surjective (φbar f (σ := σ)) := by
  intro s
  obtain ⟨x, rfl⟩ := φ_surjective f s
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

def linearEquivS : Q f (Option σ) ≃ₗ[k] S f σ :=
  LinearEquiv.ofBijective (φbar f (σ := σ)).toLinearMap ⟨φbar_injective f, φbar_surjective f⟩

/--
@isnad1 id=and.3h3v.s10.1cabf8fb3976 from=translated src=- shape=c9d909c3 vocab=cdb107c6
-/
theorem step (hf : f.Monic) [Fintype σ] (hfin : Module.Finite k (R f σ))
    (hrk : Module.finrank k (R f σ) = f.natDegree ^ Fintype.card σ) :
    Module.Finite k (Q f (Option σ)) ∧
      Module.finrank k (Q f (Option σ)) = f.natDegree ^ Fintype.card (Option σ) := by
  rw [Fintype.card_option, pow_succ]
  rcases Nat.eq_zero_or_pos f.natDegree with hd | hd
  ·
    have hf1 : f = 1 := (hf.natDegree_eq_zero).1 hd
    have htop : I f (Option σ) = ⊤ := by
      have h1 : Polynomial.aeval (MvPolynomial.X none : MvPolynomial (Option σ) k) f = 1 := by
        rw [hf1, map_one]
      rw [Ideal.eq_top_iff_one, ← h1]
      exact aeval_X_mem _ none
    haveI : Subsingleton (Q f (Option σ)) := Ideal.Quotient.subsingleton_iff.2 htop
    haveI : Subsingleton (Submodule k (Q f (Option σ))) := (Submodule.subsingleton_iff k).2 inferInstance
    refine ⟨⟨?_⟩, ?_⟩
    · rw [Subsingleton.elim (⊤ : Submodule k (Q f (Option σ))) ⊥]
      exact Submodule.fg_bot
    · rw [Module.finrank_zero_of_subsingleton, hd, mul_zero]
  · haveI : Module.Finite k (R f σ) := hfin
    haveI : Nontrivial (R f σ) := Module.nontrivial_of_finrank_pos (R := k) (by
      rw [hrk]; exact pow_pos hd _)
    let pb := AdjoinRoot.powerBasis' (g_monic f (σ := σ) hf)
    haveI : Module.Free (R f σ) (S f σ) := Module.Free.of_basis pb.basis
    haveI : Module.Finite (R f σ) (S f σ) := Module.Finite.of_basis pb.basis
    have hS : Module.finrank (R f σ) (S f σ) = f.natDegree := by
      rw [pb.finrank, AdjoinRoot.powerBasis'_dim, g, hf.natDegree_map]
    haveI : Module.Finite k (S f σ) := Module.Finite.trans (R f σ) (S f σ)
    have hkS : Module.finrank k (S f σ) = f.natDegree ^ Fintype.card σ * f.natDegree := by
      rw [← Module.finrank_mul_finrank k (R f σ) (S f σ), hrk, hS]
    refine ⟨Module.Finite.equiv (linearEquivS f (σ := σ)).symm, ?_⟩
    rw [(linearEquivS f (σ := σ)).finrank_eq, hkS]

end OptionStep

/--
@isnad1 id=and.1h3v.s9.8220dee21b11 from=translated src=- shape=5eface80 vocab=f82999bb
-/
theorem main (hf : f.Monic) (ι : Type v) [Fintype ι] :
    Module.Finite k (Q f ι) ∧ Module.finrank k (Q f ι) = f.natDegree ^ Fintype.card ι := by
  refine Fintype.induction_empty_option
    (P := fun (α : Type v) (_ : Fintype α) =>
      Module.Finite k (Q f α) ∧ Module.finrank k (Q f α) = f.natDegree ^ Fintype.card α) ?_ ?_ ?_ ι
  · intro α β _ e ih
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨hfin, hrk⟩ := ih
    haveI := hfin
    refine ⟨Module.Finite.equiv (equivOfEquiv (f := f) e).toLinearEquiv, ?_⟩
    rw [← (equivOfEquiv (f := f) e).toLinearEquiv.finrank_eq, hrk]
    congr 1
    exact Fintype.card_congr e
  · refine ⟨Module.Finite.equiv (equivOfIsEmpty (f := f) PEmpty).symm.toLinearEquiv, ?_⟩
    rw [(equivOfIsEmpty (f := f) PEmpty).toLinearEquiv.finrank_eq, Module.finrank_self,
      Fintype.card_eq_zero, pow_zero]
  · intro α _ ih
    exact step f hf ih.1 ih.2

end MonogenicTensorPower

end

/--
@isnad1 id=and.1h3v.s11.600e401bf225 from=translated src=- shape=6662afd6 vocab=82d6fda4
-/
theorem solution
    (k : Type u) [Field k] (ι : Type v) [Finite ι] (f : Polynomial k) (hf : f.Monic) :
    Module.Finite k (MvPolynomial ι k ⧸
        Ideal.span (Set.range fun i : ι => Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι k) f)) ∧
      Module.finrank k (MvPolynomial ι k ⧸
        Ideal.span (Set.range fun i : ι => Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι k) f)) =
        f.natDegree ^ Nat.card ι := by
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact MonogenicTensorPower.main hf ι
