import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddMonoidAlgebra_finite_setOf_withConv_algHom_pow_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddMonoidAlgebra_finite_setOf_withConv_algHom_pow_eq_one

set_option autoImplicit false

universe u

/--
@isnad1 id=finite.1h3v.s9.41f9b2913abc from=translated src=- shape=5a65157e vocab=35e3c1ac
-/
theorem solution
    (κ : Type u) [CommRing κ] [IsDomain κ] (t n : ℕ) (hn : 0 < n) :
    {χ : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ) | χ ^ n = 1}.Finite := by
  classical

  have hmul : ∀ (ψ ψ' : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ)) (g : Fin t → ℤ),
      (ψ * ψ').ofConv (AddMonoidAlgebra.single g 1) =
        ψ.ofConv (AddMonoidAlgebra.single g 1) * ψ'.ofConv (AddMonoidAlgebra.single g 1) := by
    intro ψ ψ' g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hone : ∀ g : Fin t → ℤ, (1 : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ)).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
    intro g
    rw [AlgHom.convOne_def]
    simp [AddMonoidAlgebra.counit_single]
  have hpow : ∀ (ψ : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ)) (k : ℕ) (g : Fin t → ℤ),
      (ψ ^ k).ofConv (AddMonoidAlgebra.single g 1) = (ψ.ofConv (AddMonoidAlgebra.single g 1)) ^ k := by
    intro ψ k g
    induction k with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ k ih => rw [pow_succ, pow_succ, hmul, ih]

  let ev : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ) → (Fin t → κ) :=
    fun χ i => χ.ofConv (AddMonoidAlgebra.single (Pi.single i 1) 1)

  have hroots : {x : κ | x ^ n = 1}.Finite := by
    have : {x : κ | x ^ n = 1} = ↑((Polynomial.nthRoots n (1 : κ)).toFinset) := by
      ext x; simp [Polynomial.mem_nthRoots hn]
    rw [this]; exact Finset.finite_toSet _
  have himage : ev '' {χ | χ ^ n = 1} ⊆ Set.pi Set.univ (fun _ : Fin t => {x : κ | x ^ n = 1}) := by
    rintro _ ⟨χ, hχ, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const]
    intro i
    have h := congrArg (fun ψ : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ) =>
      ψ.ofConv (AddMonoidAlgebra.single (Pi.single i 1) 1)) (Set.mem_ofPred_eq ▸ hχ)
    rw [hpow, hone] at h
    exact h

  have hinj : Set.InjOn ev {χ | χ ^ n = 1} := by
    intro χ _ χ' _ h

    have key : (AddMonoidAlgebra.lift κ κ (Fin t → ℤ)).symm χ.ofConv =
        (AddMonoidAlgebra.lift κ κ (Fin t → ℤ)).symm χ'.ofConv := by
      apply Multiplicative.monoidHom_ext
      apply AddMonoidHom.functions_ext
      intro i x
      suffices hs : (MonoidHom.toAdditiveRight ((AddMonoidAlgebra.lift κ κ (Fin t → ℤ)).symm χ.ofConv)).comp
            (AddMonoidHom.single (fun _ : Fin t => ℤ) i) =
          (MonoidHom.toAdditiveRight ((AddMonoidAlgebra.lift κ κ (Fin t → ℤ)).symm χ'.ofConv)).comp
            (AddMonoidHom.single (fun _ : Fin t => ℤ) i) by
        have := congrArg (fun f => f x) hs
        simpa using this
      apply AddMonoidHom.ext_int
      change Additive.ofMul (χ.ofConv (AddMonoidAlgebra.single (Pi.single i 1) 1)) =
        Additive.ofMul (χ'.ofConv (AddMonoidAlgebra.single (Pi.single i 1) 1))
      exact congrArg Additive.ofMul (congrFun h i)
    apply WithConv.ofConv_injective
    exact (AddMonoidAlgebra.lift κ κ (Fin t → ℤ)).symm.injective key
  exact Set.Finite.of_finite_image ((Set.Finite.pi (fun _ => hroots)).subset himage) hinj
