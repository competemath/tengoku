module

public import Tengoku.KummerCriterion.KummerCriterion.GaussSum.SignInvariant.BlockDeterminant
import Tengoku.KummerCriterion.KummerCriterion.GaussSum.SignInvariant.VandermondeEndpoint
import Tengoku.Seed.Analysis.SpecialFunctions.Bernstein
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Branch choice for the quadratic Gauss sum

This file compares the determinant formula coming from the block decomposition
with the independent Vandermonde computation, and uses that comparison to fix
the quadratic Gauss-sum branch in the two mod-`4` cases.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The even complex Dirichlet characters modulo `p` have cardinality
`(p - 1) / 2`.
@isnad1 id=eq.1h1v.s6.3bfedb96b7d9 from=translated src=- shape=e827cb13 vocab=b3b84ea0
-/
theorem card_even_characters (hp₂ : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 := by
  classical
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  let O : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Odd
  have hdisj : Disjoint E O := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even : χ.Even := by simpa [E] using hχE
    have hχ_odd : χ.Odd := by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion : E ∪ O = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    ext χ
    simp only [E, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hneg_ne_one : (-1 : ZMod p) ≠ 1 := by
    have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp₂)⟩
    exact ZMod.neg_one_ne_one
  have hsum_zero :
      ∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p) = 0 :=
    DirichletCharacter.sum_characters_eq_zero (R := ℂ) (n := p) hneg_ne_one
  have hsum_split :
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) = (E.card : ℂ) - O.card := by
    have hsum_union :
        (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) =
          (E ∪ O).sum (fun χ => χ (-1 : ZMod p)) := by
      rw [hunion]
    have hsum_E : E.sum (fun χ => χ (-1 : ZMod p)) = E.card := by
      calc
        E.sum (fun χ => χ (-1 : ZMod p)) = E.sum (fun _ => (1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_even : χ.Even := by simpa [E] using hχ
          simpa [DirichletCharacter.Even] using hχ_even
        _ = E.card := by simp
    have hsum_O : O.sum (fun χ => χ (-1 : ZMod p)) = -(O.card : ℂ) := by
      calc
        O.sum (fun χ => χ (-1 : ZMod p)) = O.sum (fun _ => (-1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_odd : χ.Odd := by simpa [O] using hχ
          simpa [DirichletCharacter.Odd] using hχ_odd
        _ = -(O.card : ℂ) := by simp
    calc
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) =
          E.sum (fun χ => χ (-1 : ZMod p)) + O.sum (fun χ => χ (-1 : ZMod p)) := by
            rw [hsum_union, Finset.sum_union hdisj]
      _ = (E.card : ℂ) - O.card := by
            rw [hsum_E, hsum_O]
            simp [sub_eq_add_neg]
  have hbalance : (E.card : ℂ) - O.card = 0 := by
    rw [← hsum_split]
    exact hsum_zero
  have hsame : E.card = O.card := by
    have hsame_real : (E.card : ℝ) = O.card := by
      have hdiff_real : (E.card : ℝ) - O.card = 0 := by
        simpa using congrArg Complex.re hbalance
      nlinarith
    exact_mod_cast hsame_real
  have hcard_total : E.card + O.card = p - 1 := by
    calc
      E.card + O.card = (E ∪ O).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Fintype.card (DirichletCharacter ℂ p) := by
        rw [hunion, Finset.card_univ]
      _ = p - 1 := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
          Nat.totient_prime hp.out]
  have hcardE : E.card = (p - 1) / 2 := by
    omega
  simpa [E] using hcardE

/--
@isnad1 id=eq.0h2v.s7.d2abc198bc97 from=translated src=- shape=bf8222f5 vocab=544690ff
-/
theorem inv_eval_neg_one_eq (χ : DirichletCharacter ℂ p) :
    χ⁻¹ (-1 : ZMod p) = χ (-1) := by
  rw [MulChar.inv_apply', inv_neg_one]

/--
@isnad1 id=iff.0h2v.s5.45337696e3e7 from=translated src=- shape=b4299c56 vocab=8965dc6f
-/
theorem even_inv_iff {χ : DirichletCharacter ℂ p} : χ⁻¹.Even ↔ χ.Even := by
  simp [DirichletCharacter.Even, inv_eval_neg_one_eq (p := p) χ]

/--
@isnad1 id=odd.2h1v.s5.72c9bfb56f23 from=translated src=- shape=4367746b vocab=2a9e99e8
-/
theorem quadraticCharComplex_odd_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (quadraticCharComplex p).Odd := by
  simpa [DirichletCharacter.Odd] using
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄

/-- The even non-self-dual characters.-/
noncomputable def evenNonselfdualCharacterFinset : Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterFinset (p := p)).filter fun χ => χ.Even

/-- One representative from each even non-self-dual inverse pair.-/
noncomputable def evenNonselfdualCharacterReps : Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterReps (p := p)).filter fun χ => χ.Even

/--
@isnad1 id=iff.0h2v.s7.9a5d63272f3f from=translated src=- shape=6441d8b0 vocab=4c26fa9c
-/
theorem mem_evenNonselfdualCharacterFinset_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ evenNonselfdualCharacterFinset (p := p) ↔
      χ ∈ nonselfdualCharacterFinset (p := p) ∧ χ.Even := by
  simp [evenNonselfdualCharacterFinset]

/--
@isnad1 id=iff.0h2v.s7.9106979936a8 from=translated src=- shape=6441d8b0 vocab=6f472195
-/
theorem mem_evenNonselfdualCharacterReps_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ evenNonselfdualCharacterReps (p := p) ↔
      χ ∈ nonselfdualCharacterReps (p := p) ∧ χ.Even := by
  simp [evenNonselfdualCharacterReps]

/--
@isnad1 id=eq.1h1v.s7.ab6433312c15 from=translated src=- shape=077ac455 vocab=bee2c31a
-/
theorem evenNonselfdualCharacterFinset_eq_union_evenReps_image_inv (hp₂ : p ≠ 2) :
    evenNonselfdualCharacterFinset (p := p) =
      evenNonselfdualCharacterReps (p := p) ∪
        (evenNonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹ := by
  ext χ
  constructor
  · intro hχ
    rcases (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχnon, hχeven⟩
    rcases mem_reps_or_inv_mem_reps (p := p) (hp₂ := hp₂) hχnon with hχrep | hχinvrep
    · exact Finset.mem_union.mpr <| Or.inl <|
        (mem_evenNonselfdualCharacterReps_iff (p := p) χ).2 ⟨hχrep, hχeven⟩
    · have hχinv_even : (χ⁻¹ : DirichletCharacter ℂ p).Even :=
        (even_inv_iff (p := p) (χ := χ)).2 hχeven
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨χ⁻¹,
          (mem_evenNonselfdualCharacterReps_iff (p := p) (χ⁻¹)).2 ⟨hχinvrep, hχinv_even⟩,
          by simp⟩
  · intro hχ
    rcases Finset.mem_union.mp hχ with hχrep | hχimage
    · rcases (mem_evenNonselfdualCharacterReps_iff (p := p) χ).1 hχrep with
        ⟨hχrep', hχeven⟩
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).2
        ⟨(mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχrep' |>.1, hχeven⟩
    · rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, rfl⟩
      rcases (mem_evenNonselfdualCharacterReps_iff (p := p) ψ).1 hψrep with ⟨hψrep', hψeven⟩
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) ψ⁻¹).2
        ⟨inv_mem_nonselfdualCharacterFinset (p := p)
            ((mem_nonselfdualCharacterReps_iff (p := p) ψ).1 hψrep' |>.1),
          (even_inv_iff (p := p) (χ := ψ)).2 hψeven⟩

/--
@isnad1 id=disjoint.0h1v.s6.d56b7916218a from=translated src=- shape=356fe337 vocab=1b302387
-/
theorem disjoint_evenNonselfdualCharacterReps_image_inv :
    Disjoint (evenNonselfdualCharacterReps (p := p))
      ((evenNonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹) := by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, hψ⟩
  have hψrep' : ψ ∈ nonselfdualCharacterReps (p := p) :=
    (mem_evenNonselfdualCharacterReps_iff (p := p) ψ).1 hψrep |>.1
  have hχrep' : χ ∈ nonselfdualCharacterReps (p := p) :=
    (mem_evenNonselfdualCharacterReps_iff (p := p) χ).1 hχrep |>.1
  have hψinv : ψ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
    simpa [hψ] using hχrep'
  exact (inv_not_mem_nonselfdualCharacterReps (p := p) hψrep') hψinv

/--
@isnad1 id=eq.2h1v.s6.c24ec850c52e from=translated src=- shape=8aa86db3 vocab=89855654
-/
theorem card_evenNonselfdualCharacterFinset_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (evenNonselfdualCharacterFinset (p := p)).card = (p - 3) / 2 := by
  classical
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hquad_odd : (quadraticCharComplex p).Odd :=
    quadraticCharComplex_odd_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hq_not_even : ¬ (quadraticCharComplex p).Even :=
    DirichletCharacter.Odd.not_even (quadraticCharComplex p) hquad_odd
  have hrewrite :
      evenNonselfdualCharacterFinset (p := p) = E.erase (1 : DirichletCharacter ℂ p) := by
    ext χ
    constructor
    · intro hχ
      rcases (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχnon, hχeven⟩
      rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχnon with ⟨hχ1, _⟩
      simp [E, hχ1, hχeven]
    · intro hχ
      have hχ1 : χ ≠ (1 : DirichletCharacter ℂ p) := by
        simpa [E] using (Finset.mem_erase.mp hχ).1
      have hχeven : χ.Even := by
        simpa [E] using (Finset.mem_erase.mp hχ).2
      have hχquad : χ ≠ quadraticCharComplex p := fun hχquad =>
        hq_not_even (hχquad ▸ hχeven)
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).2
        ⟨(mem_nonselfdualCharacterFinset_iff (p := p) χ).2 ⟨hχ1, hχquad⟩, hχeven⟩
  rw [hrewrite, Finset.card_erase_of_mem]
  · rw [card_even_characters (p := p) hp₂]
    omega
  · simpa [E] using htriv_even

/--
@isnad1 id=eq.2h1v.s6.2661681f2278 from=translated src=- shape=8aa86db3 vocab=dfc3983c
-/
theorem card_evenNonselfdualCharacterReps_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (evenNonselfdualCharacterReps (p := p)).card = (p - 3) / 4 := by
  let reps := evenNonselfdualCharacterReps (p := p)
  have hsplit :
      (evenNonselfdualCharacterFinset (p := p)).card = reps.card + reps.card := by
    rw [evenNonselfdualCharacterFinset_eq_union_evenReps_image_inv (p := p) hp₂,
      Finset.card_union_of_disjoint (disjoint_evenNonselfdualCharacterReps_image_inv (p := p)),
      Finset.card_image_of_injective _ (fun χ ψ hEq => by simpa using congrArg Inv.inv hEq)]
  have hcard : (evenNonselfdualCharacterFinset (p := p)).card = (p - 3) / 2 :=
    card_evenNonselfdualCharacterFinset_of_mod_four_eq_three (p := p) hp₂ hp₄
  have htwice : (p - 3) / 2 = reps.card * 2 := by
    omega
  have hdiv : ((p - 3) / 2) / 2 = reps.card :=
    Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) htwice
  have hquarter : ((p - 3) / 2) / 2 = (p - 3) / 4 := by
    omega
  calc
    reps.card = ((p - 3) / 2) / 2 := hdiv.symm
    _ = (p - 3) / 4 := hquarter

/--
@isnad1 id=eq.0h1v.s7.36eef71d9780 from=translated src=- shape=f68497ea vocab=e3d2f004
-/
theorem prod_pairBlockDeterminants_eq_negOnePow_card_evenReps :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ (evenNonselfdualCharacterReps (p := p)).card := by
  classical
  let reps := nonselfdualCharacterReps (p := p)
  let g : DirichletCharacter ℂ p → ℂ := fun χ => if χ.Even then (-1 : ℂ) else 1
  have hrewrite :
      Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g := by
    refine Finset.prod_congr rfl ?_
    intro χ hχ
    rcases DirichletCharacter.even_or_odd χ with hχeven | hχodd
    · have hχeval : χ (-1 : ZMod p) = 1 := by
        simpa [DirichletCharacter.Even] using hχeven
      simp [g, hχeven, hχeval]
    · have hχeval : χ (-1 : ZMod p) = -1 := by
        simpa [DirichletCharacter.Odd] using hχodd
      have hχnot_even : ¬ χ.Even := DirichletCharacter.Odd.not_even χ hχodd
      simp [g, hχnot_even, hχeval]
  have hfilter :
      reps.filter (fun χ => g χ ≠ 1) = reps.filter fun χ => χ.Even := by
    ext χ
    by_cases hχeven : χ.Even
    · have hneq : (-1 : ℂ) ≠ 1 := by norm_num
      simp [g, hχeven, hneq]
    · simp [g, hχeven]
  calc
    Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g := hrewrite
    _ = Finset.prod (reps.filter fun χ => χ.Even) g := by
          rw [← hfilter, Finset.prod_filter_ne_one]
    _ = Finset.prod (reps.filter fun χ => χ.Even) (fun _ => (-1 : ℂ)) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          simp [g, (Finset.mem_filter.mp hχ).2]
    _ = (-1 : ℂ) ^ (evenNonselfdualCharacterReps (p := p)).card := by
          simp [evenNonselfdualCharacterReps, reps]

/--
@isnad1 id=eq.2h1v.s7.dc1830469c13 from=translated src=- shape=dc002ca7 vocab=a20655ab
-/
theorem prod_pairBlockDeterminants_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ ((p - 3) / 4) := by
  rw [prod_pairBlockDeterminants_eq_negOnePow_card_evenReps (p := p),
    card_evenNonselfdualCharacterReps_of_mod_four_eq_three (p := p) hp₂ hp₄]

/-- On the quadratic line, the block scalar is the negative normalized
quadratic Gauss sum in the `p ≡ 3 [ZMOD 4]` branch.
@isnad1 id=eq.2h1v.s6.bf7af8c3da17 from=translated src=- shape=33cac8de vocab=334269ab
-/
theorem normalizedDft_quadraticScalar_eq_neg_scaledGaussSum_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) =
      -((Real.sqrt p : ℂ)⁻¹ *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) := by
  have hq_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
    quadraticCharComplex_ne_one (p := p) hp₂
  simp [normalizedDftConstOneBasisScalar, hq_ne, quadraticCharComplex_inv (p := p),
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄]

/-- In the imaginary branch, the quadratic block scalar is `-I`.
@isnad1 id=eq.2h1v.s5.fa33e9354c30 from=translated src=- shape=7cdf4020 vocab=8dbe9ed2
-/
theorem normalizedDft_quadraticScalar_eq_neg_I_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) = -Complex.I := by
  let qScalar : ℂ := normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hdet_block :=
    det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
      (p := p) hp₂
  have hdet_vand := det_normalizedDft_eq_negOnePow_mul_I_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hpair := prod_pairBlockDeterminants_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hdet_q :
      LinearMap.det (normalizedDft p) = (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) := by
    calc
      LinearMap.det (normalizedDft p)
          = (-1 : ℂ) * (qScalar * (-1 : ℂ) ^ ((p - 3) / 4)) := by
              simpa [qScalar, hpair] using hdet_block
      _ = (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) := by
            ring
  have hpow_ne : ((-1 : ℂ) ^ ((p - 3) / 4)) ≠ 0 := by simp
  have heq : (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) =
      Complex.I * (-1 : ℂ) ^ ((p - 3) / 4) := by
    calc
      (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) = LinearMap.det (normalizedDft p) :=
        hdet_q.symm
      _ = (-1 : ℂ) ^ ((p - 3) / 4) * Complex.I := hdet_vand
      _ = Complex.I * (-1 : ℂ) ^ ((p - 3) / 4) := by ring
  have hneg : qScalar * (-1 : ℂ) = Complex.I :=
    mul_right_cancel₀ hpow_ne heq
  calc
    qScalar = qScalar * (1 : ℂ) := by ring
    _ = qScalar * ((-1 : ℂ) * (-1 : ℂ)) := by ring
    _ = (qScalar * (-1 : ℂ)) * (-1 : ℂ) := by ring
    _ = Complex.I * (-1 : ℂ) := by rw [hneg]
    _ = -Complex.I := by ring

/-- In the `p ≡ 3 [ZMOD 4]` branch, the quadratic Gauss sum is `I * √p`.
@isnad1 id=eq.2h1v.s6.1cad31a720c9 from=translated src=- shape=9cf40083 vocab=6b541780
-/
theorem gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
      Complex.I * (Real.sqrt p : ℂ) := by
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp_pos_real)
  have hscaled_neg :
      -((Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
        -Complex.I := by
    rw [← normalizedDft_quadraticScalar_eq_neg_scaledGaussSum_of_mod_four_eq_three
      (p := p) hp₂ hp₄]
    exact normalizedDft_quadraticScalar_eq_neg_I_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hscaled := congrArg (fun z : ℂ => (-1 : ℂ) * z) hscaled_neg
  have hscaled' :
      (Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        Complex.I := by
    simpa [mul_assoc] using hscaled
  have hmul := congrArg (fun z : ℂ => (Real.sqrt p : ℂ) * z) hscaled'
  simpa [hsqrt_ne, mul_assoc, mul_left_comm, mul_comm] using hmul

end SignInvariant

end KummerCriterion
