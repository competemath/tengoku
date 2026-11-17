import Tengoku.LeanEvalPlatonicClassification.Submission.Ortoplesse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Il 24-cell in `E 4`.

I vertici sono le radici del sistema `D₄`: esattamente due coordinate non nulle,
entrambe uguali a `±1`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

abbrev CoppiaVentiquattro := {p : Fin 4 × Fin 4 // p.1 < p.2}

/-- Codice di un vertice del 24-cell: due coordinate ordinate e due segni.-/
abbrev CodiceVentiquattro := CoppiaVentiquattro × (Bool × Bool)

abbrev indicePrimoVentiquattro (c : CodiceVentiquattro) : Fin 4 := c.1.1.1

abbrev indiceSecondoVentiquattro (c : CodiceVentiquattro) : Fin 4 := c.1.1.2

abbrev segnoPrimoVentiquattro (c : CodiceVentiquattro) : Bool := c.2.1

abbrev segnoSecondoVentiquattro (c : CodiceVentiquattro) : Bool := c.2.2

/--
@isnad1 id=lt.0h1v.s4.8c80c3c12bb6 from=translated src=- shape=39692a2b vocab=df369684
-/
theorem indicePrimo_lt_indiceSecondo (c : CodiceVentiquattro) :
    indicePrimoVentiquattro c < indiceSecondoVentiquattro c :=
  c.1.2

/--
@isnad1 id=ne.0h1v.s3.c3bd4a433312 from=translated src=- shape=39692a2b vocab=3faae265
-/
theorem indicePrimo_ne_indiceSecondo (c : CodiceVentiquattro) :
    indicePrimoVentiquattro c ≠ indiceSecondoVentiquattro c :=
  ne_of_lt (indicePrimo_lt_indiceSecondo c)

def segnoVentiquattro (b : Bool) : ℝ :=
  if b then 1 else -1

/--
@isnad1 id=ne.0h1v.s3.bfaa7f8f729d from=translated src=- shape=a311c14d vocab=2337f519
-/
@[simp] theorem segnoVentiquattro_ne_zero (b : Bool) :
    segnoVentiquattro b ≠ 0 := by
  cases b <;> norm_num [segnoVentiquattro]

/--
@isnad1 id=eq.0h1v.s3.a0e0d8dd720e from=translated src=- shape=562e4a6d vocab=26abe8a1
-/
@[simp] theorem norm_segnoVentiquattro (b : Bool) :
    ‖segnoVentiquattro b‖ = 1 := by
  cases b <;> norm_num [segnoVentiquattro]

/--
@isnad1 id=eq.0h1v.s4.9650f8920e0d from=translated src=- shape=7bab346c vocab=dacc8464
-/
@[simp] theorem mul_self_segnoVentiquattro (b : Bool) :
    segnoVentiquattro b * segnoVentiquattro b = 1 := by
  cases b <;> norm_num [segnoVentiquattro]

/--
@isnad1 id=injectiv.0h0v.s2.5fe2bff169de from=translated src=- shape=54c8eceb vocab=0c7d0b98
-/
theorem segnoVentiquattro_injective :
    Function.Injective segnoVentiquattro := by
  intro b c h
  cases b <;> cases c
  · rfl
  · norm_num [segnoVentiquattro] at h
  · norm_num [segnoVentiquattro] at h
  · rfl

/-- Costruttore comodo per i codici.-/
def codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) : CodiceVentiquattro :=
  (⟨(i, j), hij⟩, (si, sj))

/--
@isnad1 id=eq.1h4v.s5.cf547d1deb36 from=translated src=- shape=563fbf00 vocab=7b46434c
-/
@[simp] theorem indicePrimo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    indicePrimoVentiquattro (codiceVentiquattro i j hij si sj) = i := rfl

/--
@isnad1 id=eq.1h4v.s5.600b5e4b59d3 from=translated src=- shape=d17bfd95 vocab=2b579bf4
-/
@[simp] theorem indiceSecondo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    indiceSecondoVentiquattro (codiceVentiquattro i j hij si sj) = j := rfl

/--
@isnad1 id=eq.1h4v.s5.3f9b292ede6a from=translated src=- shape=80da84a0 vocab=35b84676
-/
@[simp] theorem segnoPrimo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    segnoPrimoVentiquattro (codiceVentiquattro i j hij si sj) = si := rfl

/--
@isnad1 id=eq.1h4v.s5.f4aceb299bcb from=translated src=- shape=982d69fd vocab=3bd7b459
-/
@[simp] theorem segnoSecondo_codiceVentiquattro (i j : Fin 4) (hij : i < j)
    (si sj : Bool) :
    segnoSecondoVentiquattro (codiceVentiquattro i j hij si sj) = sj := rfl

/-- Un vertice del 24-cell.-/
def vertVentiquattro (c : CodiceVentiquattro) : E 4 :=
  EuclideanSpace.single (indicePrimoVentiquattro c)
      (segnoVentiquattro (segnoPrimoVentiquattro c)) +
    EuclideanSpace.single (indiceSecondoVentiquattro c)
      (segnoVentiquattro (segnoSecondoVentiquattro c))

/--
@isnad1 id=eq.0h2v.s6.11a8eb4c9bf9 from=translated src=- shape=e5431e48 vocab=35db7519
-/
theorem vertVentiquattro_apply (c : CodiceVentiquattro) (k : Fin 4) :
    vertVentiquattro c k =
      (if k = indicePrimoVentiquattro c then
          segnoVentiquattro (segnoPrimoVentiquattro c) else 0) +
        (if k = indiceSecondoVentiquattro c then
          segnoVentiquattro (segnoSecondoVentiquattro c) else 0) := by
  simp [vertVentiquattro]

/--
@isnad1 id=eq.0h1v.s5.8acac39da679 from=translated src=- shape=8905823c vocab=5b09169f
-/
@[simp] theorem vertVentiquattro_apply_primo (c : CodiceVentiquattro) :
    vertVentiquattro c (indicePrimoVentiquattro c) =
      segnoVentiquattro (segnoPrimoVentiquattro c) := by
  simp [vertVentiquattro_apply, indicePrimo_ne_indiceSecondo c]

/--
@isnad1 id=eq.0h1v.s5.b9f520279298 from=translated src=- shape=8905823c vocab=fb9da9cf
-/
@[simp] theorem vertVentiquattro_apply_secondo (c : CodiceVentiquattro) :
    vertVentiquattro c (indiceSecondoVentiquattro c) =
      segnoVentiquattro (segnoSecondoVentiquattro c) := by
  simp [vertVentiquattro_apply, (indicePrimo_ne_indiceSecondo c).symm]

/--
@isnad1 id=iff.0h2v.s6.9a19032535e0 from=translated src=- shape=72ba0b8d vocab=ab67eb6d
-/
theorem vertVentiquattro_apply_ne_zero_iff (c : CodiceVentiquattro) (k : Fin 4) :
    vertVentiquattro c k ≠ 0 ↔
      k = indicePrimoVentiquattro c ∨ k = indiceSecondoVentiquattro c := by
  by_cases hk₁ : k = indicePrimoVentiquattro c
  · subst hk₁
    simp [indicePrimo_ne_indiceSecondo c]
  · by_cases hk₂ : k = indiceSecondoVentiquattro c
    · subst hk₂
      simp [hk₁]
    · simp [vertVentiquattro_apply, hk₁, hk₂]

/--
@isnad1 id=eq.4h2v.s5.23d45553ad4a from=translated src=- shape=c8cf2b38 vocab=b5aea14a
-/
theorem codiceVentiquattro_ext {c d : CodiceVentiquattro}
    (h₁ : indicePrimoVentiquattro c = indicePrimoVentiquattro d)
    (h₂ : indiceSecondoVentiquattro c = indiceSecondoVentiquattro d)
    (hs₁ : segnoPrimoVentiquattro c = segnoPrimoVentiquattro d)
    (hs₂ : segnoSecondoVentiquattro c = segnoSecondoVentiquattro d) :
    c = d := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  rcases d with ⟨⟨⟨i', j'⟩, hij'⟩, ⟨si', sj'⟩⟩
  simp [indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro] at h₁ h₂ hs₁ hs₂
  subst i'
  subst j'
  subst si'
  subst sj'
  rfl

/--
@isnad1 id=and.1h2v.s5.9dd77e06acdd from=translated src=- shape=2555a48b vocab=0bb6e231
-/
theorem vertVentiquattro_pair_eq_of_eq {c d : CodiceVentiquattro}
    (h : vertVentiquattro c = vertVentiquattro d) :
    indicePrimoVentiquattro c = indicePrimoVentiquattro d ∧
      indiceSecondoVentiquattro c = indiceSecondoVentiquattro d := by
  have hci : vertVentiquattro c (indicePrimoVentiquattro c) ≠ 0 := by
    simp
  have hcj : vertVentiquattro c (indiceSecondoVentiquattro c) ≠ 0 := by
    simp
  have hiMem :
      indicePrimoVentiquattro c = indicePrimoVentiquattro d ∨
        indicePrimoVentiquattro c = indiceSecondoVentiquattro d := by
    exact (vertVentiquattro_apply_ne_zero_iff d
      (indicePrimoVentiquattro c)).mp (by simpa [h] using hci)
  have hjMem :
      indiceSecondoVentiquattro c = indicePrimoVentiquattro d ∨
        indiceSecondoVentiquattro c = indiceSecondoVentiquattro d := by
    exact (vertVentiquattro_apply_ne_zero_iff d
      (indiceSecondoVentiquattro c)).mp (by simpa [h] using hcj)
  rcases hiMem with hi | hi
  · rcases hjMem with hj | hj
    · exfalso
      exact indicePrimo_ne_indiceSecondo c (hi.trans hj.symm)
    · exact ⟨hi, hj⟩
  · rcases hjMem with hj | hj
    · exfalso
      have hlt : indiceSecondoVentiquattro c < indicePrimoVentiquattro c := by
        calc
          indiceSecondoVentiquattro c = indicePrimoVentiquattro d := hj
          _ < indiceSecondoVentiquattro d := indicePrimo_lt_indiceSecondo d
          _ = indicePrimoVentiquattro c := hi.symm
      exact (not_lt_of_ge (indicePrimo_lt_indiceSecondo c).le) hlt
    · exfalso
      exact indicePrimo_ne_indiceSecondo c (hi.trans hj.symm)

/--
@isnad1 id=injectiv.0h0v.s3.77e040d3ddf9 from=translated src=- shape=d3a93718 vocab=f15dc1c0
-/
theorem vertVentiquattro_injective :
    Function.Injective vertVentiquattro := by
  intro c d h
  obtain ⟨h₁, h₂⟩ := vertVentiquattro_pair_eq_of_eq h
  have hs₁ :
      segnoPrimoVentiquattro c = segnoPrimoVentiquattro d := by
    apply segnoVentiquattro_injective
    have hc := congrArg (fun x : E 4 => x (indicePrimoVentiquattro c)) h
    simpa [h₁] using hc
  have hs₂ :
      segnoSecondoVentiquattro c = segnoSecondoVentiquattro d := by
    apply segnoVentiquattro_injective
    have hc := congrArg (fun x : E 4 => x (indiceSecondoVentiquattro c)) h
    simpa [h₂] using hc
  exact codiceVentiquattro_ext h₁ h₂ hs₁ hs₂

/-- I 24 vertici del 24-cell.-/
def verticiVentiquattro : Finset (E 4) :=
  (Finset.univ : Finset CodiceVentiquattro).image vertVentiquattro

/--
@isnad1 id=iff.0h1v.s5.d81a5f9d4131 from=translated src=- shape=897fd71a vocab=cd06afa9
-/
theorem mem_verticiVentiquattro {x : E 4} :
    x ∈ verticiVentiquattro ↔ ∃ c : CodiceVentiquattro, vertVentiquattro c = x := by
  simp [verticiVentiquattro]

/--
@isnad1 id=eq.0h0v.s7.6523dceebcaa from=translated src=- shape=b0ae1d2b vocab=850c2423
-/
theorem card_coppiaVentiquattro : Fintype.card CoppiaVentiquattro = 6 := by
  rw [Fintype.card_subtype]
  have h :
      (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)) =
        {((0 : Fin 4), (1 : Fin 4)), ((0 : Fin 4), (2 : Fin 4)),
          ((0 : Fin 4), (3 : Fin 4)), ((1 : Fin 4), (2 : Fin 4)),
          ((1 : Fin 4), (3 : Fin 4)), ((2 : Fin 4), (3 : Fin 4))} := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp

/--
@isnad1 id=eq.0h0v.s7.15128e74e259 from=translated src=- shape=b0ae1d2b vocab=32582dbe
-/
theorem card_codiceVentiquattro : Fintype.card CodiceVentiquattro = 24 := by
  rw [Fintype.card_prod, Fintype.card_prod, card_coppiaVentiquattro]
  norm_num

/--
@isnad1 id=eq.0h0v.s3.0ce194300e5f from=translated src=- shape=415057c6 vocab=3c8b4f7f
-/
theorem card_ventiquattro : verticiVentiquattro.card = 24 := by
  rw [verticiVentiquattro,
    Finset.card_image_of_injective _ vertVentiquattro_injective]
  exact card_codiceVentiquattro

/--
@isnad1 id=nonempty.0h0v.s3.315033c27395 from=translated src=- shape=06f63001 vocab=f8877e24
-/
theorem verticiVentiquattro_nonempty : verticiVentiquattro.Nonempty := by
  refine ⟨vertVentiquattro
    (codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true), ?_⟩
  exact mem_verticiVentiquattro.mpr
    ⟨codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true, rfl⟩

/--
@isnad1 id=eq.0h1v.s6.51dc8689ccdc from=translated src=- shape=7b9ddabb vocab=45da75bd
-/
theorem norm_sq_vertVentiquattro (c : CodiceVentiquattro) :
    ‖vertVentiquattro c‖ ^ 2 = 2 := by
  let i := indicePrimoVentiquattro c
  let j := indiceSecondoVentiquattro c
  let si := segnoVentiquattro (segnoPrimoVentiquattro c)
  let sj := segnoVentiquattro (segnoSecondoVentiquattro c)
  have horth : inner ℝ (EuclideanSpace.single i si)
      (EuclideanSpace.single j sj) = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [i, j, indicePrimo_ne_indiceSecondo c]
  change ‖EuclideanSpace.single i si + EuclideanSpace.single j sj‖ ^ 2 = 2
  rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real horth]
  simp [si, sj, PiLp.norm_single]
  norm_num

/--
@isnad1 id=eq.1h3v.s7.c79e29e2d047 from=translated src=- shape=7af2d40a vocab=84390e8a
-/
theorem vertVentiquattro_sub_flip_primo (i j : Fin 4) (hij : i < j)
    (sj : Bool) :
    vertVentiquattro (codiceVentiquattro i j hij true sj) -
        vertVentiquattro (codiceVentiquattro i j hij false sj) =
      (2 : ℝ) • EuclideanSpace.single i 1 := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [vertVentiquattro, hij.ne,
      segnoVentiquattro]
    ring_nf
  · simp [vertVentiquattro, hki,
      segnoVentiquattro]
    ring_nf
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)

/--
@isnad1 id=eq.1h3v.s7.22fad51157ac from=translated src=- shape=84f89a88 vocab=84390e8a
-/
theorem vertVentiquattro_sub_flip_secondo (i j : Fin 4) (hij : i < j)
    (si : Bool) :
    vertVentiquattro (codiceVentiquattro i j hij si true) -
        vertVentiquattro (codiceVentiquattro i j hij si false) =
      (2 : ℝ) • EuclideanSpace.single j 1 := by
  ext k
  by_cases hkj : k = j
  · subst k
    simp [vertVentiquattro, (ne_of_lt hij).symm,
      segnoVentiquattro]
    ring_nf
  · simp [vertVentiquattro, hkj,
      segnoVentiquattro]
    ring_nf
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)

/--
@isnad1 id=eq.0h1v.s5.d7b3bc89f689 from=translated src=- shape=188b318a vocab=a13885d7
-/
theorem norm_vertVentiquattro (c : CodiceVentiquattro) :
    ‖vertVentiquattro c‖ = Real.sqrt 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    norm_sq_vertVentiquattro c, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/--
@isnad1 id=eq.0h0v.s8.36a0c4d4c5f8 from=translated src=- shape=c466b020 vocab=0eef63b0
-/
theorem verticiVentiquattro_eq_extremePoints :
    ((verticiVentiquattro : Finset (E 4)) : Set (E 4)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiVentiquattro : Finset (E 4)) : Set (E 4))) := by
  let c₀ : CodiceVentiquattro :=
    codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true
  have hne : (0 : E 4) ≠ vertVentiquattro c₀ := by
    intro h
    have h0 := congrArg (fun x : E 4 => x (0 : Fin 4)) h
    norm_num [c₀, codiceVentiquattro, vertVentiquattro,
      indicePrimoVentiquattro, indiceSecondoVentiquattro,
      segnoPrimoVentiquattro, segnoSecondoVentiquattro,
      segnoVentiquattro, PiLp.single_apply] at h0
  haveI : Nontrivial (E 4) := ⟨⟨0, vertVentiquattro c₀, hne⟩⟩
  symm
  apply cosferico_extremePoints 0 (Real.sqrt 2)
  intro v hv
  rw [mem_sphere_zero_iff_norm]
  have hv' : v ∈ verticiVentiquattro := by exact_mod_cast hv
  rw [mem_verticiVentiquattro] at hv'
  obtain ⟨c, rfl⟩ := hv'
  exact norm_vertVentiquattro c

/-- Il 24-cell `{3,4,3}` come politopo convesso in `E 4`.-/
def ventiquattro : ConvexPolytope 4 :=
  ⟨verticiVentiquattro, verticiVentiquattro_nonempty,
    verticiVentiquattro_eq_extremePoints⟩

/--
@isnad1 id=eq.0h0v.s4.4e0d31dd7893 from=translated src=- shape=1538b06e vocab=0964c848
-/
theorem card_politope_ventiquattro :
    ventiquattro.vertices.card = 24 :=
  card_ventiquattro

/-- Il 24-cell genera affineamente tutto `E 4`.
@isnad1 id=isfulldi.0h0v.s2.c33c1b5173a9 from=translated src=- shape=cef8a6bf vocab=fca13ba5
-/
theorem ventiquattro_isFullDim : ventiquattro.IsFullDim := by
  let W : Submodule ℝ (E 4) := vectorSpan ℝ ventiquattro.toSet
  have mem_toSet (c : CodiceVentiquattro) :
      vertVentiquattro c ∈ ventiquattro.toSet := by
    exact subset_convexHull ℝ _
      (by exact_mod_cast (mem_verticiVentiquattro.mpr ⟨c, rfl⟩))
  have basis0 : (EuclideanSpace.basisFun (Fin 4) ℝ) (0 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true
    let cm := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) false true
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (0 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_primo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have basis1 : (EuclideanSpace.basisFun (Fin 4) ℝ) (1 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true true
    let cm := codiceVentiquattro (0 : Fin 4) (1 : Fin 4) (by norm_num) true false
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (1 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_secondo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have basis2 : (EuclideanSpace.basisFun (Fin 4) ℝ) (2 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) true true
    let cm := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) false true
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (2 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_primo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have basis3 : (EuclideanSpace.basisFun (Fin 4) ℝ) (3 : Fin 4) ∈ W := by
    let cp := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) true true
    let cm := codiceVentiquattro (2 : Fin 4) (3 : Fin 4) (by omega) true false
    have hdiff : vertVentiquattro cp - vertVentiquattro cm ∈ W :=
      vsub_mem_vectorSpan ℝ (mem_toSet cp) (mem_toSet cm)
    have hcalc :
        vertVentiquattro cp - vertVentiquattro cm =
          (2 : ℝ) • EuclideanSpace.single (3 : Fin 4) 1 := by
      exact vertVentiquattro_sub_flip_secondo _ _ _ true
    rw [EuclideanSpace.basisFun_apply]
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
  have hbasis : ∀ i : Fin 4,
      (EuclideanSpace.basisFun (Fin 4) ℝ) i ∈ W := by
    intro i
    fin_cases i
    · exact basis0
    · exact basis1
    · exact basis2
    · exact basis3
  have hW : W = ⊤ := by
    apply (Submodule.eq_top_iff').2
    intro x
    rw [← (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = 4
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

def segnoBoolDaReale (s : ({-1, 1} : Set ℝ)) (b : Bool) : Bool :=
  if (s : ℝ) = 1 then b else !b

/--
@isnad1 id=eq.0h2v.s6.d924417d8b3f from=translated src=- shape=4d606ca1 vocab=23594683
-/
theorem segnoBoolDaReale_spec (s : ({-1, 1} : Set ℝ)) (b : Bool) :
    segnoVentiquattro (segnoBoolDaReale s b) =
      (s : ℝ) * segnoVentiquattro b := by
  unfold segnoBoolDaReale
  split_ifs with h
  · rw [h]
    simp
  · have hs : (s : ℝ) = -1 := by
      have hm := s.property
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact hm
      · exact (h hm).elim
    rw [hs]
    cases b <;> norm_num [segnoVentiquattro]

/--
@isnad1 id=eq.0h2v.s9.76d0536b05d8 from=translated src=- shape=3468f6f8 vocab=70af8d6f
-/
theorem segnoPerm_refl_vertVentiquattro
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) (c : CodiceVentiquattro) :
    segnoPerm 4 (Equiv.refl (Fin 4)) ε (vertVentiquattro c) =
      vertVentiquattro
        (codiceVentiquattro (indicePrimoVentiquattro c)
          (indiceSecondoVentiquattro c) (indicePrimo_lt_indiceSecondo c)
          (segnoBoolDaReale (ε (indicePrimoVentiquattro c))
            (segnoPrimoVentiquattro c))
          (segnoBoolDaReale (ε (indiceSecondoVentiquattro c))
            (segnoSecondoVentiquattro c))) := by
  rw [segnoPerm_apply]
  simp only [vertVentiquattro, map_add, segnoLinear_single,
    Equiv.refl_apply, indicePrimo_codiceVentiquattro,
    indiceSecondo_codiceVentiquattro, segnoPrimo_codiceVentiquattro,
    segnoSecondo_codiceVentiquattro, segnoBoolDaReale_spec]

/--
@isnad1 id=mem.1h2v.s9.8aa9362573ed from=translated src=- shape=4c5e1521 vocab=81510e54
-/
theorem segnoPerm_refl_mem_verticiVentiquattro
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) {v : E 4}
    (hv : v ∈ verticiVentiquattro) :
    segnoPerm 4 (Equiv.refl (Fin 4)) ε v ∈ verticiVentiquattro := by
  rw [mem_verticiVentiquattro] at hv
  obtain ⟨c, rfl⟩ := hv
  refine mem_verticiVentiquattro.mpr ?_
  refine ⟨codiceVentiquattro (indicePrimoVentiquattro c)
      (indiceSecondoVentiquattro c) (indicePrimo_lt_indiceSecondo c)
      (segnoBoolDaReale (ε (indicePrimoVentiquattro c))
        (segnoPrimoVentiquattro c))
      (segnoBoolDaReale (ε (indiceSecondoVentiquattro c))
        (segnoSecondoVentiquattro c)), ?_⟩
  exact (segnoPerm_refl_vertVentiquattro ε c).symm

/--
@isnad1 id=eq.0h1v.s9.d5ff5347bbf9 from=translated src=- shape=c980a7a8 vocab=0eed2ba9
-/
theorem segnoPerm_refl_image_verticiVentiquattro
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    (segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4) ''
        (verticiVentiquattro : Set (E 4)) =
      (verticiVentiquattro : Set (E 4)) := by
  have hfin :
      Finset.image (segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4)
          verticiVentiquattro =
        verticiVentiquattro := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_refl_mem_verticiVentiquattro ε hu
    · rw [Finset.card_image_of_injective _
        (segnoPerm 4 (Equiv.refl (Fin 4)) ε).injective]
  rw [← Finset.coe_image, hfin]

/-- Simmetrie parziali: cambi indipendenti di segno delle coordinate.
@isnad1 id=issymmet.0h1v.s5.39e487627aab from=translated src=- shape=b80341b3 vocab=927fe150
-/
theorem segnoPerm_refl_isSymmetry
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    ventiquattro.isSymmetry (segnoPerm 4 (Equiv.refl (Fin 4)) ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4) ''
        convexHull ℝ ((ventiquattro.vertices : Finset (E 4)) : Set (E 4)) =
      convexHull ℝ ((segnoPerm 4 (Equiv.refl (Fin 4)) ε : E 4 → E 4) ''
        ((ventiquattro.vertices : Finset (E 4)) : Set (E 4))) := by
          exact (segnoPerm 4 (Equiv.refl (Fin 4)) ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ventiquattro.vertices : Finset (E 4)) : Set (E 4)) := by
      rw [show ((ventiquattro.vertices : Finset (E 4)) : Set (E 4)) =
          (verticiVentiquattro : Set (E 4)) by rfl,
        segnoPerm_refl_image_verticiVentiquattro]

/-!
Resta aperta la dimostrazione completa di `ventiquattro.IsRegular`: qui sono
costruiti il politopo, la cardinalità, la piena dimensionalità e un sottogruppo
esplicito di simmetrie. La transitività su tutte le bandiere richiede una
descrizione kernel-pura della struttura facciale del 24-cell.
-/

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
