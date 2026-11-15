import Tengoku.FltAnthropic.Definitions.Def_IharaAmalgam
import Tengoku.FltAnthropic.Definitions.Def_Gamma0Away

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

variable (N q : ℕ)

def slToAway : SL(2, ℤ) →* SL(2, ZAway q) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℤ (ZAway q))

/--
@isnad1 id=eq.0h2v.s9.78340800a0dd from=translated src=- shape=192311c2 vocab=3b982b0a
-/
@[simp]
theorem coe_slToAway (g : SL(2, ℤ)) :
    ((slToAway q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      ((g : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl

/--
@isnad1 id=injectiv.1h1v.s7.94dca7f46b20 from=translated src=- shape=785810a3 vocab=b55ca00b
-/
theorem algebraMap_ZAway_injective {q : ℕ} (hq : q ≠ 0) :
    Function.Injective (algebraMap ℤ (ZAway q)) :=
  IsLocalization.injective (M := Submonoid.powers (q : ℤ)) (ZAway q)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.natCast_ne_zero.mpr hq))

/--
@isnad1 id=injectiv.1h1v.s9.f0af6543ab4b from=translated src=- shape=acac32ae vocab=cc8a359b
-/
theorem slToAway_injective {q : ℕ} (hq : q ≠ 0) : Function.Injective (slToAway q) := by
  intro g h hgh
  have hmat := congrArg (fun x : SL(2, ZAway q) => (x : Matrix (Fin 2) (Fin 2) (ZAway q))) hgh
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have hij := congrFun (congrFun hmat i) j
  simp only [coe_slToAway, map_apply] at hij
  exact algebraMap_ZAway_injective hq hij

def vertexZero : Gamma0 N →* SL(2, ZAway q) :=
  (slToAway q).comp (Gamma0 N).subtype

/--
@isnad1 id=eq.0h3v.s11.a9fe92755eb7 from=translated src=- shape=ec8a1a78 vocab=ad412ec0
-/
@[simp]
theorem coe_vertexZero (g : Gamma0 N) :
    ((vertexZero N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl

noncomputable def vertexOne : Gamma0 N →* SL(2, ZAway q) :=
  (wConj q).symm.toMonoidHom.comp (vertexZero N q)

/--
@isnad1 id=eq.0h3v.s12.8c6fe6a5a1b7 from=translated src=- shape=eeee8558 vocab=a262f33c
-/
theorem coe_vertexOne (g : Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      wMat q * (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) *
        wMatInv q :=
  rfl

/--
@isnad1 id=eq.0h2v.s9.886d378cca26 from=translated src=- shape=dfdd4d49 vocab=1692a597
-/
theorem wMat_mul_mul_wMatInv (M : Matrix (Fin 2) (Fin 2) (ZAway q)) :
    wMat q * M * wMatInv q =
      !![M 0 0, M 0 1 * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * M 1 0, M 1 1] := by
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add, mul_one]
  rw [mul_right_comm (q : ZAway q) (M 1 1), q_mul_invSelf, one_mul]

/--
@isnad1 id=eq.0h3v.s12.4465413380cf from=translated src=- shape=c81db4bf vocab=17dd2093
-/
theorem coe_vertexOne_eq (g : Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 1) *
           IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1)] := by
  rw [coe_vertexOne, wMat_mul_mul_wMatInv]
  rfl

/--
@isnad1 id=eq.0h1v.s8.7feb1ec1c582 from=translated src=- shape=47b8452f vocab=544fa349
-/
theorem map_wInt_eq_wMat :
    (!![(1 : ℤ), 0; 0, (q : ℤ)]).map (algebraMap ℤ (ZAway q)) = wMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

/--
@isnad1 id=eq.0h2v.s12.6f6aef0cee0b from=translated src=- shape=48ec12d0 vocab=b8c42883
-/
theorem vertex_compat : (vertexZero N q).comp (ι₀ N q) = (vertexOne N q).comp (ι₁ N q) := by
  ext γ : 1
  apply Subtype.ext
  show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) =
    wMat q * ((((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map
      (algebraMap ℤ (ZAway q)) * wMatInv q
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ (ZAway q)))
    (w_mul_iota1 N q γ)
  simp only [Matrix.map_mul, map_wInt_eq_wMat] at h
  rw [h, mul_assoc, wMat_mul_wMatInv, mul_one]

noncomputable def amalgamToAway : iharaAmalgam N q →* SL(2, ZAway q) :=
  iharaLift (vertexZero N q) (vertexOne N q) (vertex_compat N q)

/--
@isnad1 id=eq.0h3v.s12.68b3c3ea0900 from=translated src=- shape=15368cd4 vocab=78618dbe
-/
theorem amalgamToAway_vertex_zero (g : Gamma0 N) :
    amalgamToAway N q (iharaVertex N q 0 g) = vertexZero N q g :=
  iharaLift_vertex_zero _ _ _ g

/--
@isnad1 id=eq.0h3v.s12.a59dee9eb7bd from=translated src=- shape=15368cd4 vocab=21434064
-/
theorem amalgamToAway_vertex_one (g : Gamma0 N) :
    amalgamToAway N q (iharaVertex N q 1 g) = vertexOne N q g :=
  iharaLift_vertex_one _ _ _ g

/--
@isnad1 id=eq.0h3v.s12.6d5871a3bd5d from=translated src=- shape=b87d6ba7 vocab=93142634
-/
theorem amalgamToAway_base (γ : Gamma0 (N * q)) :
    amalgamToAway N q (iharaBase N q γ) = slToAway q γ :=
  iharaLift_base _ _ _ γ

/--
@isnad1 id=dvd.0h2v.s9.b65d1e427690 from=translated src=- shape=7e17b7dc vocab=cd3533ca
-/
theorem N_dvd_entry (g : Gamma0 N) : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := by
  have h := g.2
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N] at h
  exact h

/--
@isnad1 id=mem.0h3v.s11.b94548c29ccb from=translated src=- shape=6248cb09 vocab=9d329444
-/
theorem vertexZero_mem (g : Gamma0 N) : vertexZero N q g ∈ Gamma0Away N q := by
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨algebraMap ℤ (ZAway q) k, ?_⟩
  show algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) = _
  rw [hk, map_mul]
  simp

/--
@isnad1 id=eq.0h3v.s11.eea3d7d76acf from=translated src=- shape=d2c0268b vocab=1c67cd0e
-/
theorem vertexOne_apply_one_zero (g : Gamma0 N) :
    (vertexOne N q g : SL(2, ZAway q)) 1 0 =
      (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) := by
  rw [coe_vertexOne_eq]
  rfl

/--
@isnad1 id=mem.0h3v.s11.07a4ab3b2977 from=translated src=- shape=6248cb09 vocab=e2ef9cbe
-/
theorem vertexOne_mem (g : Gamma0 N) : vertexOne N q g ∈ Gamma0Away N q := by
  rw [mem_Gamma0Away, vertexOne_apply_one_zero]
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨(q : ZAway q) * algebraMap ℤ (ZAway q) k, ?_⟩
  rw [hk, map_mul, eq_intCast, Int.cast_natCast]
  ring

/--
@isnad1 id=le.0h2v.s8.e84ea25d27b9 from=translated src=- shape=66c6a86c vocab=cacfd5bb
-/
theorem range_amalgamToAway_le : (amalgamToAway N q).range ≤ Gamma0Away N q := by
  rw [MonoidHom.range_eq_map, ← iharaVertex_range_sup, Subgroup.map_sup, sup_le_iff,
    MonoidHom.map_range, MonoidHom.map_range]
  constructor
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, amalgamToAway_vertex_zero]
    exact vertexZero_mem N q g
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, amalgamToAway_vertex_one]
    exact vertexOne_mem N q g

/--
@isnad1 id=mem.0h3v.s9.61e840c85bdd from=translated src=- shape=1cbb87e9 vocab=3c0f8a84
-/
theorem amalgamToAway_mem (x : iharaAmalgam N q) : amalgamToAway N q x ∈ Gamma0Away N q :=
  range_amalgamToAway_le N q ⟨x, rfl⟩

noncomputable def amalgamToGamma0Away : iharaAmalgam N q →* Gamma0Away N q :=
  (amalgamToAway N q).codRestrict (Gamma0Away N q) (amalgamToAway_mem N q)

/--
@isnad1 id=eq.0h3v.s12.5ec7f54f8bca from=translated src=- shape=a2d3234c vocab=b8463946
-/
@[simp]
theorem coe_amalgamToGamma0Away (x : iharaAmalgam N q) :
    ((amalgamToGamma0Away N q x : Gamma0Away N q) : SL(2, ZAway q)) = amalgamToAway N q x :=
  rfl

/--
@isnad1 id=iff.0h2v.s12.d8243e79166b from=translated src=- shape=083da02a vocab=7aed7d3b
-/
theorem amalgamToGamma0Away_injective_iff :
    Function.Injective (amalgamToGamma0Away N q) ↔ Function.Injective (amalgamToAway N q) :=
  MonoidHom.injective_codRestrict _ _ _

end Ihara
