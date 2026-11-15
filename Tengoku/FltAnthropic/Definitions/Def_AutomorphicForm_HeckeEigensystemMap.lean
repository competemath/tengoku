import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_HeckeEigensystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]

def map (ι : R →+* S) (Φ : HeckeEigensystem F R) : HeckeEigensystem F S where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => ι (Φ.a v)
  b := fun v => ι (Φ.b v)

/--
@isnad1 id=eq.0h5v.s6.b4fe82f88e43 from=translated src=- shape=8210925b vocab=6ddaf4b1
-/
@[simp] theorem map_level (ι : R →+* S) (Φ : HeckeEigensystem F R) :
    (Φ.map ι).level = Φ.level := rfl

/--
@isnad1 id=eq.0h6v.s6.561afef4eeb0 from=translated src=- shape=ab70cf6b vocab=a57c786a
-/
@[simp] theorem map_a (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).a v = ι (Φ.a v) := rfl

/--
@isnad1 id=eq.0h6v.s6.d14dbd82a979 from=translated src=- shape=ab70cf6b vocab=02a3d9d8
-/
@[simp] theorem map_b (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).b v = ι (Φ.b v) := rfl

/--
@isnad1 id=eq.0h3v.s5.85d6c7b75dd3 from=translated src=- shape=ffad0d57 vocab=047091d5
-/
theorem map_id (Φ : HeckeEigensystem F R) : Φ.map (RingHom.id R) = Φ := rfl

/--
@isnad1 id=eq.0h7v.s7.7a8491970301 from=translated src=- shape=36c6ac85 vocab=330adc01
-/
theorem map_map {T : Type*} [CommRing T] (ι : R →+* S) (κ : S →+* T)
    (Φ : HeckeEigensystem F R) : (Φ.map ι).map κ = Φ.map (κ.comp ι) := rfl

/--
@isnad1 id=eq.0h6v.s7.aed9266d8109 from=translated src=- shape=f5dbc1aa vocab=830f720a
-/
theorem map_twist (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (Φ.twist χ).map ι = (Φ.map ι).twist fun v => ι (χ v) := by
  simp only [map, twist]
  congr 1 <;> funext v
  · exact map_mul ι (χ v) (Φ.a v)
  · rw [map_mul, map_pow]

/--
@isnad1 id=agreesaw.1h6v.s6.3044e786973b from=translated src=- shape=365f9bd3 vocab=0beb19f7
-/
theorem AgreesAwayFromFinite.map {Φ Φ' : HeckeEigensystem F R}
    (h : AgreesAwayFromFinite Φ Φ') (ι : R →+* S) :
    AgreesAwayFromFinite (Φ.map ι) (Φ'.map ι) := by
  obtain ⟨S₀, hS₀⟩ := h
  exact ⟨S₀, fun v hv => ⟨congrArg ι (hS₀ v hv).1, congrArg ι (hS₀ v hv).2⟩⟩

end HeckeEigensystem

end AutomorphicForm
