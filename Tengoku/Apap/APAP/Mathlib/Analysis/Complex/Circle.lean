module

public import Tengoku

public section

open Real

namespace Circle

/--
@isnad1 id=eq.1h2v.s5.e662d047e859 from=translated src=- shape=42017082 vocab=93295bca
-/
lemma cos_eq_cos_of_exp_eq_exp {x y : ℝ} (h : exp x = exp y) : cos x = cos y := by
  simpa using congr(($h : ℂ).re)

/--
@isnad1 id=eq.1h2v.s5.8df654a3ebb7 from=translated src=- shape=42017082 vocab=1748eabb
-/
lemma sin_eq_sin_of_exp_eq_exp {x y : ℝ} (h : exp x = exp y) : sin x = sin y := by
  simpa using congr(($h : ℂ).im)

end Circle
