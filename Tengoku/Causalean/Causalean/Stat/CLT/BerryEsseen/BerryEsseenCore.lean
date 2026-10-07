module
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenGaussian
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenLocalProduct
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenMomentLowerBound
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenSmoothing
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenStandardize
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenTaylor
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenUnit
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.IIDCharFunProduct
public import Tengoku

/-! # Quantitative scalar normal approximation for an iid real law

This module isolates the probability-theoretic Berry–Esseen step from the
cross-fitting model. The law is on the real line and the sample has its finite
product distribution. The third absolute moment is explicitly integrable;
its numerical upper bound alone would not imply integrability in Lean.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

end Causalean.Stat.CLT.BerryEsseen
