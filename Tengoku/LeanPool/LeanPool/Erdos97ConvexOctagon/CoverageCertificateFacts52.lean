/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 7).
@isnad1 id=eq.0h0v.s5.708db658a53b from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_07 :
    branchClaimRootValidB 2 7 (.patternThree 2) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 64.
@isnad1 id=eq.0h0v.s3.5aea18a79336 from=translated src=- shape=6f582f20 vocab=89a7448e
-/
theorem coverageBranchNodes_5_14_00064 :
    nodeClaimChunkValidB branchClaims5Row14 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 128.
@isnad1 id=eq.0h0v.s3.56e585bce6b5 from=translated src=- shape=6f582f20 vocab=89a7448e
-/
theorem coverageBranchNodes_5_14_00128 :
    nodeClaimChunkValidB branchClaims5Row14 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 192.
@isnad1 id=eq.0h0v.s3.ce50ff9db324 from=translated src=- shape=6f582f20 vocab=89a7448e
-/
theorem coverageBranchNodes_5_14_00192 :
    nodeClaimChunkValidB branchClaims5Row14 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 256.
@isnad1 id=eq.0h0v.s3.cfd85c5850b4 from=translated src=- shape=6f582f20 vocab=89a7448e
-/
theorem coverageBranchNodes_5_14_00256 :
    nodeClaimChunkValidB branchClaims5Row14 256 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
