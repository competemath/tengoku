/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 14).
@isnad1 id=eq.0h0v.s5.766fcce838e1 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_14 :
    branchClaimRootValidB 1 14 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 31).
@isnad1 id=eq.0h0v.s5.aa61f1f356ba from=translated src=- shape=e9e0773c vocab=7093c046
-/
theorem coverageBranchRoot_3_31 :
    branchClaimRootValidB 3 31 (.search branchClaims3Row31) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 30), starting at 64.
@isnad1 id=eq.0h0v.s3.fea59b654d43 from=translated src=- shape=6f582f20 vocab=eeb4028c
-/
theorem coverageBranchNodes_3_30_00064 :
    nodeClaimChunkValidB branchClaims3Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 30), starting at 128.
@isnad1 id=eq.0h0v.s3.52dbfc28e4da from=translated src=- shape=6f582f20 vocab=eeb4028c
-/
theorem coverageBranchNodes_3_30_00128 :
    nodeClaimChunkValidB branchClaims3Row30 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 30), starting at 192.
@isnad1 id=eq.0h0v.s3.b4cb53a2ec63 from=translated src=- shape=6f582f20 vocab=eeb4028c
-/
theorem coverageBranchNodes_3_30_00192 :
    nodeClaimChunkValidB branchClaims3Row30 192 31 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 31), starting at 0.
@isnad1 id=eq.0h0v.s3.ab1b529456fc from=translated src=- shape=6f582f20 vocab=a8971433
-/
theorem coverageBranchNodes_3_31_00000 :
    nodeClaimChunkValidB branchClaims3Row31 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
