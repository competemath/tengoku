/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 13).
@isnad1 id=eq.0h0v.s5.b6f5e2796bfe from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_13 :
    branchClaimRootValidB 1 13 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 30).
@isnad1 id=eq.0h0v.s5.878e3c2b6294 from=translated src=- shape=e9e0773c vocab=b66057d2
-/
theorem coverageBranchRoot_3_30 :
    branchClaimRootValidB 3 30 (.search branchClaims3Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 192.
@isnad1 id=eq.0h0v.s3.0fa9267eb310 from=translated src=- shape=6f582f20 vocab=6a248f59
-/
theorem coverageBranchNodes_3_28_00192 :
    nodeClaimChunkValidB branchClaims3Row28 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 256.
@isnad1 id=eq.0h0v.s3.f741d408cc9b from=translated src=- shape=6f582f20 vocab=6a248f59
-/
theorem coverageBranchNodes_3_28_00256 :
    nodeClaimChunkValidB branchClaims3Row28 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 320.
@isnad1 id=eq.0h0v.s3.7511bfc42a4d from=translated src=- shape=6f582f20 vocab=6a248f59
-/
theorem coverageBranchNodes_3_28_00320 :
    nodeClaimChunkValidB branchClaims3Row28 320 21 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 30), starting at 0.
@isnad1 id=eq.0h0v.s3.d46c5be67438 from=translated src=- shape=6f582f20 vocab=eeb4028c
-/
theorem coverageBranchNodes_3_30_00000 :
    nodeClaimChunkValidB branchClaims3Row30 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
