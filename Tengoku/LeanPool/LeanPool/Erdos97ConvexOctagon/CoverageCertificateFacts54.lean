/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 16).
@isnad1 id=eq.0h0v.s5.387c1c378b65 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_16 :
    branchClaimRootValidB 2 16 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 16).
@isnad1 id=eq.0h0v.s5.7fe2743595ee from=translated src=- shape=e9e0773c vocab=c8f1ba19
-/
theorem coverageBranchRoot_5_16 :
    branchClaimRootValidB 5 16 (.search branchClaims5Row16) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 192.
@isnad1 id=eq.0h0v.s3.ef82119ae655 from=translated src=- shape=6f582f20 vocab=15da5cca
-/
theorem coverageBranchNodes_5_15_00192 :
    nodeClaimChunkValidB branchClaims5Row15 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 256.
@isnad1 id=eq.0h0v.s3.76b7e5614a16 from=translated src=- shape=6f582f20 vocab=15da5cca
-/
theorem coverageBranchNodes_5_15_00256 :
    nodeClaimChunkValidB branchClaims5Row15 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 320.
@isnad1 id=eq.0h0v.s3.d9982579236c from=translated src=- shape=6f582f20 vocab=15da5cca
-/
theorem coverageBranchNodes_5_15_00320 :
    nodeClaimChunkValidB branchClaims5Row15 320 45 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 16), starting at 0.
@isnad1 id=eq.0h0v.s3.61222609971f from=translated src=- shape=6f582f20 vocab=5df7a720
-/
theorem coverageBranchNodes_5_16_00000 :
    nodeClaimChunkValidB branchClaims5Row16 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
