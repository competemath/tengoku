/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 19).
@isnad1 id=eq.0h0v.s5.2a0dc717466f from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_19 :
    branchClaimRootValidB 2 19 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 17).
@isnad1 id=eq.0h0v.s5.8217b618c2cf from=translated src=- shape=e9e0773c vocab=56fc287e
-/
theorem coverageBranchRoot_5_17 :
    branchClaimRootValidB 5 17 (.search branchClaims5Row17) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 16), starting at 64.
@isnad1 id=eq.0h0v.s3.4189b5dfc67a from=translated src=- shape=6f582f20 vocab=5df7a720
-/
theorem coverageBranchNodes_5_16_00064 :
    nodeClaimChunkValidB branchClaims5Row16 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 16), starting at 128.
@isnad1 id=eq.0h0v.s3.55084f429d98 from=translated src=- shape=6f582f20 vocab=5df7a720
-/
theorem coverageBranchNodes_5_16_00128 :
    nodeClaimChunkValidB branchClaims5Row16 128 42 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 17), starting at 0.
@isnad1 id=eq.0h0v.s3.a25ff6156fa7 from=translated src=- shape=6f582f20 vocab=e3b1c049
-/
theorem coverageBranchNodes_5_17_00000 :
    nodeClaimChunkValidB branchClaims5Row17 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 17), starting at 64.
@isnad1 id=eq.0h0v.s3.3076081e8772 from=translated src=- shape=6f582f20 vocab=e3b1c049
-/
theorem coverageBranchNodes_5_17_00064 :
    nodeClaimChunkValidB branchClaims5Row17 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
