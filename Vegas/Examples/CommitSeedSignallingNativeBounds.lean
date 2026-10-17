/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingAsyncService
import Vegas.Examples.CommitSeedSignallingHalfSuccess
import Vegas.Examples.CommitSeedSignallingBobJoint
import Vegas.Examples.CommitSeedSignallingAcceptanceBoundary
import Vegas.Examples.CommitSeedSignallingAlicePrePoll
import Vegas.Examples.CommitSeedSignallingBobIncentives
import Vegas.Examples.CommitSeedSignallingCountedContinuation
import Vegas.Examples.CommitSeedSignallingUnopenedContinuation
import Vegas.Examples.CommitSeedSignallingCountedSeedTrace
import Vegas.Examples.CommitSeedSignallingTailRecall
import Vegas.Examples.CommitSeedSignallingInitializedPayoff
import Vegas.Examples.CommitSeedSignallingInitializedHalf
import Vegas.Examples.CommitSeedSignallingAliceInitializedHalf
import Vegas.Examples.CommitSeedSignallingOwnContinuation
import Vegas.Examples.CommitSeedSignallingBobQuietInitialization

/-! # Native service and conditional timing bounds for private-seed signalling

These results establish the actual raw asynchronous contract, initialized
late-acceptance bounds and exact physical continuation laws. They do not assert
private calendar or success laws, or exclude every preserving equilibrium.
-/
