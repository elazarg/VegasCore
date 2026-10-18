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
import Vegas.Examples.CommitSeedSignallingPrivateCalendar
import Vegas.Examples.CommitSeedSignallingCorrectSeedProbability
import Vegas.Examples.CommitSeedSignallingJointAcceptance
import Vegas.Examples.CommitSeedSignallingOriginalReceipts
import Vegas.Examples.CommitSeedSignallingRetryCheckpoint
import Vegas.Examples.CommitSeedSignallingPublicationChoice
import Vegas.Examples.CommitSeedSignallingPrivateBindingSuccess
import Vegas.Examples.CommitSeedSignallingUnilateralDelivery
import Vegas.Examples.CommitSeedSignallingReceiptPayoff
import Vegas.Examples.CommitSeedSignallingProperBindingRecords
import Vegas.Examples.CommitSeedSignallingHelperInitialRecall
import Vegas.Examples.CommitSeedSignallingBobEarlyAcceptance
import Vegas.Examples.CommitSeedSignallingPublicationResponse
import Vegas.Examples.CommitSeedSignallingInitialDeviation
import Vegas.Examples.CommitSeedSignallingHelperBindingValue
import Vegas.Examples.CommitSeedSignallingHelperCountedTrace
import Vegas.Examples.CommitSeedSignallingHelperPendingAcceptance
import Vegas.Examples.CommitSeedSignallingNonpreservation
import Interaction.ReactiveInvariantPrefix

/-! # Native service and equilibrium obstruction for private-seed signalling

These results establish the actual raw asynchronous contract, private clock
calendar and binding-success quotient, helper knowledge on full raw information
fibers, unilateral delivery bounds, and binding and opening incentives.
The fixed proper late deviation survives recovery whenever its original
binding lands, and its initialized expected payoff is at least one quarter
against an opponent who initially waits. The same whole-deviation bound holds
at Bob's actual quiet information set, including off-path assessments.
Every native sequential equilibrium gives Alice expected payoff at least one
quarter, whereas every honest source profile gives her zero. Consequently no
native sequential equilibrium preserves the required joint law. The fixture
has reward three and exclusion loss one; it does not satisfy a forfeit bound
strictly above the entire payoff range.
-/
