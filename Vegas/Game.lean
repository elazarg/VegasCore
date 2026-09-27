/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PurificationEdge
import Vegas.Game.ValueBindingEdge
import Vegas.Game.EventScheduling
import Vegas.Game.EventCompilation
import Vegas.Game.EventServiceEdge
import Vegas.Game.EventMessages
import Vegas.Game.ReactiveCompilation
import Vegas.Game.RevealService
import Vegas.Game.RevealServiceActions
import Vegas.Game.RevealServiceBounds
import Vegas.Game.RevealServiceClock
import Vegas.Game.RevealServiceCompletion
import Vegas.Game.RevealServiceBlock
import Vegas.Game.RevealServiceCalendarState
import Vegas.Game.RevealServiceCheckpoint
import Vegas.Game.RevealServiceCollection
import Vegas.Game.RevealServiceExecution
import Vegas.Game.RevealServiceLaw
import Vegas.Game.RevealServicePrefix
import Vegas.Game.RevealServicePrefixLaw
import Vegas.Game.RevealServicePrefixSupport
import Vegas.Game.RevealServicePrefixInformation
import Vegas.Game.RevealServicePrefixHistory
import Vegas.Game.RevealServicePrefixBehavioral
import Vegas.Game.RevealServicePrefixContinuation
import Vegas.Game.RevealServiceOwnerPrefix
import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServiceOwnerInformation
import Vegas.Game.RevealServiceOwnerSource
import Vegas.Game.RevealServicePrefixChoice
import Vegas.Game.RevealServiceMixing
import Vegas.Game.RevealServiceBayes
import Vegas.Game.RevealServiceConsistency
import Vegas.Game.RevealServiceOwnerContinuation
import Vegas.Game.RevealServicePrefixResponse
import Vegas.Game.RevealServiceOwnerResponse
import Vegas.Game.RevealServiceOwnerLocalLaw
import Vegas.Game.RevealServiceOwnerValue
import Vegas.Game.RevealServiceOwnerIncentives
import Vegas.Game.RevealServiceEquilibrium
import Vegas.Game.RevealServicePrefixEnforcement
import Vegas.Game.RevealServiceOwnerCollection
import Vegas.Game.RevealServiceClean
import Vegas.Game.RevealServiceOrdinaryExtension
import Vegas.Game.RevealServiceDeposits
import Vegas.Game.RevealServiceCompilation
import Vegas.Game.RevealServiceWatcherSupport
import Vegas.Game.RevealServiceReplayMenu
import Vegas.Game.RevealServiceReplayRelation
import Vegas.Game.RevealServiceReplaySource
import Vegas.Game.RevealServiceTraffic
import Vegas.Game.RevealServiceTrafficSound
import Vegas.Game.RevealServiceTrafficDeparture
import Vegas.Game.RevealServiceAuditDeposits
import Vegas.Game.RevealServiceAuditCompilation
import Vegas.Game.RevealServicePerturbation
import Vegas.Game.RevealServiceFocalLaw
import Vegas.Game.RevealServiceFocalRecall
import Vegas.Game.RevealServiceOrdinaryComparison
import Vegas.Game.RevealServicePayoffs
import Vegas.Game.RevealServiceSelector
import Vegas.Game.RevealServiceTranscript
import Vegas.Game.RevealServiceEnforcement
import Vegas.Game.RevealServiceCorrespondence
import Vegas.Game.RevealServiceInformation
import Vegas.Game.RevealServiceObservation
import Vegas.Game.RevealServiceState
import Vegas.Game.RevealServicePolicy
import Vegas.Game.RevealServiceWatcher
import Vegas.Game.EventMessageStrategic
import Vegas.Game.PendingCompositions
import Vegas.Game.ParameterOutcomes
import Vegas.Game.ZeroSum
import Vegas.Game.SetupSubgame
import Vegas.Game.SourceInformation
import Vegas.Game.SourceContinuation
import Vegas.Game.SourceLocalContinuation
import Vegas.Game.SourceStateKernel
import Vegas.Game.SourcePrefixKernel
import Vegas.Game.SourceObservationRecall
import Vegas.Game.BehavioralSubgame

/-! Strategic source-to-graph and graph-to-message correspondence. -/

-- OPEN OBLIGATION: Native subgame-perfect preservation
-- Source continuation laws and conditional SPE transfer and reflection are checked.
-- The reactive protocol has canonical policy correspondence and bounded play.
-- The source policy compiler is defined. Canonical service completion is proved
-- for arbitrary player policies and adaptive network choices.
-- Packet protection, compiler outcome/deviation laws, continuation correspondence,
-- and proper-root coverage remain open. Recovery preserves initialized execution
-- laws, but ReactiveEarlyOpeningSPE proves that the actual recovery compiler fails
-- SPE under a fixed uniform, at-most-once service. Its source policy is honest and
-- SPE. This refutes sufficiency of event-local selection regularity for that compiler;
-- a service or translation contract addressing competition between events is needed.
-- The separate ReactivePendingMenusSource impossibility quantifies over all compilers
-- for its adaptive public scheduler. Neither witness rules out every constrained service.
-- The initial-play Nash/Bayesian theorem does not discharge these obligations.
