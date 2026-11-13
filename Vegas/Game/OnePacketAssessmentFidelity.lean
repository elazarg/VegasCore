module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketStrategyFidelity
public import Vegas.Game.OnePacketBeliefFidelity
public import Vegas.Game.OnePacketContinuationFidelity
public import Vegas.Game.OnePacketProjectedSite
public import Interaction.ReactiveResponseEvaluation

@[expose] public section

/-! # Intended assessments realized at native source decisions

The correspondence identifies genuine first source decisions, retains the
intended action law there, and identifies source posteriors through actual
partial replay. Clean source boundaries retain their complete continuation
readout law. All properties concern one common native assessment.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

local notation "Initial" => initialLaw setup
local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds Initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) Initial horizon scheduler

open Classical in
/-- A genuine first native decision at the displayed intended source site
in the forced region. In well-formed setups its source projection entails
cleanliness and no own debt. -/
structure SourceDecisionRealization {who : Player}
    (source : setup.intendedModel.InformationSite who)
    (native : (N).InformationSite who) : Prop where
  projected : source.1 = projectView setup timeouts leaks who native.1
  forced : forcedAgent (timeouts := timeouts) (menu) Initial horizon scheduler who native.1
  first : FirstActivation setup timeouts leaks who native.1

open Classical in
/-- Pointwise intended decision laws, actual replay posteriors and clean-boundary
continuations of one native assessment. The statements include off-path sites. -/
structure OnePacketAssessmentFidelity
    (intended : setup.intendedModel.BehavioralAssessment)
    (native : (N).BehavioralAssessment) : Prop where
  strategy : ∀ {who} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who),
    SourceDecisionRealization setup timeouts leaks bounds horizon scheduler source site →
      native.strategy who site.1 =
        honestChoice setup timeouts leaks bounds Initial horizon scheduler intended who site.1
  belief : ∀ {who} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who),
    source.1 = projectView setup timeouts leaks who site.1 →
    forcedAgent (timeouts := timeouts) (menu) Initial horizon scheduler who site.1 →
    ∀ {past view}, site.1 = some (past, view) →
    ∀ {event}, view.application.publicView.ownTurn? who = some event →
      (native.belief who site).map (fun history =>
        intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace) =
      (intended.belief who source).map (fun history => some history.1)
  continuation : ∀ (rank : Nat) (start : (E).History)
    (anchor : (application setup timeouts leaks).Execution),
    start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ →
    ReachedBoundary setup timeouts leaks horizon scheduler rank anchor →
    ∀ point, sourceServicePrefix? setup rank anchor.application.config = some point →
    ProtocolState.Intended setup.program point →
      ((menu).runFrom Initial horizon scheduler native.strategy start).map
          (fun final => sourceReadout setup timeouts leaks final.state) =
        sourceContinuation setup (setup.intendedOpeningProfile intended.strategy) rank
          anchor.application.config
  coverage : ∀ {who} (source : setup.intendedModel.InformationSite who),
    ∃ site : (N).InformationSite who,
      SourceDecisionRealization setup timeouts leaks bounds horizon scheduler source site
  replay : ∀ {who} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who),
    SourceDecisionRealization setup timeouts leaks bounds horizon scheduler source site →
    ∀ sourceHistory : setup.intendedModel.InformationHistory who source.1,
      ∃ history : (N).InformationHistory who site.1,
        intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
          some sourceHistory.1

end Vegas
