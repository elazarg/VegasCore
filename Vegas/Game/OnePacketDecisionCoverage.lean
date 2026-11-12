module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketSourceCoverage
public import Vegas.Game.OnePacketDecisionRealization

@[expose] public section

/-! # Coverage of intended source information sites

Every intended source history at an information site has a genuine native
first activation at that same decoded source state. In particular, the native
decision-realization relation covers every intended source information site,
including those outside the preserved equilibrium's support.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler

variable (wellFormed : setup.WellFormed)
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) → control.execution.application.config.defaulted = ∅ →
    OpportunityAt timeouts leaks control.execution delay)
  (inclusion : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) → control.execution.application.config.defaulted = ∅ →
    ProtectedInclusionAt timeouts leaks control.execution bound)
  (timely : AsyncTimely timeouts delay bound)
  (completes : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) → control.execution.application.config.defaulted = ∅ →
    (application setup timeouts leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
  (covers : bounds.CoversOutputValues)
  (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
  (certificate : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
    horizon scheduler).WellFoundedHistories)
  (reference : setup.intendedModel.BehavioralAssessment) (full : reference.IsFullyMixed)

include wellFormed opportunity inclusion timely completes covers capacity certificate reference full
  in
/-- Every intended source history in a genuine decision fiber has a native
first activation realizing its source site and exact complete source state. -/
theorem exists_sourceDecisionRealization_of_intended_history
    {who : Player} (source : setup.intendedModel.InformationSite who)
    (sourceHistory : setup.intendedModel.InformationHistory who source.1) :
    ∃ site : (N).InformationSite who,
      SourceDecisionRealization setup timeouts leaks bounds horizon scheduler source site ∧
      ∃ history : (N).InformationHistory who site.1,
        nativeDecodedState setup timeouts leaks history.1.state = sourceHistory.1.state := by
  have active := InformationSite.active setup.intendedModel source sourceHistory
  cases sourceState : sourceHistory.1.state with
  | none =>
    rw [sourceState] at active
    change False at active
    exact active.elim
  | some point =>
    obtain ⟨rank, start, execution, current, boundary, decoded, intended⟩ :=
      exists_native_boundary_of_intended_history wellFormed opportunity inclusion timely completes
        covers capacity certificate reference full who sourceHistory.1.trace point sourceState
    obtain ⟨site, realizes, history, same⟩ :=
      exists_sourceDecisionRealization_of_boundary opportunity timely completes certificate
        (honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler reference)
        rank start execution current boundary point decoded intended source sourceHistory
          sourceState
    exact ⟨site, realizes, history, same⟩

include wellFormed opportunity inclusion timely completes covers capacity certificate reference full
  in
/-- The native first-decision realization relation covers every intended
information site, regardless of its probability under a later equilibrium. -/
theorem exists_sourceDecisionRealization
    {who : Player} (source : setup.intendedModel.InformationSite who) :
    ∃ site : (N).InformationSite who,
      SourceDecisionRealization setup timeouts leaks bounds horizon scheduler source site := by
  obtain ⟨history, _, _⟩ := source.2
  obtain ⟨site, realizes, _⟩ :=
    exists_sourceDecisionRealization_of_intended_history wellFormed opportunity inclusion timely
      completes covers capacity certificate reference full source history
  exact ⟨site, realizes⟩

end Vegas
