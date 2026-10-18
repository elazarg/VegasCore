/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalRetention
import Vegas.Compile.EventGraphEvaluation
import Vegas.Source.ProposalRecoveryDisclosure

/-! # Source prestate readback of actual submitted counted proposals -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Compiler context agreement reads a submitted plaintext from the actual
source binding. This applies to the prestate used by source-order publication
replay, independently of the proposal's accepting or rejecting receipt. -/
theorem submitted_proposal_source_binding
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw))
    (sameAttempt : coordinate.attempt = current.execution.application.attempt)
    {Γ : SourceCtx Player L} {owner : Player} {name : VarId} {payload : L.Ty}
    (refs : ContextRefs graph.layout Γ) (sourceConfig : Config Player L Γ)
    (source : HasVar Γ name (.commitment owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout coordinate.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes coordinate.event) =
      .resolve owner payload (refs.get source) checks)
    (agree : refs.Agrees sourceConfig.state
      current.execution.application.current.native.config.store) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
      sourceConfig.state.get source = .success value := by
  obtain ⟨value, typed, stored⟩ := submitted_proposal_current_binding_meaning runtime leaks
    bounds plan ordered inputs horizon scheduler current trace message submitted coordinate raw
      proposed sameAttempt owner payload (refs.get source) checks outputEq codeEq
  have readback := agree source
  change (refs.get source).get? current.execution.application.current.native.config.store =
    some (sourceConfig.state.get source) at readback
  exact ⟨value, typed, Option.some.inj (readback.symm.trans stored)⟩

/-- The actual source proposal decoder returns that same typed value whenever
the lifted reveal is labeled as a proposal. The label supplies no plaintext. -/
theorem submitted_proposal_source_delta
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw))
    (sameAttempt : coordinate.attempt = current.execution.application.attempt)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (refs : ContextRefs graph.layout Γ) (sourceConfig : Config Player L Γ)
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout coordinate.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes coordinate.event) =
      .resolve owner payload (refs.get source) checks)
    (agree : refs.Agrees sourceConfig.state
      current.execution.application.current.native.config.store)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (disclosed : ((joint owner).map (·.discloses)).getD false = true) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
      ProtocolState.recoveryProposal
        (.reveal published owner name fresh source unresolved next)
        (.inl sourceConfig) joint = some (0, ⟨payload, value⟩) := by
  obtain ⟨value, typed, stored⟩ := submitted_proposal_source_binding runtime leaks bounds plan
    ordered inputs horizon scheduler current trace message submitted coordinate raw proposed
      sameAttempt refs sourceConfig source checks outputEq codeEq agree
  exact ⟨value, typed, ProtocolState.recoveryProposal_reveal_success fresh source unresolved next
    sourceConfig joint disclosed value stored⟩

end Vegas.EventGraphRuntime.PhaseProposal
