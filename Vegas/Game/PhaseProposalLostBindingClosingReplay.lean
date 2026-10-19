/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingBeforeClosure
import Vegas.Game.PhaseProposalLostBindingAfterClosure
import Interaction.ReactiveEnvironmentMass

/-! # The actual primitive closing command of a lost binding

The original pre-normalization witness rules out accepting the omitted
packet at the closing include itself. Its actual image is then constructed
through the same environment kernel, including drain and restoration.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The original closing INCLUDE cannot be the omitted binding's packet.
Command identity comes from the literal scheduler recall, before any restore. -/
theorem phase_lost_binding_closing_include_rejected
    (before after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before after current)
    (phase : RuntimePhase graph) (event : graph.EventId) (candidate : Handle graph)
    (unaccepted : (phase.drain current).native.accepted (.inr event) = none)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : before.network.lookup id = some message)
    (call : message.payload.packet.call = .commitment event candidate)
    (moved : after ∈ (before.environmentStep app (.include id)).support) :
    before.application.handle runtime message = none := by
  rcases effect with ⟨otherId, other, native, otherFound, otherMoved, handled, rfl⟩ |
    ⟨command, native, otherMoved, _supported, _current⟩
  · have same := (app).environmentStep_command_unique before after (.include otherId)
      (.include id) otherMoved moved
    have ids : otherId = id := ReactiveApplication.Command.include.inj same
    subst otherId
    have messages : other = message := Option.some.inj (otherFound.symm.trans found)
    subst other
    exact False.elim (phase_closing_inclusion_call_ne_of_omission runtime
      before.application.current message native handled phase event candidate unaccepted call)
  · have impossible := (app).environmentStep_command_unique before after (.application command)
      (.include id) otherMoved moved
    cases impossible

/-- Every actual closing command transports to an actual physical image,
including the case where INCLUDE itself retires the attempt. -/
theorem phase_lost_binding_closing_environment_replay
    (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (before image after : (app).Execution)
    (paired : image.eraseRecall app owner =
      ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution before).eraseRecall
        app owner)
    (command : (app).Command) (moved : after ∈ (before.environmentStep app command).support)
    (current : RecoveryState graph) (effect : PhaseClosingEffect runtime leaks before after current)
    (phase : RuntimePhase graph) (event : graph.EventId)
    (unaccepted : (phase.drain current).native.accepted (.inr event) = none)
    (unused : before.application.current.native.HandleUnused (owner, slot))
    (unique : ∀ message, message ∈ before.network.inputs → ∀ otherEvent,
      message.payload.packet.call = .commitment otherEvent (owner, slot) →
        message.payload.packet.call = .commitment event (owner, slot))
    (origins : before.Provenance app) (recalled : before.InputRecall app) :
    ∃ target ∈ (image.environmentStep app command).support,
      target.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution after).eraseRecall
          app owner := by
  apply HiddenSwap.preparationOnly_environment_erased owner slot first second before image paired
    command after moved unused
  intro id message otherEvent selected found named
  subst command
  have input := ((app).retained_envelopes_mem_inputs before origins recalled).lookup
    id message found
  exact phase_lost_binding_closing_include_rejected runtime leaks before after current effect
    phase event (owner, slot) unaccepted id message found
      (unique message input otherEvent named) moved

end Vegas.EventGraphRuntime
