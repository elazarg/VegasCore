/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseLatestBindings

/-! # Authentic token-valid packets name their physical source phase -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Physical token masking prevents every packet emitted outside its current
phase interval from possessing a valid readiness token. -/
theorem emit_address_lower (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) (event : graph.EventId)
    (valid : (state.emit who known material).packet.tokenValid = true)
    (named : (state.emit who known material).packet.call.event? graph = some event) :
    (state.emit who known material).attempt.phase ≤ event.val := by
  let packet := state.current.emit who
    (known.map fun message => ⟨message.id, message.payload.packet⟩) material
  change (if state.allows packet.call then packet else {packet with token := none}).tokenValid =
    true at valid
  change (if state.allows packet.call then packet else {packet with token := none}).call.event?
    graph = some event at named
  change state.attempt.phase ≤ event.val
  cases allowed : state.allows packet.call with
  | false =>
      simp only [allowed, Bool.false_eq_true, ↓reduceIte, WitnessedPacket.tokenValid_none] at valid
  | true =>
      simp only [allowed, ↓reduceIte] at named
      obtain ⟨phase, head, actual, addressed, inside⟩ := state.allows_event packet.call allowed
      have same : actual = event := Option.some.inj (addressed.symm.trans named)
      subst actual
      have member : state.phases.head? = some phase := head
      simpa only [attempt, member, Option.map_some, Option.getD_some] using
        ((phase.mem_events event).mp inside).1

end PhaseRuntimeState

/-- Authentic authored packet provenance supplies the lower phase rank for
every token-valid signed input, independently of inclusion or count cleanliness. -/
theorem issued_address_lower (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution)
    (message : Message Player (CommitAttemptPacket graph))
    (issued : execution.Issued (phaseApplication runtime leaks) message)
    (event : graph.EventId) (valid : message.payload.packet.tokenValid = true)
    (named : message.payload.packet.call.event? graph = some event) :
    message.payload.attempt.phase ≤ event.val := by
  obtain ⟨entry, present, material, transmitted, emitted, state, known, packet⟩ := issued
  change state.emit message.sender known material = message.payload at packet
  rw [← packet] at valid named ⊢
  exact state.emit_address_lower message.sender known material event valid named

end Vegas.EventGraphRuntime
