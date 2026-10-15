/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingNativeResponse

/-! # Count admission discharges native response replay guards -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Authentic local authorization discharges both actual physical masks. -/
theorem localEnvelope_admitted (physical : (phaseApplication runtime leaks).Execution)
    (who : Player) (material : WitnessedSubmission graph)
    (authorized : (PhaseCount.localEnvelope runtime leaks who (physical.recall who)
      (physical.observe (phaseApplication runtime leaks) who) material).payload.packet.tokenValid =
        true) :
    physical.application.allows material.call.packet = true ∧
      physical.application.current.excludedCall material.call.packet = false := by
  let packet : WitnessedPacket graph :=
    ⟨material.call.packet, material.evidence.resolve who
      (material.call.candidateAfter who
        (physical.application.current.native.playerView who).candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets (physical.recall who)
        (physical.observe (phaseApplication runtime leaks) who)).map PhaseCount.nativeMessage),
      physical.application.current.native.publicView.tokenFor material.call.packet⟩
  change (PhaseCount.maskPacket physical.application.publicView packet).tokenValid = true
    at authorized
  have allowed : PhaseCount.allows physical.application.publicView packet.call = true := by
    cases permission : PhaseCount.allows physical.application.publicView packet.call with
    | false =>
        simp only [PhaseCount.maskPacket, permission, Bool.false_eq_true, ↓reduceIte,
          WitnessedPacket.tokenValid_none] at authorized
    | true => rfl
  have unexcluded : PhaseCount.excludedCall physical.application.publicView packet.call =
      false := by
    cases excluded : PhaseCount.excludedCall physical.application.publicView packet.call with
    | false => rfl
    | true =>
        simp only [PhaseCount.maskPacket, allowed, excluded, ↓reduceIte,
          WitnessedPacket.tokenValid_none, Bool.false_eq_true] at authorized
  exact ⟨(PhaseCount.allows_publicView _ _).symm.trans allowed, unexcluded⟩

variable [Fintype Player] (bounds : MessageBounds graph)

/-- Every actual counted response projects to its native response. Raw evidence
requests and preparation syntax remain unrestricted by the statement. -/
theorem execution_respond_of_onePacket
    (physical : (phaseApplication runtime leaks).Execution) (who : Player)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (physical.recall who) (physical.observe (phaseApplication runtime leaks) who)) :
    execution runtime leaks (physical.respond (phaseApplication runtime leaks) who response) =
      (execution runtime leaks physical).respond
        (runtime.reactiveApplication (nativeLeaks (graph := graph))) who
          (action runtime leaks response) := by
  apply execution_respond runtime leaks physical who response
  intro material transmitted
  have permitted := ((PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mp
    member).2
  rcases permitted with silent | ⟨other, emitted, allowed⟩
  · rw [transmitted] at silent
    cases silent
  · have same : other = material := Option.some.inj (emitted.symm.trans transmitted)
    subst other
    exact localEnvelope_admitted runtime leaks physical who material
      ((PhaseCount.permits_eq_true_iff _ _).mp allowed).1

/-- The repair starts at the real clear initialized prefix. Empty retirement is
derived from the actual history, rather than imposed as an extra runtime condition. -/
theorem frame_at_clear_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (owner : Player) :
    Frame runtime leaks (BindingMemory.atRecall runtime (nativeLeaks (graph := graph))
      ((execution runtime leaks control.execution).recall owner)) owner
        control.execution control.execution := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace
  exact frame_atRecall owner control.execution clear
    (phase_clear_history runtime leaks plan inputs horizon scheduler control raw clear).2

end Vegas.EventGraphRuntime.PhaseBindingRepair
