/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseRecordedBindingMeaning
import Interaction.ReactiveInvariantPrefix
import Interaction.ReactiveRecordedResponseAfter

/-! # The permanent typed meaning of arbitrary recorded private binding material -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A recorded fresh private preparation determines its exact typed binding
result through every later physical operation. Evidence and private raw types
are arbitrary; the result may be successful or unusable. -/
theorem phase_recorded_material_binding_result (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (payload : L.Ty) (serial : Nat)
    (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall who)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh) :
    control.execution.application.current.native.bindingResult (who, .prepared serial) payload =
      (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success := by
  let app := phaseApplication runtime leaks
  let result := (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success
  let candidate : Handle graph := (who, .prepared serial)
  have invariant : app.Invariant (fun state =>
      state.current.native.candidates.lookup candidate ≠ .fresh ∧
        state.current.native.bindingResult candidate payload = result) := by
    let stable := phaseApplication_preservesFixedCandidates runtime leaks
    constructor
    · intro state owner material valid
      have retained := stable.submit state owner material candidate valid.1
      dsimp only [app]
      exact ⟨by simpa only [retained] using valid.1,
        by simpa only [State.bindingResult, retained] using valid.2⟩
    · intro state message next valid handled
      have retained := stable.handle state message next handled candidate valid.1
      exact ⟨by simpa only [retained] using valid.1,
        by simpa only [State.bindingResult, retained] using valid.2⟩
    · intro state command next valid reached
      have retained := stable.environment state command next reached candidate valid.1
      exact ⟨by simpa only [retained] using valid.1,
        by simpa only [State.bindingResult, retained] using valid.2⟩
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
  obtain ⟨remaining, execution, _prior, post, kept, _past, viewed, _allowed, _before, _length⟩ :=
    menu.recorded_response_after initial horizon scheduler control trace who
      earlier entry later recalled
  have freshHere : execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh := by
    rw [viewed] at fresh
    exact fresh
  have registered :
      (execution.respond app who entry.action).application.current.native.bindingResult
        candidate payload = result := by
    rw [declared]
    change (submitStep (Submission.register
      ⟨.commitment event (who, .prepared serial), opening⟩
        execution.application.current.native who) who
          (.commitment event (who, .prepared serial))).bindingResult _ payload = _
    rw [submitStep_bindingResult]
    cases opening with
    | none => simp only [result, candidate, Submission.register, State.bindingResult, freshHere,
        Option.bind_none, Option.elim_none]
    | some raw =>
        simp only [result, candidate, Submission.register, ite_true, State.bindingResult,
          CommitmentCandidates.lookup_prepare_self, freshHere, Option.bind_some]
  have fixed : (execution.respond app who entry.action).application.current.native.candidates.lookup
      candidate ≠ .fresh := by
    rw [declared]
    change (submitStep _ who (.commitment event (who, .prepared serial))).candidates.lookup
      (who, .prepared serial) ≠ .fresh
    exact submitStep_commitment_fixed _ who event (.prepared serial)
  exact (invariant.tracePrefix menu initial horizon scheduler
    ⟨remaining, none, execution.respond app who entry.action⟩ control post trace kept
      ⟨fixed, registered⟩).2

end Vegas.EventGraphRuntime
