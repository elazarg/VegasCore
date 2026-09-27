/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRepair

/-! # Inclusion of arbitrary private commitment material

The submitted packet is opaque. Missing and mistyped opening material both
produce the typed failed binding, while retaining their distinct private raw
catalog entries. Acceptance and its receipt do not certify hidden usability.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem submitted_bindingResult (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty) (serial : Nat)
    (opening : Option (Raw L))
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩
    (execution.respond (runtime.reactiveApplication leaks) who response).application.bindingResult
      (who, .prepared serial) payload =
      (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success := by
  cases opening with
  | none =>
      change (submitStep execution.application who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh, Option.bind_none, Option.elim_none]
  | some raw =>
      change (submitStep (Submission.register
        ⟨.commitment event (who, .prepared serial), some raw⟩ execution.application who) who
          (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [Submission.register, ↓reduceIte, State.bindingResult,
        CommitmentCandidates.lookup_prepare_self, fresh, Option.bind_some]

/-- Actual reserved inclusion keeps the exact typed result of arbitrary raw
material, with a successful receipt even when that typed result is failure. -/
theorem rawBinding_reserved_config
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (who, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩
    let result := (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success
    (runtime.interactionStep leaks players scheduler (.includeLatest event who)
      (execution.respond (runtime.reactiveApplication leaks) who response)).map
        (fun final => (final.application.config, final.receipts)) =
      FinDist.pure (execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) result)
        (cast (congrArg EventField.Value outputEq.symm) result),
          execution.receipts ++ [((who, execution.network.nextSerial who), true)]) := by
  let app := runtime.reactiveApplication leaks
  let call : Submission graph := ⟨.commitment event (who, .prepared serial), opening⟩
  let submission : WitnessedSubmission graph := ⟨call, .none⟩
  let response : app.Action := ⟨some (.submit submission)⟩
  let submitted := execution.respond app who response
  let id : MessageId Player := (who, execution.network.nextSerial who)
  have selected : runtime.reactiveLatest leaks event who (submitted.observeEnvironment app) =
      .include id := runtime.reactiveLatest_after_submit leaks who event execution serials
        submission rfl
  have selectedStep : runtime.interactionStep leaks players scheduler (.includeLatest event who)
      submitted = submitted.environmentStep app (.include id) := by
    unfold interactionStep
    rw [interactionInstruction, selected, FinDist.pure_bind]
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    exact FinDist.bind_pure _
  have configEq : submitted.application.config = execution.application.config := by
    change (submitStep (call.register execution.application who) who call.packet).config = _
    rw [submitStep_config, (call.register_facts who execution.application).1]
  have publicEq : submitted.application.publicView = execution.application.publicView := by
    change (submitStep (call.register execution.application who) who call.packet).publicView = _
    rw [submitStep_publicView, (call.register_facts who execution.application).2.2]
  have accepted := congrArg PublicView.accepted publicEq
  have submittedReady : submitted.application.config.cut.Ready event := by rwa [configEq]
  have submittedTimely : submitted.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline
    rw [show submitted.application.clock = execution.application.clock from
      congrArg PublicView.clock publicEq,
      show submitted.application.activatedAt = execution.application.activatedAt from
        congrArg PublicView.activatedAt publicEq]
    exact timely
  have submittedVacant := (congrFun accepted (.inr event)).trans vacant
  have submittedUnused : submitted.application.HandleUnused (who, .prepared serial) := by
    intro field associated
    exact unused field ((congrFun accepted field).symm.trans associated)
  have found : submitted.network.lookup id =
      some ⟨id, ⟨.commitment event (who, .prepared serial), none⟩⟩ :=
    serials.lookup_submit who ⟨.commitment event (who, .prepared serial), none⟩
  have handled := runtime.handle_commitment_eq submitted.application id event
    (who, .prepared serial) who payload outputEq codeEq node submittedReady submittedTimely
      rfl rfl submittedVacant submittedUnused
  have meaning := runtime.submitted_bindingResult leaks execution who event payload serial
    opening fresh
  change submitted.application.bindingResult (who, .prepared serial) payload = _ at meaning
  dsimp only
  change (runtime.interactionStep leaks players scheduler (.includeLatest event who)
    submitted).map _ = _
  rw [selectedStep]
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  change FinDist.pure ((handle runtime submitted.application
    ⟨id, .commitment event (who, .prepared serial)⟩).getD submitted.application |>.config,
      submitted.receipts ++ [(id, (handle runtime submitted.application
        ⟨id, .commitment event (who, .prepared serial)⟩).isSome)]) = _
  rw [handled, Option.getD_some, Option.isSome_some]
  change FinDist.pure (submitted.application.config.complete event submittedReady
    (cast (congrArg EventField.Action outputEq.symm) (submitted.application.bindingResult _ _))
    (cast (congrArg EventField.Value outputEq.symm) (submitted.application.bindingResult _ _)),
      execution.receipts ++ [(id, true)]) = _
  rw [meaning]
  simp only [configEq]
  rfl

end Vegas.EventGraphRuntime
