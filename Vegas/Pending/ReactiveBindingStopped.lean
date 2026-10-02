/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingClassification
import Interaction.ReactiveTrafficState

/-! # Concrete stopping evidence at a required binding response

Every bounded effective response is covered. Canonical public commitments may
contain unusable hidden material and remain in the repair branch. Other emitted
packets produce an authentic record. Silence and spent replay produce the
public missed-binding obligation through actual protected expiry.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The protected binding block has a public, exhaustive stopping condition.
The canonical branch does not test hidden value validity. The other two cases
carry actual traffic or actual deadline evidence, rather than missing samples. -/
theorem protected_binding_response_cases (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (absent : execution.application.accepted (.inr event) = none)
    (prefixFresh : execution.application.PreparedPrefix who)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (knownPublished : ∀ message ∈ execution.network.known who,
      message.id ∈ execution.network.ledger.map Message.id)
    (pendingPublished : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock + ticks - entered)
    (response : (runtime.reactiveApplication leaks).Action)
    (available : response ∈ (bounds.menu runtime leaks).actions who
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)) :
    let app := runtime.reactiveApplication leaks
    let serial := execution.application.publicView.bindingCount who
    (∃ opening, bounds.AllowsOpening opening ∧ response =
      ⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩) ∨
    (∃ record, app.trafficStep (some ⟨remaining, some who, execution⟩)
        (some ⟨remaining, none, execution.respond app who response⟩) = [record] ∧
      record.input.envelope.sender = who ∧
      record.input.envelope.payload ≠
        ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩) ∨
    (∃ next, runtime.runInteractionPlan leaks players scheduler
        (.includeLatest event who :: List.replicate ticks .tick ++ [.expire event])
          (execution.respond app who response) = PMF.pure next ∧
      next.application.publicView.missedBinding event = true) := by
  let app := runtime.reactiveApplication leaks
  let serial := execution.application.publicView.bindingCount who
  have fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh :=
    (prefixFresh serial).mpr (Nat.le_refl _)
  have known := app.known_from_recall execution who recalled
  change execution.network.known who = ReactiveApplication.ResponseMenu.knownPackets
    (execution.recall who) (execution.observe app who) at known
  have member := (bounds.menu_mem runtime leaks who _ _ response).mp available
  have omitted (quiet : response = ⟨none⟩ ∨ ∃ id ∈ execution.network.ledger.map Message.id,
      response = ⟨some (.replay id)⟩) :=
    runtime.silent_or_spent_binding_omission leaks players scheduler execution who event payload
      outputEq codeEq node ready absent pendingPublished entered ticks activated due response quiet
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inr (Or.inr (omitted (Or.inl rfl)))
  | some transmission =>
      cases transmission with
      | replay id =>
          obtain ⟨message, inKnown, same⟩ :=
            (ReactiveApplication.SubmissionNormalization.replayKnown_iff execution who
              recalled id).mp member.1
          exact Or.inr (Or.inr (omitted (Or.inr
            ⟨id, same ▸ knownPublished message inKnown, rfl⟩)))
      | submit submission =>
          by_cases canonical : submission.emit (app.submit execution.application who submission)
              who (execution.network.known who) =
                ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩
          · have normal : submission.normalizeReactive who
                (app.observePlayer execution.application who)
                  (execution.network.known who) = submission := by
              have fixed := member.2
              change (⟨some (.submit (submission.normalizeReactive who _ _))⟩ : app.Action) =
                ⟨some (.submit submission)⟩ at fixed
              have same := ReactiveApplication.Transmission.submit.inj
                (Option.some.inj (congrArg ReactiveApplication.Action.transmission fixed))
              rw [← known] at same
              exact same
            have shape := runtime.normal_binding_of_canonical_packet leaks execution.application
              who (execution.network.known who) submission event serial fresh normal canonical
            exact Or.inl ⟨submission.call.opening, member.1.1.2,
              congrArg (fun material => (⟨some (.submit material)⟩ : app.Action)) shape⟩
          · let record : app.TrafficRecord :=
              ⟨execution.application.publicView, execution.network.ledger,
                ⟨who, ⟨(who, execution.network.nextSerial who), submission.emit
                  (app.submit execution.application who submission) who
                    (execution.network.known who)⟩⟩⟩
            refine Or.inr (Or.inl ⟨record, ?_, rfl, canonical⟩)
            exact app.trafficStep_submit execution remaining who submission

end Vegas.EventGraphRuntime
