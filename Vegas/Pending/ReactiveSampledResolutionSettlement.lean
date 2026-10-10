/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosure

/-! # Actual accepted openings realize original disclosure steps -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A transmitted original resolution decision necessarily chose disclosure. -/
theorem reactiveDecision_resolution_transmitted_true (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event) (view : PlayerView graph)
    (material : WitnessedSubmission graph)
    (transmitted : (runtime.reactiveDecision leaks who event action view).transmission =
      some material) : cast (congrArg EventField.Action outputEq) action = true := by
  cases disclose : cast (congrArg EventField.Action outputEq) action with
  | false => simp [reactiveDecision, node, reactiveResolutionPacket, disclose] at transmitted
  | true => rfl

/-- Every transmitted resolution decision carries exactly a typed opening
for its sampled event, including after compiler normalization. -/
theorem reactiveDecision_resolution_transmitted_packet (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event) (view : PlayerView graph)
    (material : WitnessedSubmission graph)
    (transmitted : (runtime.reactiveDecision leaks who event action view).transmission =
      some material) : ∃ candidate value,
      material.call.packet = .opening event candidate ⟨payload, value⟩ := by
  have chosen := runtime.reactiveDecision_resolution_transmitted_true leaks who owner event
    payload binding checks outputEq codeEq node action view material transmitted
  simp only [reactiveDecision, node, reactiveResolutionPacket, chosen, ite_true] at transmitted
  cases result : EventCode.resolveOutput? binding checks true view.observation.store with
  | none => simp [result] at transmitted
  | some publication =>
      cases publication with
      | failure => simp [result] at transmitted
      | success value =>
          cases associated : view.publicView.accepted binding.field with
          | none => simp [result, associated] at transmitted
          | some candidate =>
              by_cases owned : candidate.1 = who
              · simp only [result, associated, owned, ite_true, Option.map_some,
                  Option.some.injEq] at transmitted
                rw [← transmitted]
                exact ⟨candidate, value, by
                  simp only [WitnessedSubmission.normalizeReactive,
                    Submission.normalizeReactive_packet, disclosureSubmission]⟩
              · simp [result, associated, owned] at transmitted

/-- Actual authenticated acceptance of an opening realizes the original
resolution action. All handler side conditions are derived from acceptance. -/
theorem accepted_resolution_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state after : State graph) (id : MessageId Player)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (candidate : Handle graph) (value : L.Val payload)
    (message : Message Player (WitnessedPacket graph))
    (packet : message.id = id ∧ message.payload.call =
      .opening event candidate ⟨payload, value⟩)
    (sender : id.1 = owner)
    (accepted : (runtime.reactiveApplication leaks).handle state message = some after) :
    ∃ ready : state.config.cut.Ready event,
      PMF.pure after.config = state.config.step event ready action := by
  have physical := reactiveHandle_call accepted
  rw [packet.1, packet.2] at physical
  simp only [handle] at physical
  split at physical
  · rename_i ready
    split at physical
    · simp only [node, Message.sender, sender] at physical
      simp only [dite_eq_ite, Option.ite_none_right_eq_some, true_and] at physical
      obtain ⟨owned, associated, verified, physical⟩ := physical
      split at physical
      · rename_i impossible
        simp only [Raw.as?_mk, reduceCtorEq] at impossible
      · rename_i decoded typed
        have equal : value = decoded := by
          simpa only [Raw.as?_mk, Option.some.injEq] using typed
        subst decoded
        simp only [Option.ite_none_right_eq_some] at physical
        obtain ⟨stored, physical⟩ := physical
        change (EventCode.resolveOutput? binding checks true state.config.store).bind
          (fun result => some (state.complete event ready
            (cast (congrArg EventField.Action outputEq.symm) true)
            (cast (congrArg EventField.Value outputEq.symm) result))) = some after at physical
        cases resultEq : EventCode.resolveOutput? binding checks true state.config.store with
        | none => simp [resultEq] at physical
        | some result =>
            simp only [resultEq, Option.bind_some, Option.some.injEq] at physical
            subst after
            refine ⟨ready, ?_⟩
            have original : cast (congrArg EventField.Action outputEq.symm) true = action := by
              rw [← discloses]
              simp only [cast_cast, cast_eq]
            rw [← original]
            symm
            have law := state.config.step_eq_map_of_code event ready outputEq _ codeEq true
              (PMF.pure result) (by simp only [EventCode.eval?, resultEq, Option.map_some])
            simpa only [PMF.pure_map, State.complete] using law
    · simp at physical
  · simp at physical

/-- Authentic acceptance of the actual emitted compiler resolution packet
realizes its original sampled action at the inclusion state. The packet kind
and TRUE intention follow from transmission, not from a desired step law. -/
theorem reactiveDecision_resolution_accepted_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state after : State graph) (id : MessageId Player)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event) (view : PlayerView graph)
    (material : WitnessedSubmission graph)
    (transmitted : (runtime.reactiveDecision leaks owner event action view).transmission =
      some material)
    (authored : State graph) (known : List (Message Player (WitnessedPacket graph)))
    (sender : id.1 = owner)
    (accepted : (runtime.reactiveApplication leaks).handle state
      ⟨id, material.emit authored owner known⟩ = some after) :
    ∃ ready : state.config.cut.Ready event,
      PMF.pure after.config = state.config.step event ready action := by
  have discloses := runtime.reactiveDecision_resolution_transmitted_true leaks owner owner
    event payload binding checks outputEq codeEq node action view material transmitted
  obtain ⟨candidate, value, packet⟩ := runtime.reactiveDecision_resolution_transmitted_packet
    leaks owner owner event payload binding checks outputEq codeEq node action view material
    transmitted
  apply runtime.accepted_resolution_step leaks state after id owner event payload binding checks
    outputEq codeEq node action discloses candidate value
    ⟨id, material.emit authored owner known⟩ _ sender accepted
  exact ⟨rfl, by simpa only [WitnessedSubmission.emit_call] using packet⟩

end Vegas.EventGraphRuntime
