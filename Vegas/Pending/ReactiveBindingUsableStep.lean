/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingCommitmentStep
import Vegas.Pending.ReactiveAuthorizationProgress
import Vegas.Pending.ReactiveBindingFrameCommands
import Vegas.Pending.ReactiveBindingSubmissionFrame
import Vegas.Pending.ReactiveMissingBindingTransport

/-! # Fresh usable owner bindings across actual inclusion and expiry

A usable fresh binding is transmitted unchanged and remembers only its actual
candidate meaning. Its whole frame survives both accepted and rejected inclusion
when the addressed fixed candidate agrees, with no protected-timing premise.
This does not cover reuse of a changed candidate or further unusable bindings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- A commitment failing the actual public inclusion test is rejected on
both executions, regardless of either candidate's private meaning or the packet token. -/
theorem commitment_step_not_includable
    (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
    (blocked : ¬ original.application.publicView.BindingIncludable runtime
      ⟨id, .commitment event candidate⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have rejected (state : State graph)
      (same : state.publicView = original.application.publicView) :
      handle runtime state ⟨id, .commitment event candidate⟩ = none := by
    cases handled : handle runtime state ⟨id, .commitment event candidate⟩ with
    | none => rfl
    | some next =>
        have includable := (State.publicView_bindingIncludable runtime state id event
          candidate).mpr (by simp only [handled, Option.isSome_some])
        exact False.elim (blocked (same ▸ includable))
  exact frame.include_rejected id _ found
    (reactiveHandle_none (rejected original.application rfl))
    (reactiveHandle_none (rejected repaired.application frame.publicView.symm))

/-- Actual owner commitment inclusion preserves the whole frame when both
fixed candidate meanings agree. Public rejection, invalid tokens, late calls
and addressed-node mismatches are derived from the actual handler. -/
theorem commitment_step_matching_owner
    (frame : Frame runtime leaks memory owner original repaired)
    (past : memory.shadow.CompletedAt original.application.config)
    (id : MessageId Player) (authored : id.1 = owner)
    (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
    (fixed : original.application.candidates.lookup candidate ≠ .fresh)
    (matching : original.application.candidates.lookup candidate =
      repaired.application.candidates.lookup candidate) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } ∧
      memory.shadow.CompletedAt (original.includePending app id).application.config := by
  intro app
  have retained := (runtime.reactiveCompletedInvariant leaks
    original.application.config.cut.completed).includePending original id (Finset.Subset.refl _)
  refine ⟨?_, past.mono retained⟩
  let packet : WitnessedPacket graph := ⟨.commitment event candidate, evidence, token⟩
  by_cases valid : packet.tokenValid = true
  swap
  · exact frame.include_rejected id packet found
      (reactiveApplication_handle_of_not_tokenValid runtime leaks original.application _
        (Bool.eq_false_iff.mpr valid))
      (reactiveApplication_handle_of_not_tokenValid runtime leaks repaired.application _
        (Bool.eq_false_iff.mpr valid))
  by_cases allowed : original.application.publicView.BindingIncludable runtime
      ⟨id, .commitment event candidate⟩
  swap
  · exact frame.commitment_step_not_includable id event candidate evidence token found allowed
  obtain ⟨named, addressed, tokened⟩ := (WitnessedPacket.tokenValid_iff packet).mp valid
  have eventEq : named = event := (Option.some.inj addressed).symm
  subst named
  change token = some ⟨event⟩ at tokened
  subst token
  change original.application.publicView.EventReady event ∧
    original.application.WithinDeadline runtime event ∧ _ at allowed
  obtain ⟨publicReady, timely, checks⟩ := allowed
  have ready := (original.application.publicView_eventReady event).mp publicReady
  cases node : nodeView graph event with
  | resolve actor payload binding guards outputEq codeEq => simp only [node] at checks
  | sample payload law outputEq codeEq => simp only [node] at checks
  | bind actor payload outputEq codeEq =>
      simp only [node, Message.sender] at checks
      obtain ⟨sender, owned, vacant, unused⟩ := checks
      rw [authored] at sender
      have sameOwner : actor = owner := sender.symm
      subst actor
      obtain ⟨noAction, noValue⟩ := past.ready_none event ready
      have sameResult : repaired.application.bindingResult candidate payload =
          original.application.bindingResult candidate payload := by
        unfold State.bindingResult
        rw [matching]
      exact frame.binding_inclusion_unmodified id event candidate owner payload outputEq codeEq
        node ready timely authored owned vacant unused fixed (matching ▸ fixed) sameResult
          noValue noAction evidence found

/-- A real usable fresh response establishes matching fixed candidate meanings
and completed-boundary memory before any inclusion. Expiry can therefore use the
existing arbitrary-command frame law, without an intended-success override. -/
theorem fresh_usable_submission_resources
    (frame : Frame runtime leaks memory owner original repaired)
    (past : memory.shadow.CompletedAt original.application.config)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (raw : Raw L) (value : L.Val payload)
    (typed : raw.as? payload = some value)
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : original.application.config.cut.Ready event) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), some raw⟩, .none⟩⟩
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    let updated : BindingMemory runtime leaks :=
      ⟨changed.2, memory.responses ++
        [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩
    let left := original.respond app owner response
    let right := repaired.respond app owner changed.1
    Frame runtime leaks updated owner left right ∧
      updated.shadow.CompletedAt left.application.config ∧
      left.application.candidates.lookup (owner, .prepared serial) = .openable raw ∧
      right.application.candidates.lookup (owner, .prepared serial) = .openable raw := by
  intro app response changed updated left right
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView runtime leaks
      (repaired.observe app owner)).application.candidates (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have decoded : (some raw).bind (fun raw => raw.as? payload) = some value := typed
  have changedEq := memory.repairResponse_usable runtime leaks owner
    (repaired.observe app owner) event payload outputEq codeEq node serial (some raw)
      ownFresh actualFresh value decoded
  refine ⟨frame.binding_submission event payload outputEq codeEq node serial (some raw) fresh
    ready, ?_, runtime.bareBinding_submitted_openable leaks original owner event serial raw fresh,
    ?_⟩
  · have changedShadow := congrArg Prod.snd changedEq
    change changed.2 = _ at changedShadow
    have remembered := past.rememberCandidate (.prepared serial)
      ((⟨.commitment event (owner, .prepared serial), some raw⟩ : Submission graph).candidateAfter
        owner (memory.shadow.inputView runtime leaks
          (repaired.observe app owner)).application.candidates (.prepared serial))
    change changed.2.CompletedAt left.application.config
    rw [(runtime.reactive_respond_application leaks original owner response).1]
    exact changedShadow.symm ▸ remembered
  · change (repaired.respond app owner changed.1).application.candidates.lookup _ = _
    rw [congrArg Prod.fst changedEq]
    exact runtime.bareBinding_submitted_openable leaks repaired owner event serial raw actualFresh

end Vegas.EventGraphRuntime.BindingMemory.Frame
