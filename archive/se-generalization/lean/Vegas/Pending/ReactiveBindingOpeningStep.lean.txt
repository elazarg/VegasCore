/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAcceptedOpening

/-! # Actual opening inclusion before the first signed breach

Both application rejections preserve the repair frame and their real receipt.
An opening accepted only after repair must be authored by the repaired owner
and have no matching certificate in the common actual traffic. These facts
identify the stopping envelope without an additional penalty or payoff bound.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Rejected inclusions consume the same actual envelope and record a false
receipt on both sides, preserving application states and the full repair frame. -/
theorem include_rejected (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (packet : WitnessedPacket graph)
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (leftRejected : (runtime.reactiveApplication leaks).handle original.application
      ⟨id, packet⟩ = none)
    (rightRejected : (runtime.reactiveApplication leaks).handle repaired.application
      ⟨id, packet⟩ = none) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  let app := runtime.reactiveApplication leaks
  have rightFound : repaired.network.lookup id = some ⟨id, packet⟩ := frame.network ▸ found
  have applied (execution : app.Execution)
      (located : execution.network.lookup id = some ⟨id, packet⟩)
      (rejected : app.handle execution.application ⟨id, packet⟩ = none) :
      (execution.includePending app id).application = execution.application ∧
      (execution.includePending app id).receipts = execution.receipts ++ [⟨id, false⟩] ∧
      (execution.includePending app id).recall = execution.recall := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      located, rejected, Option.getD_none, Option.isSome_none]
    exact ⟨trivial, trivial, trivial⟩
  have left := applied original found leftRejected
  have right := applied repaired rightFound rightRejected
  have nextNetwork : (original.includePending app id).network =
      (repaired.includePending app id).network := by
    rw [app.includePending_network, app.includePending_network, frame.network]
  refine ⟨?_, ?_, ?_, nextNetwork, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change memory.restoreRecall runtime leaks ((repaired.includePending app id).recall owner) =
      (original.includePending app id).recall owner
    rw [left.2.2, right.2.2]
    exact frame.past
  · change (⟨(repaired.includePending app id).network.observe owner,
      memory.shadow.view (app.observePlayer (repaired.includePending app id).application owner),
        (repaired.includePending app id).receipts⟩ : app.PlayerView) =
      ⟨(original.includePending app id).network.observe owner,
        app.observePlayer (original.includePending app id).application owner,
          (original.includePending app id).receipts⟩
    rw [left.1, right.1, left.2.1, right.2.1, nextNetwork, frame.receipts]
    exact congrArg (fun view => (⟨(repaired.includePending app id).network.observe owner,
      view, repaired.receipts ++ [⟨id, false⟩]⟩ : app.PlayerView))
        (congrArg ReactiveApplication.PlayerView.application frame.observed)
  · change ((repaired.includePending app id).recall owner).length = memory.responses.length
    rw [right.2.2]
    exact frame.lengths
  · change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
    rw [frame.service, frame.environment]
  · intro who different
    change (original.includePending app id).application.playerView who =
      (repaired.includePending app id).application.playerView who
    rw [left.1, right.1]
    exact frame.views who different
  · intro who different
    change (original.includePending app id).recall who =
      (repaired.includePending app id).recall who
    rw [left.2.2, right.2.2]
    exact frame.recall who different
  · intro slot
    change (original.includePending app id).application.candidates.lookup (owner, slot) = .fresh ↔
      (repaired.includePending app id).application.candidates.lookup (owner, slot) = .fresh
    rw [left.1, right.1]
    exact frame.slots slot
  · change (original.includePending app id).application.config.store.BindingRefines
      (repaired.includePending app id).application.config.store
    rw [left.1, right.1]
    exact frame.successful
  · change runtime.submissionRecall leaks ((original.includePending app id).recall owner) =
      runtime.submissionRecall leaks ((repaired.includePending app id).recall owner)
    rw [left.2.2, right.2.2]
    exact frame.submissions

/-- Foreign authenticated candidate catalogues are unchanged by the repair.
Thus a repaired-only opening acceptance is necessarily the owner's action. -/
theorem repaired_only_opening_sender
    (frame : Frame runtime leaks memory owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (next : State graph)
    (accepted : handle runtime repaired.application ⟨id, .opening event candidate raw⟩ =
      some next)
    (rejected : handle runtime original.application ⟨id, .opening event candidate raw⟩ = none) :
    id.1 = owner := by
  obtain ⟨rightReady, rightTimely, sender, owned, rightAssociated, value, rawEq, rightFixed,
      rightStored, result, rightResolved⟩ := runtime.handle_opening_at_resolve_facts
        repaired.application next id event candidate raw actor payload binding checks outputEq
          codeEq node accepted
  subst raw
  by_contra foreign
  have actorForeign : actor ≠ owner := by rwa [← sender]
  have tables := congrArg PlayerView.candidates (frame.views actor actorForeign)
  have leftFixed : original.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩ := by
    have same := congrFun tables candidate.2
    change original.application.candidates.lookup (actor, candidate.2) =
      repaired.application.candidates.lookup (actor, candidate.2) at same
    have eta : (actor, candidate.2) = candidate := by
      exact Prod.ext owned.symm rfl
    rw [eta] at same
    exact same.trans rightFixed
  have acceptedEq := congrArg PublicView.accepted frame.publicView
  have associated : original.application.accepted binding.field = some candidate :=
    (congrFun acceptedEq binding.field).trans rightAssociated
  have leftStored := leftBinding.opening_stored binding candidate value associated leftFixed
  obtain ⟨ready, timely, _, resolved⟩ := opening_right_facts runtime repaired.application
    original.application frame.publicView.symm event actor payload binding checks candidate
      rightReady rightTimely rightAssociated value rightStored leftStored result rightResolved
  have handled := handle_opening_eq runtime original.application id event candidate actor
    payload binding checks outputEq codeEq node ready timely sender owned associated value
      leftFixed leftStored result resolved
  rw [rejected] at handled
  cases handled

/-- The full actual opening inclusion transition preserves the frame or reaches
a concrete owner-authored signed breach in the common pending traffic. Invalid
tokens and two application rejections are coupled, rather than stipulated bad. -/
theorem opening_step_or_owner_breach
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } ∨
      id.1 = owner ∧
        SignedContentBreach ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩ := by
  let app := runtime.reactiveApplication leaks
  let packet : WitnessedPacket graph := ⟨.opening event candidate raw, evidence, token⟩
  by_cases valid : packet.tokenValid = true
  swap
  · exact Or.inl (frame.include_rejected id packet found
      (reactiveApplication_handle_of_not_tokenValid runtime leaks original.application _
        (Bool.eq_false_iff.mpr valid))
      (reactiveApplication_handle_of_not_tokenValid runtime leaks repaired.application _
        (Bool.eq_false_iff.mpr valid)))
  obtain ⟨named, addressed, tokened⟩ := (WitnessedPacket.tokenValid_iff packet).mp valid
  have eventEq : named = event := (Option.some.inj addressed).symm
  subst named
  change token = some ⟨event⟩ at tokened
  subst token
  cases leftHandled : handle runtime original.application ⟨id, .opening event candidate raw⟩ with
  | some next =>
      exact Or.inl (frame.accepted_opening_inclusion onlyBindings leftBinding rightBinding id
        event candidate raw actor payload binding checks outputEq codeEq node evidence found next
          leftHandled)
  | none =>
      cases rightHandled : handle runtime repaired.application
          ⟨id, .opening event candidate raw⟩ with
      | none =>
          exact Or.inl (frame.include_rejected id _ found
            ((reactiveApplication_handle_of_tokenValid runtime leaks original.application _
              valid).trans leftHandled)
            ((reactiveApplication_handle_of_tokenValid runtime leaks repaired.application _
              valid).trans rightHandled))
      | some next =>
          exact Or.inr ⟨frame.repaired_only_opening_sender leftBinding id event candidate raw actor
            payload binding checks outputEq codeEq node next rightHandled leftHandled,
            frame.repaired_only_opening_breach onlyBindings sound leftBinding rightBinding id
              event candidate raw actor payload binding checks outputEq codeEq node evidence
                found next rightHandled leftHandled⟩

end Vegas.EventGraphRuntime.BindingMemory.Frame
