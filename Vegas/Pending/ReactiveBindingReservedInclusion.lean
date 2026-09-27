/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingGuardedInclusion
import Vegas.Pending.ReactiveBindingFrameForeign
import Vegas.Pending.ReactiveServiceOpening
import Vegas.Pending.ReactiveSelectionObservation
import Vegas.Pending.ReactiveServicePublication
import Vegas.Pending.ReactiveBindingExpiry

/-! # Reserved inclusion derived from the actual conforming envelope

A selected certified opening supplies its true candidate value through the
network evidence invariant. Public phase checking then supplies readiness,
deadline and guard facts. The inclusion comparison does not assume acceptance
or a private-value test by the auditor. Foreign opaque bindings use their
unchanged actual candidate catalogue.
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

/-- The actual pending certificate and public checker discharge every handler
precondition. This includes the focal player's previously repaired bindings:
only an authentic original successful opening can enter this branch. -/
theorem conforming_opening_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (packet : WitnessedPacket graph)
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (permitted : runtime.freshServiceEnvelope original.application.publicView ⟨id, packet⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨candidate, raw, authored, owned, associated, _, shaped, guards⟩ :=
    runtime.freshServiceEnvelope_resolution_shape original.application.publicView actor event
      payload binding checks outputEq codeEq node granted ⟨id, packet⟩ permitted
  change packet = _ at shaped
  subst packet
  obtain ⟨_, ready, timely, _, _, _, _, _, _⟩ :=
    (runtime.freshServiceEnvelope_opening_iff original.application.publicView id event actor
      payload binding checks outputEq codeEq node candidate raw (some ⟨candidate, raw⟩)).mp
        permitted
  obtain ⟨value, rawEq, acceptedChecks⟩ :=
    (original.application.publicView.openingGuardsAccepted_iff actor event payload binding checks
      outputEq codeEq node candidate raw (some ⟨candidate, raw⟩)).mp guards
  subst raw
  have fixed : original.application.candidates.lookup candidate = .openable ⟨payload, value⟩ :=
    sound.lookup id _ found ⟨candidate, ⟨payload, value⟩⟩ (by
      change (⟨candidate, ⟨payload, value⟩⟩ : OpeningFact graph) ∈
        (some ⟨candidate, ⟨payload, value⟩⟩).toList
      exact List.mem_singleton_self _)
  have stored := leftBinding.opening_stored binding candidate value associated fixed
  obtain ⟨rightStored, actual, leftAssociated, _, _, _, rightFixed⟩ :=
    frame.successful_opening leftBinding rightBinding binding value stored
  cases Option.some.inj (leftAssociated.symm.trans associated)
  have checksAccepted : GuardCheck.allAccepted? checks original.application.config.store
      (.success value) = some true := by
    change GuardCheck.allAccepted? checks (graph.publicStore original.application.config.store)
      (.success value) = some true at acceptedChecks
    rwa [GuardCheck.allAccepted?_publicStore] at acceptedChecks
  have resolved : EventCode.resolveOutput? binding checks true original.application.config.store =
      some (.success value) := by
    simp only [EventCode.resolveOutput?, stored, Option.bind_eq_bind, Option.bind_some,
      ↓reduceIte, checksAccepted, Option.pure_def]
  exact frame.opening_inclusion onlyBindings id event candidate actor payload binding _ outputEq
    codeEq node ((original.application.publicView_eventReady event).mp ready) timely authored
    owned associated value fixed rightFixed stored rightStored (.success value) resolved
      (some ⟨candidate, ⟨payload, value⟩⟩) found

/-- A publicly conforming foreign binding fixes the same actual hidden
candidate on both sides. Its private opening is never checked by the audit. -/
theorem conforming_foreign_binding_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (id : MessageId Player) (event : graph.EventId) (actor : Player)
    (different : actor ≠ owner) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (fixed : original.application.candidates.lookup
      (actor, .prepared (original.application.publicView.bindingCount actor)) ≠ .fresh)
    (packet : WitnessedPacket graph)
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (permitted : runtime.freshServiceEnvelope original.application.publicView ⟨id, packet⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨authored, shaped⟩ := runtime.freshServiceEnvelope_binding_shape
    original.application.publicView actor event payload outputEq codeEq node granted
      ⟨id, packet⟩ permitted
  change packet = _ at shaped
  subst packet
  have includable := permitted.2.1
  simp only [PublicView.BindingIncludable, node,
    original.application.publicView_eventReady] at includable
  obtain ⟨ready, timely, _, _, vacant, unused⟩ := includable
  exact frame.foreign_binding_inclusion onlyBindings id event _ actor different payload
    outputEq codeEq node ready timely authored rfl vacant unused fixed none found

private theorem latest_step_frame
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (actor : Player)
    (inclusion : ∀ id packet, original.network.lookup id = some ⟨id, packet⟩ →
      id ∉ original.network.ledger.map Message.id →
      Frame runtime leaks memory owner
        { original.includePending (runtime.reactiveApplication leaks) id with
          environmentRecall := original.environmentRecall ++
            [⟨original.observeEnvironment (runtime.reactiveApplication leaks), .include id⟩] }
        { repaired.includePending (runtime.reactiveApplication leaks) id with
          environmentRecall := repaired.environmentRecall ++
            [⟨repaired.observeEnvironment (runtime.reactiveApplication leaks), .include id⟩] })
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftSupport : left ∈ (runtime.interactionStep leaks players network
      (.includeLatest event actor) original).support)
    (rightSupport : right ∈ (runtime.interactionStep leaks players network
      (.includeLatest event actor) repaired).support) :
    Frame runtime leaks memory owner left right := by
  let app := runtime.reactiveApplication leaks
  rw [runtime.interaction_includeLatest_environment leaks players network actor event original]
    at leftSupport
  rw [runtime.interaction_includeLatest_environment leaks players network actor event repaired,
    ← frame.environment] at rightSupport
  rcases runtime.reactiveLatest_wait_or_owned leaks event actor
      (original.observeEnvironment app) with waiting | ⟨id, _, selected⟩
  · rw [waiting] at leftSupport rightSupport
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at leftSupport rightSupport
    subst left
    subst right
    exact { frame with
      service := by
        change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
        rw [frame.service, frame.environment] }
  · have unpublished := runtime.reactiveLatest_fresh leaks event actor
      (original.observeEnvironment app) id selected
    rw [selected] at leftSupport rightSupport
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at leftSupport rightSupport
    subst left
    subst right
    cases found : original.network.lookup id with
    | none =>
        have rightFound : repaired.network.lookup id = none := frame.network ▸ found
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, rightFound]
        exact { frame with
          service := by
            change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
            rw [frame.service, frame.environment] }
    | some message =>
        have hit := List.find?_some found
        have identified : message.id = id := of_decide_eq_true hit
        rcases message with ⟨messageId, packet⟩
        change messageId = id at identified
        subst messageId
        exact inclusion id packet found unpublished

/-- Reserved resolution selection is compared in the actual runtime, including
the no-envelope branch. The pending-packet premise is a local state invariant;
packet authenticity derives acceptance after selection. -/
theorem resolution_reserved_step
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (permitted : ∀ message ∈ original.network.pending,
      runtime.permittedServiceEnvelope original.application.publicView original.network.ledger
        message = true)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftSupport : left ∈ (runtime.interactionStep leaks players network
      (.includeLatest event actor) original).support)
    (rightSupport : right ∈ (runtime.interactionStep leaks players network
      (.includeLatest event actor) repaired).support) :
    Frame runtime leaks memory owner left right := by
  apply frame.latest_step_frame players network event actor _ left right leftSupport rightSupport
  intro id packet found unpublished
  exact frame.conforming_opening_inclusion onlyBindings sound leftBinding rightBinding id event
    actor payload binding checks outputEq codeEq node granted packet found
      ((runtime.permittedServiceEnvelope_unpublished_iff _ _ _ unpublished).mp
        (permitted _ (List.mem_of_find?_eq_some found))).2

/-- The same reserved selector handles another player's mandatory binding.
All private data used here are operational catalogue facts, not audit inputs. -/
theorem foreign_binding_reserved_step
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (actor : Player) (different : actor ≠ owner) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (fixed : original.application.candidates.lookup
      (actor, .prepared (original.application.publicView.bindingCount actor)) ≠ .fresh)
    (permitted : ∀ message ∈ original.network.pending,
      runtime.permittedServiceEnvelope original.application.publicView original.network.ledger
        message = true)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftSupport : left ∈ (runtime.interactionStep leaks players network
      (.includeLatest event actor) original).support)
    (rightSupport : right ∈ (runtime.interactionStep leaks players network
      (.includeLatest event actor) repaired).support) :
    Frame runtime leaks memory owner left right := by
  apply frame.latest_step_frame players network event actor _ left right leftSupport rightSupport
  intro id packet found unpublished
  exact frame.conforming_foreign_binding_inclusion onlyBindings id event actor different payload
    outputEq codeEq node granted fixed packet found
      ((runtime.permittedServiceEnvelope_unpublished_iff _ _ _ unpublished).mp
        (permitted _ (List.mem_of_find?_eq_some found))).2

/-- The complete guarded-resolution suffix uses the actual reserved selector,
then all clock padding and expiry. Legal withholding is included: its pending
selection can wait, and expiry supplies the common failure result. -/
theorem resolution_reserved_tail_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (permitted : ∀ message ∈ original.network.pending,
      runtime.permittedServiceEnvelope original.application.publicView original.network.ledger
        message = true) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    let tail := .includeLatest event actor :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : FinDist (app.Execution × app.Execution),
      coupling.map Prod.fst = runtime.runInteractionPlan leaks players network tail original ∧
      coupling.map Prod.snd = runtime.runInteractionPlan leaks players network tail repaired ∧
      ∀ next ∈ coupling.support, Frame runtime leaks memory owner next.1 next.2 := by
  intro app tail
  let left := runtime.runInteractionPlan leaks players network tail original
  let right := runtime.runInteractionPlan leaks players network tail repaired
  refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
    FinDist.map_snd_product .., ?_⟩
  intro next supported
  have first : next.1 ∈ left.support := by
    rw [← FinDist.map_fst_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  have second : next.2 ∈ right.support := by
    rw [← FinDist.map_snd_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  obtain ⟨leftIncluded, leftStep, leftTail⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ first)
  obtain ⟨rightIncluded, rightStep, rightTail⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ second)
  have paired := frame.resolution_reserved_step onlyBindings sound leftBinding rightBinding
    players network event actor payload binding checks outputEq codeEq node granted permitted
      leftIncluded rightIncluded leftStep rightStep
  have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
  exact paired.clock_tail_unmodified players network event
    (onlyBindings.public_value_none (.inr event) visible)
    (onlyBindings.public_action_none event visible) ticks next.1 next.2 leftTail rightTail

/-- A foreign binding and its deadline tail preserve the complete frame.
The fixed candidate fact is operational; it is never exposed to the auditor. -/
theorem foreign_binding_reserved_tail_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (actor : Player) (different : actor ≠ owner) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (fixed : original.application.candidates.lookup
      (actor, .prepared (original.application.publicView.bindingCount actor)) ≠ .fresh)
    (permitted : ∀ message ∈ original.network.pending,
      runtime.permittedServiceEnvelope original.application.publicView original.network.ledger
        message = true) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    let tail := .includeLatest event actor :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : FinDist (app.Execution × app.Execution),
      coupling.map Prod.fst = runtime.runInteractionPlan leaks players network tail original ∧
      coupling.map Prod.snd = runtime.runInteractionPlan leaks players network tail repaired ∧
      ∀ next ∈ coupling.support, Frame runtime leaks memory owner next.1 next.2 := by
  intro app tail
  let left := runtime.runInteractionPlan leaks players network tail original
  let right := runtime.runInteractionPlan leaks players network tail repaired
  refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
    FinDist.map_snd_product .., ?_⟩
  intro next supported
  have first : next.1 ∈ left.support := by
    rw [← FinDist.map_fst_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  have second : next.2 ∈ right.support := by
    rw [← FinDist.map_snd_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  obtain ⟨leftIncluded, leftStep, leftTail⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ first)
  obtain ⟨rightIncluded, rightStep, rightTail⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ second)
  have paired := frame.foreign_binding_reserved_step onlyBindings players network event actor
    different payload outputEq codeEq node granted fixed permitted
      leftIncluded rightIncluded leftStep rightStep
  have noValue : memory.shadow.values (.inr event) = none := by
    cases stored : memory.shadow.values (.inr event) with
    | none => rfl
    | some value =>
        obtain ⟨selected, _, same, binding⟩ :=
          onlyBindings.1 (.inr event) (by simp only [stored]; rfl)
        cases Sum.inr.inj same
        rw [outputEq] at binding
        exact (different (EventField.binding.inj binding).1).elim
  have noAction : memory.shadow.actions event = none := by
    cases stored : memory.shadow.actions event with
    | none => rfl
    | some action =>
        obtain ⟨_, binding⟩ := onlyBindings.2 event (by simp only [stored]; rfl)
        rw [outputEq] at binding
        exact (different (EventField.binding.inj binding).1).elim
  exact paired.clock_tail_unmodified players network event noValue noAction ticks
    next.1 next.2 leftTail rightTail

end Vegas.EventGraphRuntime.BindingMemory.Frame
