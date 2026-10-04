/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.BindingCapabilityReadout
import Vegas.Pending.ReactiveBindingFrameForeign

/-! # Failure-preserving private commitment reconstruction

Replacing unusable private opening material by canonical failure preserves the
opaque packet and actual typed binding result. The owner's private memory
records its original candidate and response, without overriding typed values
or completed actions. The concrete frame is constructed at transmission and
preserved by actual accepted inclusion.

These are operational submission and inclusion results. They do not establish
closure under every subsequent raw response, a consistent behavioral strategy
for the repair, or an equilibrium comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace BindingMemory

/-- Save the original owned candidate and response using only the owner's
reconstructed current input. The replacement sends the same handle without
opening material; no typed store value or completion action is remembered. -/
def rememberCapabilitySubmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (memory : BindingMemory runtime leaks) (owner : Player)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L)) :
    BindingMemory runtime leaks :=
  let input := memory.shadow.inputView runtime leaks view
  let call : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  ⟨memory.shadow.rememberCandidate (.prepared serial)
      (call.candidateAfter owner input.application.candidates (.prepared serial)),
    memory.responses ++ [(input, ⟨some ⟨call, .none⟩⟩)]⟩

namespace Frame

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The actual pending response frame is constructed from the previous frame
and owner-local candidate memory. Inclusion, freshness, and a typed result
are not presumed at transmission. -/
theorem capability_submission
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    let remembered := memory.rememberCapabilitySubmission runtime leaks owner
      (repaired.observe app owner) event serial opening
    Frame runtime leaks remembered owner
      (original.respond app owner
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩)
      (repaired.respond app owner
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), none⟩, .none⟩⟩) := by
  let app := runtime.reactiveApplication leaks
  let originalCall : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  let repairedCall : Submission graph := ⟨.commitment event (owner, .prepared serial), none⟩
  let remembered := memory.rememberCapabilitySubmission runtime leaks owner
    (repaired.observe app owner) event serial opening
  let left := original.respond app owner ⟨some ⟨originalCall, .none⟩⟩
  let right := repaired.respond app owner ⟨some ⟨repairedCall, .none⟩⟩
  have paired := runtime.rawBinding_submit_hidden_congr leaks original repaired owner
    frame.network frame.receipts frame.publicView frame.views frame.recall event serial opening none
  change left.network = right.network ∧ left.receipts = right.receipts ∧
    left.application.publicView = right.application.publicView ∧
    (∀ who, who ≠ owner → left.application.playerView who = right.application.playerView who) ∧
    (∀ who, who ≠ owner → left.recall who = right.recall who) at paired
  have packet : (⟨originalCall, .none⟩ : WitnessedSubmission graph).emit
      (app.submit original.application owner ⟨originalCall, .none⟩) owner
        (original.network.known owner) =
      (⟨repairedCall, .none⟩ : WitnessedSubmission graph).emit
        (app.submit repaired.application owner ⟨repairedCall, .none⟩) owner
          (repaired.network.known owner) := by
    change WitnessedPacket.mk originalCall.packet none
        ((app.submit original.application owner ⟨originalCall, .none⟩).publicView.tokenFor
          originalCall.packet) =
      WitnessedPacket.mk repairedCall.packet none
        ((app.submit repaired.application owner ⟨repairedCall, .none⟩).publicView.tokenFor
          repairedCall.packet)
    rw [reactiveApplication_submit_publicView, reactiveApplication_submit_publicView,
      frame.publicView]
  have restored := memory.restoreRecall_submit runtime leaks original repaired owner
    ⟨originalCall, .none⟩ ⟨repairedCall, .none⟩ frame.lengths frame.past frame.observed
      frame.network packet
  have catalog := memory.shadow.rememberCandidate_submit_view runtime leaks
    original.application repaired.application owner
      (congrArg ReactiveApplication.PlayerView.application frame.observed) event serial opening none
  change remembered.shadow.view (app.observePlayer right.application owner) =
    app.observePlayer left.application owner at catalog
  change Frame runtime leaks remembered owner left right
  refine ⟨restored, ?_, ?_, paired.1, frame.service, paired.2.2.2.1, paired.2.2.2.2,
    ?_, ?_, ?_⟩
  · change (⟨right.network.observe owner,
      remembered.shadow.view (app.observePlayer right.application owner), right.receipts⟩ :
        app.PlayerView) =
      ⟨left.network.observe owner, app.observePlayer left.application owner, left.receipts⟩
    rw [catalog, ← paired.1, ← paired.2.1]
  · change (right.recall owner).length = remembered.responses.length
    simp only [right, remembered, rememberCapabilitySubmission,
      ReactiveApplication.Execution.respond, ↓reduceIte, List.length_append,
      List.length_singleton, frame.lengths]
  · intro query
    exact (runtime.submitted_binding_fresh_iff leaks original owner event serial opening
      query).trans ((and_congr Iff.rfl (frame.slots query)).trans
        (runtime.submitted_binding_fresh_iff leaks repaired owner event serial none query).symm)
  · change left.application.config.store.BindingRefines right.application.config.store
    rw [(runtime.reactive_respond_application leaks original owner _).1,
      (runtime.reactive_respond_application leaks repaired owner _).1]
    exact frame.successful
  · change runtime.submissionRecall leaks ((original.respond app owner _).recall owner) =
      runtime.submissionRecall leaks ((repaired.respond app owner _).recall owner)
    rw [runtime.submissionRecall_respond, runtime.submissionRecall_respond, frame.submissions]
    rfl

end Frame
end BindingMemory

end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Actual reserved acceptance of unusable material has the same typed config
and receipt as canonical failure at the counted handle. The private frame and
its candidate-only memory are constructed, rather than assumed. No prior
traffic is erased and no clean-audit premise is required. -/
theorem bindingCapability_reserved_failure
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (initial : (application setup leaks).Execution) (opening : Option (Raw L))
    (decoded : opening.bind (fun raw => raw.as? payload) = none)
    (ready : initial.application.config.cut.Ready event)
    (timely : initial.application.WithinDeadline (runtime setup) event)
    (fresh : initial.application.candidates.lookup
      (owner, .prepared (initial.application.publicView.bindingCount owner)) = .fresh)
    (vacant : initial.application.accepted (.inr event) = none)
    (unused : initial.application.HandleUnused
      (owner, .prepared (initial.application.publicView.bindingCount owner)))
    (serials : initial.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) :
    let app := application setup leaks
    let serial := initial.application.publicView.bindingCount owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    ∃ memory : BindingMemory (runtime setup) leaks,
      ∃ original repaired : app.Execution,
        (runtime setup).interactionStep leaks players network (.includeLatest event owner)
            (initial.respond app owner response) = PMF.pure original ∧
          (runtime setup).interactionStep leaks players network (.includeLatest event owner)
            (initial.respond app owner
              ((runtime setup).reactiveBinding leaks owner event payload .failure serial)) =
            PMF.pure repaired ∧
          memory.Frame (runtime setup) leaks owner original repaired ∧
          (∀ field, memory.shadow.values field = none) ∧
          (∀ query, memory.shadow.actions query = none) ∧
          (original.application.config, original.receipts) =
            (initial.application.config.complete event ready
              (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure)
              (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure),
                initial.receipts ++ [((owner, initial.network.nextSerial owner), true)]) ∧
          (repaired.application.config, repaired.receipts) =
            (original.application.config, original.receipts) := by
  let app := application setup leaks
  let serial := initial.application.publicView.bindingCount owner
  let rawCall : Submission (graph setup) :=
    ⟨.commitment event (owner, .prepared serial), opening⟩
  let failureCall : Submission (graph setup) :=
    ⟨.commitment event (owner, .prepared serial), none⟩
  let left := initial.respond app owner ⟨some ⟨rawCall, .none⟩⟩
  let right := initial.respond app owner ⟨some ⟨failureCall, .none⟩⟩
  let memory := BindingMemory.rememberCapabilitySubmission (runtime setup) leaks
    (BindingMemory.atRecall (runtime setup) leaks (initial.recall owner)) owner
      (initial.observe app owner) event serial opening
  let id : MessageId Player := (owner, initial.network.nextSerial owner)
  let original : app.Execution := { left.includePending app id with
    environmentRecall := left.environmentRecall ++ [⟨left.observeEnvironment app, .include id⟩] }
  let repaired : app.Execution := { right.includePending app id with
    environmentRecall := right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩] }
  have pending := BindingMemory.Frame.capability_submission
    (BindingMemory.frame_atRecall (runtime setup) leaks owner initial) event serial opening
  change BindingMemory.Frame (runtime setup) leaks memory owner left right at pending
  have noValues : ∀ field, memory.shadow.values field = none := fun _ => rfl
  have noActions : ∀ query, memory.shadow.actions query = none := fun _ => rfl
  have leftConfig : left.application.config = initial.application.config :=
    ((runtime setup).reactive_respond_application leaks initial owner _).1
  have leftPublic : left.application.publicView = initial.application.publicView :=
    ((runtime setup).reactive_respond_application leaks initial owner _).2
  have leftReady : left.application.config.cut.Ready event := by rwa [leftConfig]
  have leftTimely : left.application.WithinDeadline (runtime setup) event := by
    unfold EventGraphRuntime.State.WithinDeadline
    rw [show left.application.clock = initial.application.clock from
      congrArg PublicView.clock leftPublic,
      show left.application.activatedAt = initial.application.activatedAt from
        congrArg PublicView.activatedAt leftPublic]
    exact timely
  have accepted : left.application.accepted = initial.application.accepted :=
    congrArg PublicView.accepted leftPublic
  have leftVacant : left.application.accepted (.inr event) = none := by rw [accepted, vacant]
  have leftUnused : left.application.HandleUnused (owner, .prepared serial) := by
    intro field associated
    exact unused field ((congrFun accepted field).symm.trans associated)
  have found : left.network.lookup id = some
      ⟨id, ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩⟩ :=
    respond_submit_lookup_of_ready (runtime setup) leaks initial owner rawCall serials event rfl
      ready
  have leftResult := (runtime setup).submitted_bindingResult leaks initial owner event payload
    serial opening fresh
  have rightResult := (runtime setup).submitted_bindingResult leaks initial owner event payload
    serial none fresh
  change left.application.bindingResult (owner, .prepared serial) payload = _ at leftResult
  change right.application.bindingResult (owner, .prepared serial) payload = _ at rightResult
  simp only [decoded, Option.elim_none] at leftResult
  simp only [Option.bind_none, Option.elim_none] at rightResult
  have framed := pending.binding_inclusion_unmodified id event (owner, .prepared serial) owner
    payload outputEq codeEq node leftReady leftTimely rfl rfl leftVacant leftUnused
    (submitStep_commitment_fixed _ owner event (.prepared serial))
    (submitStep_commitment_fixed _ owner event (.prepared serial))
    (rightResult.trans leftResult.symm) (noValues _) (noActions _) none found
  change BindingMemory.Frame (runtime setup) leaks memory owner original repaired at framed
  have leftStep : (runtime setup).interactionStep leaks players network
      (.includeLatest event owner) left = PMF.pure original := by
    rw [(runtime setup).rawBinding_reserved_selection leaks initial owner event serial opening
      serials players network]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have rightStep : (runtime setup).interactionStep leaks players network
      (.includeLatest event owner) right = PMF.pure repaired := by
    rw [(runtime setup).rawBinding_reserved_selection leaks initial owner event serial none
      serials players network]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have leftLaw := (runtime setup).rawBinding_reserved_config leaks initial owner event payload
    outputEq codeEq node serial opening ready timely fresh vacant unused serials players network
  change ((runtime setup).interactionStep leaks players network (.includeLatest event owner)
    left).map _ = _ at leftLaw
  rw [leftStep, PMF.pure_map] at leftLaw
  simp only [decoded, Option.elim_none] at leftLaw
  have rightLaw := (runtime setup).rawBinding_reserved_config leaks initial owner event payload
    outputEq codeEq node serial none ready timely fresh vacant unused serials players network
  change ((runtime setup).interactionStep leaks players network (.includeLatest event owner)
    right).map _ = _ at rightLaw
  rw [rightStep, PMF.pure_map] at rightLaw
  simp only [Option.bind_none, Option.elim_none] at rightLaw
  have leftEq := (PMF.mem_support_pure_iff _ _).mp
    (leftLaw ▸ (PMF.mem_support_pure_iff _ _).mpr rfl)
  have rightEq := (PMF.mem_support_pure_iff _ _).mp
    (rightLaw ▸ (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact ⟨memory, original, repaired, leftStep, rightStep, framed, noValues, noActions, leftEq,
    rightEq.trans leftEq.symm⟩

/-- The two actual inclusion laws have equal joint full typed source readout
and realized audit payoff vector. Utility may inspect every terminal source
cell; prior offenses and correlated audit randomness are retained. The
inclusion endpoints need not complete the whole source program. -/
theorem bindingCapability_reserved_joint_audit_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (initial : (application setup leaks).Execution) (opening : Option (Raw L))
    (decoded : opening.bind (fun raw => raw.as? payload) = none)
    (ready : initial.application.config.cut.Ready event)
    (timely : initial.application.WithinDeadline (runtime setup) event)
    (fresh : initial.application.candidates.lookup
      (owner, .prepared (initial.application.publicView.bindingCount owner)) = .fresh)
    (vacant : initial.application.accepted (.inr event) = none)
    (unused : initial.application.HandleUnused
      (owner, .prepared (initial.application.publicView.bindingCount owner)))
    (serials : initial.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (trafficAudit : SettledRecord (graph setup) →
      List (application setup leaks).TrafficRecord → PMF (Player → Bool))
    (deposit : Player → ℝ) :
    let app := application setup leaks
    let serial := initial.application.publicView.bindingCount owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let settle := GameTheory.Enforcement.TerminalAudit.settlement
      (baseUtility setup leaks utility) ((runtime setup).serviceAuditObservation leaks)
      ((runtime setup).serviceAudit leaks trafficAudit) deposit
    (((runtime setup).interactionStep leaks players network (.includeLatest event owner)
      (initial.respond app owner response)).bind fun final =>
        (settle (some ⟨0, none, final⟩)).map (fun payoffs =>
          (sourceReadout setup leaks (some ⟨0, none, final⟩), payoffs))) =
      (((runtime setup).interactionStep leaks players network (.includeLatest event owner)
        (initial.respond app owner
          ((runtime setup).reactiveBinding leaks owner event payload .failure serial))).bind
        fun final => (settle (some ⟨0, none, final⟩)).map (fun payoffs =>
          (sourceReadout setup leaks (some ⟨0, none, final⟩), payoffs))) := by
  dsimp only
  obtain ⟨memory, original, repaired, left, right, frame, noValues, _, _, _⟩ :=
    bindingCapability_reserved_failure setup leaks owner event payload outputEq codeEq node initial
      opening decoded ready timely fresh vacant unused serials players network
  rw [left, right, PMF.pure_bind, PMF.pure_bind]
  have readout := bindingCapabilityFrame_sourceReadout setup leaks owner memory
    ⟨0, none, original⟩ ⟨0, none, repaired⟩ frame noValues
  have settlement := (bindingCapabilityFrame_auditedSettlement setup leaks utility trafficAudit
    deposit owner memory ⟨0, none, original⟩ ⟨0, none, repaired⟩ frame noValues).2
  rw [readout, settlement]

end Vegas
