/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.RevealService
import Vegas.Game.PhaseProposalGeneratedPreparation
import Vegas.Pending.PhaseLatestBindingHistory
import Vegas.Pending.PhaseRecordedBindingMaterial
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.EventGraph.PrivateInputs
import Vegas.Source.IntendedGame
import Vegas.Source.CommitRecoveryAttemptReadout
import Interaction.ReactiveRecallEntries

/-! # Usable source cells on actual histories without unusable preparations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem phaseProposal_recalled_binding_preparation_value
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control))
    (owner : Player)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial
      horizon scheduler owner ⟨some control, trace⟩)
    (event : graph.EventId) (payload : L.Ty)
    (typed : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩) :
    ∃ value : L.Val payload, opening.bind (fun raw => raw.as? payload) = some value := by
  classical
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | some value => exact ⟨value, rfl⟩
  | none =>
      apply False.elim
      apply good
      let app := phaseApplication runtime leaks
      let menu := PhaseCount.onePacketMenu runtime leaks bounds
      obtain ⟨index, inside, rfl⟩ := List.getElem_of_mem recorded
      have present := app.recallOwnPlay_entry_mem (control.execution.recall owner) index inside
      have word : (menu.information initial horizon scheduler).ownPlay owner trace =
          app.recallOwnPlay (control.execution.recall owner) := by
        change (menu.signals initial horizon scheduler).ownPlay owner trace = _
        rw [← menu.ownPlay_toRawTrace initial horizon scheduler owner trace, app.trace_ownPlay]
        rfl
      refine ⟨_, word.symm ▸ present, event, payload, serial, opening, evidence, typed, ?_, decoded⟩
      exact declared

private theorem saved_binding_result_value
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler owner ⟨some control, trace⟩)
    (event : graph.EventId) (payload : L.Ty)
    (typed : graph.outputLayout event = .binding owner payload)
    (candidate : Handle graph)
    (accepted : control.execution.application.entry.native.accepted (.inr event) =
      some candidate) :
    ∃ value : L.Val payload,
      control.execution.application.entry.native.bindingResult candidate payload =
        .success value := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs
    horizon scheduler trace
  let raw := menu.toRawTrace initial horizon scheduler trace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have owned : candidate.1 = owner := by
    obtain ⟨otherPayload, layout⟩ := bindings.saved.accepted_typed (.inr event) candidate accepted
    exact (EventField.binding.inj (layout.symm.trans typed)).1
  obtain ⟨message, member, sender, call, _latest⟩ := physical.saved event candidate accepted
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
    (physical.clean.2 message member)).2.1
  change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
  simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
  obtain ⟨_bindingOwned, _noEvidence, _candidateOwner, ⟨serial, slot⟩, _unused⟩ := correct
  have candidateEq : candidate = (owner, .prepared serial) := Prod.ext owned slot
  subst candidate
  have senderEq : message.sender = owner := sender
  obtain ⟨entry, recorded, material, sent, _emitted, state, known, emission⟩ :=
    physical.origins.inputs message member
  rw [senderEq] at recorded
  have materialCall : material.call.packet = .commitment event (owner, .prepared serial) := by
    calc
      material.call.packet = (state.emit message.sender known material).packet.call :=
        (phase_emit_call state message.sender known material).symm
      _ = message.payload.packet.call :=
        congrArg (fun packet : CommitAttemptPacket graph => packet.packet.call) emission
      _ = .commitment event (owner, .prepared serial) := call
  rcases material with ⟨⟨packet, opening⟩, evidence⟩
  dsimp only at materialCall
  subst packet
  have declared : entry.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :=
    congrArg (fun transmission => (⟨transmission⟩ : app.Action)) sent
  obtain ⟨value, decoded⟩ := phaseProposal_recalled_binding_preparation_value runtime leaks bounds
    initial horizon scheduler control trace owner good event payload typed serial opening evidence
      entry recorded declared
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler control trace owner entry recorded
  rw [declared] at offered
  have fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon
      scheduler prior owner event serial opening evidence offered
  have meaning := phase_recorded_material_binding_result runtime leaks menu initial horizon
    scheduler control trace owner event payload serial opening evidence entry recorded declared
      fresh
  rw [decoded, Option.elim_some] at meaning
  have fixed := bindings.fixed (owner, .prepared serial)
    (bindings.saved.accepted_fixed (.inr event) (owner, .prepared serial) accepted)
  refine ⟨value, ?_⟩
  unfold EventGraphRuntime.State.bindingResult at meaning ⊢
  rwa [fixed] at meaning

omit [DecidableEq Player] [Fintype Player] in
private theorem stored_binding_available
    {graph : Vegas.EventGraph Player L} {kind : EventField Player L}
    (ref : FieldRef graph.layout kind)
    (store : Store graph.layout) (value : kind.Value)
    (stored : ref.get? store = some value) : (store ref.field).isSome = true := by
  cases ref with
  | mk field layout =>
      cases layout
      exact congrArg Option.isSome stored

omit [Fintype Player] in
private theorem input_binding_value
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (wellFormed : setup.WellFormed)
    (draw : State L setup.context) (supported : draw ∈ setup.initialLaw.support)
    (store : Store (serviceGraph setup mode).layout)
    (inputs : ∀ input, store (.inl input) = some (encodeInputs draw input))
    (owner : Player) (payload : L.Ty)
    (ref : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (input : (serviceGraph setup mode).InputId) (field : ref.field = .inl input) :
    ∃ value : L.Val payload, ref.get? store = some (.success value) := by
  obtain ⟨name, kind, selected, selectedField⟩ :=
    (ContextRefs.initial_coversPrefix setup.program).1 input
  have layout : cellField kind = .binding owner payload := by
    have original := ((ContextRefs.initial setup.context (outputLayout setup.program)).get
      selected).layout_eq
    rw [selectedField] at original
    change inputLayout setup.context input = cellField kind at original
    have actual := ref.layout_eq
    rw [field] at actual
    change inputLayout setup.context input = .binding owner payload at actual
    exact original.symm.trans actual
  cases kind with
  | publicData ty => cases layout
  | privateInput actor ty => cases layout
  | publication ty => cases layout
  | commitment actor ty =>
      cases layout
      have same : ref =
          (ContextRefs.initial setup.context (outputLayout setup.program)).get selected := by
        cases ref with
        | mk actual actualLayout =>
            cases chosen : (ContextRefs.initial setup.context (outputLayout setup.program)).get
                selected with
            | mk other otherLayout =>
                have fields : actual = other := by
                  rw [chosen] at selectedField
                  exact field.trans selectedField.symm
                subst other
                rfl
      obtain ⟨value, successful⟩ := wellFormed.initialValues draw supported selected
      refine ⟨value, ?_⟩
      rw [same]
      simpa only [successful, cellValue] using
        (ContextRefs.initial_agrees (outputLayout setup.program) draw store inputs selected)

/-- On an actual initialized counted history, every surviving source binding
is usable when its owner has generated no unusable preparation. Saved cells use
their authentic immutable preparation; initial cells use the original supported
setup draw. Guard acceptance is unrestricted. -/
theorem RecoverySourceCheckpoint.bindingsHoldValues_of_no_generated_unusable
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (wellFormed : setup.WellFormed)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (owner : Player) (surviving : owner ∉ control.execution.application.current.excluded)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler owner ⟨some control, trace⟩) :
    checkpoint.source.BindingsHoldValues owner := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  have original : ∃ draw ∈ setup.initialLaw.support,
      control.execution.application.Invariant (encodeInputs draw) := by
    have invariant : app.Invariant (fun state => ∃ draw ∈ setup.initialLaw.support,
        state.Invariant (encodeInputs draw)) := by
      constructor
      · intro state owner material valid
        obtain ⟨draw, supported, native⟩ := valid
        exact ⟨draw, supported,
          (phaseApplication_invariant runtime leaks (encodeInputs draw)).submit
            state owner material native⟩
      · intro state message next valid handled
        obtain ⟨draw, supported, native⟩ := valid
        exact ⟨draw, supported,
          (phaseApplication_invariant runtime leaks (encodeInputs draw)).handle
            state message next native handled⟩
      · intro state command next valid reached
        obtain ⟨draw, supported, native⟩ := valid
        exact ⟨draw, supported,
          (phaseApplication_invariant runtime leaks (encodeInputs draw)).environment
            state command next native reached⟩
    apply invariant.history initial horizon scheduler ?_ raw
    intro state reached
    obtain ⟨input, selected, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨draw, supported, rfl⟩ := PMF.support_map .. ▸ selected
    exact ⟨draw, supported, (PhaseRuntimeState.initial_invariant plan (encodeInputs draw)).1⟩
  obtain ⟨draw, supported, native⟩ := original
  have bindings := phaseBindingRecord_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon scheduler raw
  have coverage := phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler raw
  intro name payload selected
  let ref : FieldRef (serviceGraph setup mode).layout (.binding owner payload) :=
    checkpoint.refs.get selected
  have stored : ref.get? control.execution.application.entry.native.config.store =
      some (checkpoint.source.state.get selected) := checkpoint.agrees selected
  cases field : ref.field with
  | inl input =>
      obtain ⟨value, successful⟩ := input_binding_value setup mode wellFormed draw supported
        control.execution.application.entry.native.config.store
        (fun input => by
          rw [EventGraph.Config.store_input, native.saved.reachable.inputs_eq])
        owner payload ref input field
      exact ⟨value, Option.some.inj (stored.symm.trans successful)⟩
  | inr event =>
      have typed : (serviceGraph setup mode).outputLayout event = .binding owner payload := by
        have actual := ref.layout_eq
        rw [field] at actual
        exact actual
      have completed : event ∈ control.execution.application.entry.native.config.cut.completed := by
        apply (control.execution.application.entry.native.config.output_available event).mp
        have available := stored_binding_available ref _ _ stored
        rw [field] at available
        exact available
      cases accepted : control.execution.application.entry.native.accepted (.inr event) with
      | none =>
          have failed := (control.execution.application.entry.native.publicView_missedBinding
            event owner payload typed).mpr ⟨completed, accepted⟩
          exact (surviving (coverage.inherited (coverage.saved.covered event owner
            (actor?_of_outputLayout_binding _ typed) (Or.inl failed)))).elim
      | some candidate =>
          obtain ⟨value, successful⟩ := saved_binding_result_value runtime leaks bounds plan
            (setup.initialLaw.map encodeInputs) horizon scheduler control trace owner
              good event payload typed candidate accepted
          refine ⟨value, ?_⟩
          have meaning := bindings.saved.binding_value ref (checkpoint.source.state.get selected)
            stored
          simpa only [field, accepted, Option.elim_some, successful] using meaning

/-- Foreign history cleanliness and the focal player's actual saved live
typed reads discharge the ordinary gate at the same checkpoint. Canceled old
focal preparations are unrestricted; no source usability premise is supplied. -/
theorem RecoverySourceCheckpoint.bindingsHoldValues_of_foreign_good_and_own_live
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (wellFormed : setup.WellFormed)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (focal : Player)
    (ownLive : ∀ {payload : L.Ty}
      (ref : FieldRef (serviceGraph setup mode).layout (.binding focal payload)),
      ref.get? control.execution.application.entry.native.config.store ≠ some .failure)
    (foreign : ∀ owner, owner ≠ focal →
      owner ∉ control.execution.application.current.excluded →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler owner ⟨some control, trace⟩) :
    ∀ owner, owner ∉ control.execution.application.current.excluded →
      checkpoint.source.BindingsHoldValues owner := by
  intro owner surviving name payload selected
  by_cases same : owner = focal
  · subst owner
    cases result : checkpoint.source.state.get selected with
    | success value => exact ⟨value, rfl⟩
    | failure =>
        exact (ownLive (checkpoint.refs.get selected)
          (by simpa only [result, cellValue] using checkpoint.agrees selected)).elim
  · exact checkpoint.bindingsHoldValues_of_no_generated_unusable setup mode wellFormed
      runtime leaks bounds plan horizon scheduler control trace owner surviving
        (foreign owner same surviving) selected

end Vegas
