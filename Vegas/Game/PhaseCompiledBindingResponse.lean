/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryCompiledPolicy
import Vegas.Game.PhaseSourcePolicyLaw
import Vegas.Pending.PhaseNativePlayerInput
import Vegas.Pending.ReactiveBinding

/-! # Complete physical binding laws of copied compiled source policies -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

omit [Fintype Player] in
private theorem lifted_binding_response (plan : RuntimePhasePlan (serviceGraph setup mode))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (acting : (toEventGraph setup.program).actor? event = some who) (serial : Nat)
    (graphAction : EventField.Action (outputLayout setup.program event)) :
    PhaseNativeProjection.action runtime leaks plan
        (phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding serial
          (CommitRecoveryMove.lift (decodeEventAction setup.program event graphAction))) =
      runtime.reactiveBinding (PhaseNativeProjection.nativeLeaks leaks plan) who event payload
        (cast (congrArg EventField.Action binding) graphAction) serial := by
  have owned := decodeEventAction_owner setup.program event graphAction
  rw [eventOwner?_eq_actor, acting] at owned
  obtain ⟨sourceAction, decoded, _owned⟩ := Option.map_eq_some_iff.mp owned
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program event graphAction
    sourceAction decoded
  simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, CommitRecoveryMove.lift,
    decoded, Option.map_some, Option.elim_some, Bool.false_eq_true, ↓reduceIte,
    Option.bind_some, encoded, Option.getD_some]
  rfl

private theorem binding_policy_selected (bounds : MessageBounds (serviceGraph setup mode))
    (wellFormed : setup.WellFormed) (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (supported : phaseBindingResponse runtime leaks who event payload result serial ∈
      (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding past view).support) :
    reactiveFreshSlot view.application.1 = some serial := by
  classical
  unfold phaseRecoveryBindingPolicy at supported
  split at supported
  · have impossible := (PMF.mem_support_pure_iff _ _).mp supported
    have transmitted := congrArg ReactiveApplication.Action.transmission impossible
    cases transmitted
  · rename_i allocated selected
    split at supported
    · obtain ⟨choice, _positive, same⟩ := PMF.support_map .. ▸ supported
      change phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding
        allocated choice.1 = phaseBindingResponse runtime leaks who event payload result serial
          at same
      unfold phaseRecoveryBindingResponse at same
      dsimp only at same
      split at same
      · have transmitted := congrArg ReactiveApplication.Action.transmission same
        cases transmitted
      · have named := congrArg (fun response => response.transmission.map
          (fun material => material.call.packet)) same
        change some (.commitment event (who, .prepared allocated) :
            Payload (serviceGraph setup mode)) =
          some (.commitment event (who, .prepared serial)) at named
        have candidate := (Payload.commitment.inj (Option.some.inj named)).2
        have equalSerial := Slot.prepared.inj (congrArg Prod.snd candidate)
        simpa only [equalSerial] using selected
    · have impossible := (PMF.mem_support_pure_iff _ _).mp supported
      have transmitted := congrArg ReactiveApplication.Action.transmission impossible
      cases transmitted

/-- At a genuine intended source input the entire actual unsent binding law,
including its derived fresh physical handle, is the compiled source response law.
The decoder correspondence is retained explicitly for the on-path invariant. -/
theorem phaseSourcePolicy_compiled_binding_of_history
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
       source assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (site : setup.intendedModel.InformationSite who)
    (original : setup.intendedModel.InformationHistory who site.1)
    (view : SourceProgram.ProtocolView who setup.program) (current : site.1 = some view)
    (decodedPhase : phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) = some view)
    (observation : (toEventGraph setup.program).PlayerObservation who)
    (decodedGraph : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      who event observation.store (decodeCompletions setup.program observation.ownActions) =
         some view)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) binding)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload binding codeEq) :
    let profile := setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.openingExtension source)
    let compiled := (compileEventPolicy setup.program who (profile who)) event
      (show (toEventGraph setup.program).actor? event = some who from request.2.2.2.1) observation
    ∃ serial, serial < horizon ∧
      reactiveFreshSlot (control.execution.application.current.native.playerView who) =
         some serial ∧
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
          (PhaseNativeProjection.action runtime leaks plan) =
        compiled.map (fun graphAction => runtime.reactiveDecision
          (PhaseNativeProjection.nativeLeaks leaks plan) who event graphAction
          (control.execution.application.current.native.playerView who)) := by
  classical
  intro profile compiled
  obtain ⟨actualView, serial, actualDecoded, bounded, actualLaw, _result⟩ :=
    phaseSourcePolicy_binding_of_history setup mode runtime leaks bounds wellFormed assessment who
      event payload binding (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon
      scheduler capacity control trace active request unsent values
  have equalView : actualView = view := Option.some.inj (actualDecoded.symm.trans decodedPhase)
  subst actualView
  have acting : (toEventGraph setup.program).actor? event = some who := request.2.2.2.1
  have sourceLaw := setup.commitRecovery_compiled_policy_raw_law wellFormed source
    assessment.strategy copies who site original view current event acting observation decodedGraph
  change (assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who (some view))).map Subtype.val =
    compiled.map (fun graphAction =>
      CommitRecoveryMove.lift (decodeEventAction setup.program event graphAction)) at sourceLaw
  let actual := phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
    (control.execution.recall who)
    (control.execution.observe (phaseApplication runtime leaks) who)
  have bindingLaw : actual.map (PhaseNativeProjection.action runtime leaks plan) =
      compiled.map (fun graphAction => runtime.reactiveBinding
        (PhaseNativeProjection.nativeLeaks leaks plan) who event payload
        (cast (congrArg EventField.Action binding) graphAction) serial) := by
    calc
      _ = ((assessment.strategy who
          (setup.commitRecoveryClearInformation wellFormed who (some view))).map Subtype.val).map
            (fun move => PhaseNativeProjection.action runtime leaks plan
              (phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding
                serial move)) := by
        dsimp only [actual]
        rw [actualLaw, PMF.map_comp, PMF.map_comp]
        rfl
      _ = _ := by
        rw [sourceLaw, PMF.map_comp]
        apply map_congr_on_support
        intro graphAction _supported
        exact lifted_binding_response setup mode runtime leaks plan who event payload binding acting
          serial graphAction
  obtain ⟨graphAction, positive⟩ := compiled.support_nonempty
  have selectedResponse : runtime.reactiveBinding
      (PhaseNativeProjection.nativeLeaks leaks plan) who event payload
      (cast (congrArg EventField.Action binding) graphAction) serial ∈
        (actual.map (PhaseNativeProjection.action runtime leaks plan)).support := by
    rw [bindingLaw]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨graphAction, positive, rfl⟩
  obtain ⟨response, supported, responseEq⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp selectedResponse
  have restored := congrArg (PhaseNativeProjection.liftAction runtime leaks plan) responseEq
  change response = phaseBindingResponse runtime leaks who event payload
    (cast (congrArg EventField.Action binding) graphAction) serial at restored
  subst response
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨_draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler raw
  have branch := phaseSourcePolicy_binding setup mode runtime leaks bounds wellFormed assessment
    control.execution valid who event payload binding request
  change phaseBindingResponse runtime leaks who event payload
    (cast (congrArg EventField.Action binding) graphAction) serial ∈
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).support at supported
  rw [branch] at supported
  have allocated := binding_policy_selected setup mode runtime leaks bounds wellFormed assessment
    who event payload binding (control.execution.recall who)
    (control.execution.observe (phaseApplication runtime leaks) who) _ serial supported
  refine ⟨serial, bounded, allocated, ?_⟩
  calc
    _ = _ := bindingLaw
    _ = _ := by
      apply congrArg (fun f => compiled.map f)
      funext graphAction
      exact (runtime.reactiveDecision_binding_eq (PhaseNativeProjection.nativeLeaks leaks plan)
        who who event payload binding codeEq node graphAction
        (control.execution.application.current.native.playerView who) serial allocated).symm

end Vegas
