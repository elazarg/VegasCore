module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingRejectedInclusion
public import Vegas.Pending.ReactiveBindingFrameOpening
public import Vegas.Game.OnePacketPendingLumping

@[expose] public section

/-! # Complete opening-inclusion cases through a binding repair -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : (application setup timeouts leaks).Execution}

namespace EventGraphRuntime.BindingMemory.Frame

/-- At a ready disclosure whose original binding is successful, every actual
opening inclusion preserves the frame, including rejection. The successful
binding is unchanged by directed repair, so both native handlers accept the
same packets and execute the same public deferred-guard result. -/
theorem ready_opening_inclusion
    (frame : Frame timeouts leaks memory owner original repaired)
    (clear : original.application.config.defaulted = ∅)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (event : (graph setup).EventId) (actor : Player) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve actor payload binding checks)
    (node : nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (value : L.Val payload)
    (successful : binding.get? original.application.config.store = some (.success value))
    (id : MessageId Player) (candidate : Handle (graph setup)) (raw : Raw L)
    (evidence : Option (OpeningFact (graph setup)))
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩⟩)
    (endpointClear :
      (original.includePending (application setup timeouts leaks) id).application.config.defaulted =
        ∅) :
    let app := application setup timeouts leaks
    Frame timeouts leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have sameSuccess := EventGraph.Store.BindingRefines.success frame.successful binding value
    successful
  have sameBinding : binding.get? original.application.config.store =
      binding.get? repaired.application.config.store := successful.trans sameSuccess.symm
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
    exact ready
  cases handled : handle timeouts original.application
      ⟨id, .opening event candidate raw⟩ with
  | none =>
      have rightRejected : handle timeouts repaired.application
          ⟨id, .opening event candidate raw⟩ = none := by
        cases rightHandled : handle timeouts repaired.application
            ⟨id, .opening event candidate raw⟩ with
        | none => rfl
        | some next =>
            obtain ⟨previous, previousHandled, _⟩ := handle_opening_accepted_transfer (timeouts :=
              timeouts)
              repaired.application original.application frame.publicView.symm rightBinding
              leftBinding rightReady node sameBinding.symm id candidate raw rightHandled
            rw [handled] at previousHandled
            cases previousHandled
      exact frame.include_rejected id _ found
        (reactiveHandle_none (timeouts := timeouts) (leaks := leaks) handled)
        (reactiveHandle_none (timeouts := timeouts) (leaks := leaks) rightRejected)
  | some next =>
      obtain ⟨timely, sender, owned, associated, chosen, rawEq, stored⟩ :=
        handle_opening_accepted_facts (timeouts := timeouts) original.application next ready node id
          candidate raw handled
      subst raw
      have chosenEq : chosen = value := PublicationResult.success.inj
        (Option.some.inj (stored.symm.trans successful))
      subst chosen
      obtain ⟨rightStored, actual, firstAccepted, secondAccepted, _, leftFixed, rightFixed⟩ :=
        frame.successful_opening leftBinding rightBinding binding value successful
      have actualEq : actual = candidate := Option.some.inj (firstAccepted.symm.trans associated)
      subst actual
      have available : (EventGraph.EventCode.resolveOutput? binding checks true
          original.application.config.store).isSome = true := by
        apply EventGraph.EventCode.resolveOutput?_isSome
        intro field member
        apply original.application.config.read_available ready
        rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
        exact member
      obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
      exact frame.opening_inclusion clear onlyBindings id event candidate actor payload binding
        checks outputEq codeEq node ready timely sender owned associated value leftFixed rightFixed
        successful rightStored result resolved evidence found endpointClear

end EventGraphRuntime.BindingMemory.Frame

end Vegas
