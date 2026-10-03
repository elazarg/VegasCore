/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMissingResponseClassification
import Vegas.Pending.ReactiveBindingSubmissionFrame
import Vegas.Pending.ReactiveBindingPendingExpiry

/-! # The actual uncharged binding default across submission and inclusion

The excluded original response is an arbitrary full effective choice whose
classified private material is absent or mistyped. A clear repaired risk-menu
history determines its fresh counted handle and protected public acceptance.
The retained implementation selects its actual typed default, while the same
private memory reconstructs the original candidate, failed binding and recall.

This is the response and immediate inclusion branch of the existing frame.
It neither requires original risk-menu support nor preserves every later
certificate capability of mistyped raw material.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The actual retained typed default preserves the full frame at transmission
and at immediate inclusion of the newly allocated packet. All acceptance and
candidate resources follow from the two real histories and the classified
original response; no future original menu-support premise is used. -/
theorem sourceServiceMissing_unusable_default_frame
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (completedMemory : memory.shadow.CompletedAt original.application.config)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨rightRemaining, some who, repaired⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (unusable : unusableServiceBindingResponse setup leaks who (repaired.recall who)
      (repaired.observe (application setup leaks) who) response) :
    let app := application setup leaks
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let input := (repaired.recall who, repaired.observe app who)
    let selected := BindingMemory.retainedResponse (runtime setup) leaks menu who memory
      input response
    let remembered : BindingMemory (runtime setup) leaks :=
      ⟨selected.2, memory.responses ++ [(memory.shadow.inputView (runtime setup) leaks
        input.2, response)]⟩
    let left := original.respond app who response
    let right := repaired.respond app who selected.1
    let id := (who, original.network.nextSerial who)
    remembered.Frame (runtime setup) leaks who left right ∧
      remembered.shadow.OwnBindings who ∧
      remembered.Frame (runtime setup) leaks who
        { left.includePending app id with environmentRecall := left.environmentRecall ++
          [⟨left.observeEnvironment app, .include id⟩] }
        { right.includePending app id with environmentRecall := right.environmentRecall ++
          [⟨right.observeEnvironment app, .include id⟩] } ∧
      remembered.shadow.CompletedAt (left.includePending app id).application.config := by
  let app := application setup leaks
  let view := repaired.observe app who
  have chosen := sourceServiceMissing_unusable_default_retained bounds bound values original
    repaired who memory frame rightTrace clear response effective unusable
  obtain ⟨event, payload, outputEq, codeEq, node, turn, unrecorded, opening, responseEq,
    missing⟩ := unusable
  let serial := repaired.application.publicView.bindingCount who
  have persistent := ((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  have rightFresh := riskCanonicalSlot_fresh_at_turn bounds bound _ rightTrace who persistent
    event turn unrecorded
  have fresh := (frame.slots (.prepared serial)).mpr rightFresh
  have rightReady := (repaired.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec repaired.application.publicView who event turn).1
  have ready : original.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, frame.publicView, State.publicView_eventReady]
    exact rightReady
  have fits := (runtime setup).serviceRisk_clear_protected_opportunity leaks bound who
    (repaired.recall who) view event rfl turn unrecorded clear
  have timely : original.application.WithinDeadline (runtime setup) event := by
    change original.application.publicView.WithinDeadline (runtime setup) event
    rw [frame.publicView]
    exact fits.withinDeadline
  have facts := legalFacts setup leaks horizon scheduler _ leftTrace
  have vacant : original.application.accepted (.inr event) = none := by
    cases associated : original.application.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        exact False.elim (ready.1
          (facts.binding.toAssociationInvariant.accepted_complete event candidate associated))
  have unused : original.application.HandleUnused (who, .prepared serial) :=
    fun field associated => facts.binding.accepted_fixed field _ associated fresh
  have submission := frame.binding_submission event payload outputEq codeEq node serial opening
    fresh ready
  have included := frame.binding event payload outputEq codeEq node serial opening
    (fun value usable => by rw [missing] at usable; cases usable) fresh ready timely vacant unused
    facts.serials
  have own := memory.repairResponse_ownBindings (runtime setup) leaks who onlyBindings view response
  rw [responseEq] at own
  let call : Submission (graph setup) := ⟨.commitment event (who, .prepared serial), opening⟩
  let originalResponse : app.Action := ⟨some ⟨call, .none⟩⟩
  let left := original.respond app who originalResponse
  let id := (who, original.network.nextSerial who)
  have unchanged := (runtime setup).reactive_respond_application leaks original who originalResponse
  have leftReady : left.application.config.cut.Ready event := by rwa [unchanged.1]
  have leftTimely : left.application.WithinDeadline (runtime setup) event := by
    change left.application.publicView.WithinDeadline (runtime setup) event
    rw [unchanged.2]
    exact timely
  have acceptedEq := congrArg PublicView.accepted unchanged.2
  have leftVacant := (congrFun acceptedEq (.inr event)).trans vacant
  have leftUnused : left.application.HandleUnused (who, .prepared serial) := by
    intro field associated
    exact unused field ((congrFun acceptedEq field).symm.trans associated)
  have found : left.network.lookup id =
      some ⟨id, ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩⟩ :=
    (runtime setup).respond_submit_lookup_of_ready leaks original who call facts.serials
      event rfl ready
  have handled := (runtime setup).handle_commitment_eq left.application id event
    (who, .prepared serial) who payload outputEq codeEq node leftReady leftTimely rfl rfl
      leftVacant leftUnused
  have nextCompleted : (left.includePending app id).application.config.cut.completed =
      insert event original.application.config.cut.completed := by
    change (ReactiveApplication.Execution.includePending ((runtime setup).reactiveApplication leaks)
      left id).application.config.cut.completed = _
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, reactiveApplication_handle, WitnessedPacket.tokenValid_commitment, ite_true,
      handled, Option.getD_some]
    change insert event left.application.config.cut.completed = _
    exact congrArg (insert event ·)
      (congrArg (fun config => config.cut.completed) unchanged.1)
  have advanced : original.application.config.cut.completed ⊆
      (left.includePending app id).application.config.cut.completed := by
    rw [nextCompleted]
    exact fun _ member => Finset.mem_insert_of_mem member
  have completed : event ∈ (left.includePending app id).application.config.cut.completed := by
    rw [nextCompleted]
    exact Finset.mem_insert_self _ _
  have valid := memory.repairResponse_completedAt (runtime setup) leaks who view event payload
    outputEq codeEq node serial opening (by rw [frame.observed]; exact fresh) rightFresh
      original.application.config _ completedMemory advanced completed
  dsimp only
  rw [chosen.1, responseEq]
  exact ⟨submission, own, included, valid⟩

end Vegas
