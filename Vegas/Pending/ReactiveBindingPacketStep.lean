/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingUsableStep
import Vegas.Pending.ReactiveBindingFrameCommands

/-! # Actual packet inclusion up to an owner's signed breach

All wire constructors preserve the complete repair frame, except an opening
accepted only after repair. That exception identifies the same actual owner
envelope and proves its signed-content breach. Owner commitments either address
completed events or have fixed matching candidate meanings. The latter includes
later fresh usable bindings with their actual success or expiry.
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

/-- Any actual withholding packet has the same inclusion transition. The
reactive histories' empty application caches make the accepted decision FALSE;
nonempty packet evidence does not change the contract's call handler. -/
theorem withholding_step_unremembered
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (leftRemembered : original.application.remembered = fun _ => none)
    (rightRemembered : repaired.application.remembered = fun _ => none)
    (id : MessageId Player) (event : graph.EventId)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id = some ⟨id, ⟨.withhold event, evidence, token⟩⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  let packet : WitnessedPacket graph := ⟨.withhold event, evidence, token⟩
  by_cases valid : packet.tokenValid = true
  swap
  · exact frame.include_rejected id packet found
      (reactiveApplication_handle_of_not_tokenValid runtime leaks original.application _
        (Bool.eq_false_iff.mpr valid))
      (reactiveApplication_handle_of_not_tokenValid runtime leaks repaired.application _
        (Bool.eq_false_iff.mpr valid))
  have acceptance : (handle runtime original.application ⟨id, .withhold event⟩).isSome =
      (handle runtime repaired.application ⟨id, .withhold event⟩).isSome := by
    apply Bool.eq_iff_iff.mpr
    rw [handle_withhold_isSome_iff, handle_withhold_isSome_iff]
    rw [← State.publicView_eventReady, ← State.publicView_eventReady]
    have timely : original.application.WithinDeadline runtime event ↔
        repaired.application.WithinDeadline runtime event := by
      change (match original.application.publicView.activatedAt event with
        | none => False
        | some activated => original.application.publicView.clock - activated <
            runtime.deadline event) ↔ _
      rw [frame.publicView]
      rfl
    rw [frame.publicView, timely]
  cases handled : handle runtime original.application ⟨id, .withhold event⟩ with
  | none =>
      have rejected : handle runtime repaired.application ⟨id, .withhold event⟩ = none := by
        cases right : handle runtime repaired.application ⟨id, .withhold event⟩ with
        | none => rfl
        | some next => simp only [handled, right, Option.isSome_none, Option.isSome_some,
            Bool.false_eq_true] at acceptance
      exact frame.include_rejected id packet found (reactiveHandle_none handled)
        (reactiveHandle_none rejected)
  | some next =>
      have conditions := (handle_withhold_isSome_iff runtime original.application id event).mp
        (by simp only [handled, Option.isSome_some])
      obtain ⟨ready, timely, authored⟩ := conditions
      cases node : nodeView graph event with
      | bind | sample => simp only [node] at authored
      | resolve actor payload binding checks outputEq codeEq =>
          simp only [node] at authored
          have rightReady : repaired.application.config.cut.Ready event := by
            rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
            exact ready
          have rightTimely : repaired.application.WithinDeadline runtime event := by
            change (match repaired.application.publicView.activatedAt event with
              | none => False
              | some activated => repaired.application.publicView.clock - activated <
                  runtime.deadline event)
            rw [← frame.publicView]
            exact timely
          obtain ⟨named, addressed, tokened⟩ := (WitnessedPacket.tokenValid_iff packet).mp valid
          have eventEq : named = event := (Option.some.inj addressed).symm
          subst named
          change token = some ⟨event⟩ at tokened
          subst token
          have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
          have completed := frame.complete_unmodified event ready rightReady
            (onlyBindings.public_value_none (.inr event) visible)
            (onlyBindings.public_action_none event visible)
            (cast (congrArg EventField.Action outputEq.symm) false)
            (cast (congrArg EventField.Value outputEq.symm)
              (PublicationResult.failure : PublicationResult (L.Val payload)))
          exact frame.include_accepted id _ found (WitnessedPacket.tokenValid_withhold _ _) _ _
            completed
            (runtime.handle_withhold_unremembered_eq original.application id event actor payload
              binding checks outputEq codeEq node ready timely authored (congrFun leftRemembered _))
            (runtime.handle_withhold_unremembered_eq repaired.application id event actor payload
              binding checks outputEq codeEq node rightReady rightTimely authored
                (congrFun rightRemembered _))

/-- Every actual pending envelope preserves the repair frame or identifies
an opening breach by the repaired owner. Acceptance and both real rejection
branches are derived from the handlers, including publication failure. -/
theorem packet_step_or_owner_breach
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (fixed : runtime.ReactiveCommitmentsFixed leaks original)
    (leftRemembered : original.application.remembered = fun _ => none)
    (rightRemembered : repaired.application.remembered = fun _ => none)
    (ownerCommitment : ∀ id event candidate evidence token,
      original.network.lookup id = some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ →
        id.1 = owner →
        (WitnessedPacket.mk (.commitment event candidate) evidence token).tokenValid = true →
          event ∈ original.application.config.cut.completed ∨
            (original.application.candidates.lookup candidate ≠ .fresh ∧
              original.application.candidates.lookup candidate =
                repaired.application.candidates.lookup candidate))
    (id : MessageId Player) (packet : WitnessedPacket graph)
    (found : original.network.lookup id = some ⟨id, packet⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } ∨
      id.1 = owner ∧ SignedContentBreach ⟨id, packet⟩ := by
  rcases packet with ⟨call, evidence, token⟩
  cases call with
  | malformed raw =>
      exact Or.inl (frame.include_rejected id _ found (reactiveHandle_none rfl)
        (reactiveHandle_none rfl))
  | commitment event candidate =>
      by_cases authored : id.1 = owner
      swap
      · exact Or.inl (frame.commitment_step_completed_owner onlyBindings fixed id event candidate
          evidence token found (fun same _ => (authored same).elim))
      by_cases valid :
          (WitnessedPacket.mk (.commitment event candidate) evidence token).tokenValid = true
      swap
      · exact Or.inl (frame.commitment_step_completed_owner onlyBindings fixed id event candidate
          evidence token found (fun _ tokened => (valid tokened).elim))
      rcases ownerCommitment id event candidate evidence token found authored valid with
        completed | matching
      · exact Or.inl (frame.commitment_step_completed_owner onlyBindings fixed id event candidate
          evidence token found (fun _ _ => completed))
      · exact Or.inl (frame.commitment_step_matching_owner past id authored event candidate
          evidence token found matching.1 matching.2).1
  | withhold event =>
      exact Or.inl (frame.withholding_step_unremembered onlyBindings leftRemembered rightRemembered
        id event evidence token found)
  | opening event candidate raw =>
      cases node : nodeView graph event with
      | bind | sample =>
          have rejected (state : State graph) :
              handle runtime state ⟨id, .opening event candidate raw⟩ = none := by
            simp only [handle, node]
            split <;> simp_all
          exact Or.inl (frame.include_rejected id _ found
            (reactiveHandle_none (rejected original.application))
            (reactiveHandle_none (rejected repaired.application)))
      | resolve actor payload binding checks outputEq codeEq =>
          exact frame.opening_step_or_owner_breach onlyBindings sound leftBinding rightBinding id
            event candidate raw actor payload binding checks outputEq codeEq node evidence token
              found

/-- The actual include command has joint marginals, including unknown IDs.
Any exceptional support branch identifies the original pending envelope,
whose author and content breach are derived rather than stipulated. -/
theorem include_coupling_or_owner_breach
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (fixed : runtime.ReactiveCommitmentsFixed leaks original)
    (leftRemembered : original.application.remembered = fun _ => none)
    (rightRemembered : repaired.application.remembered = fun _ => none)
    (ownerCommitment : ∀ id event candidate evidence token,
      original.network.lookup id = some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ →
        id.1 = owner →
        (WitnessedPacket.mk (.commitment event candidate) evidence token).tokenValid = true →
          event ∈ original.application.config.cut.completed ∨
            (original.application.candidates.lookup candidate ≠ .fresh ∧
              original.application.candidates.lookup candidate =
                repaired.application.candidates.lookup candidate))
    (id : MessageId Player) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app (.include id) ∧
      coupling.map Prod.snd = repaired.environmentStep app (.include id) ∧
      ∀ pair ∈ coupling.support,
        Frame runtime leaks memory owner pair.1 pair.2 ∨
          ∃ packet, original.network.lookup id = some ⟨id, packet⟩ ∧
            id.1 = owner ∧ SignedContentBreach ⟨id, packet⟩ := by
  let app := runtime.reactiveApplication leaks
  let included (execution : app.Execution) : app.Execution :=
    { execution.includePending app id with
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .include id⟩] }
  have actual (execution : app.Execution) :
      execution.environmentStep app (.include id) = PMF.pure (included execution) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  refine ⟨PMF.pure (included original, included repaired), ?_, ?_, ?_⟩
  · rw [PMF.pure_map, actual]
  · rw [PMF.pure_map, actual]
  · intro pair supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    cases found : original.network.lookup id with
    | none =>
        have rightFound : repaired.network.lookup id = none := frame.network ▸ found
        simp only [included, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found, rightFound]
        exact Or.inl { frame with
          service := by
            change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
            rw [frame.service, frame.environment] }
    | some message =>
        have hit := List.find?_some found
        have identified : message.id = id := of_decide_eq_true hit
        rcases message with ⟨messageId, packet⟩
        change messageId = id at identified
        subst messageId
        rcases frame.packet_step_or_owner_breach onlyBindings past sound leftBinding rightBinding
            fixed leftRemembered rightRemembered ownerCommitment id packet found with paired | bad
        · exact Or.inl paired
        · exact Or.inr ⟨packet, rfl, bad⟩

/-- Every scheduler command is coupled at a completed repair boundary up to
the same actual owner opening breach. Sampling remains a common partial leak
draw, and application commands include all stutters and explicit expiry. -/
theorem environment_coupling_or_owner_breach
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (fixed : runtime.ReactiveCommitmentsFixed leaks original)
    (leftRemembered : original.application.remembered = fun _ => none)
    (rightRemembered : repaired.application.remembered = fun _ => none)
    (ownerCommitment : ∀ id event candidate evidence token,
      original.network.lookup id = some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ →
        id.1 = owner →
        (WitnessedPacket.mk (.commitment event candidate) evidence token).tokenValid = true →
          event ∈ original.application.config.cut.completed ∨
            (original.application.candidates.lookup candidate ≠ .fresh ∧
              original.application.candidates.lookup candidate =
                repaired.application.candidates.lookup candidate))
    (command : (runtime.reactiveApplication leaks).Command) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app command ∧
      coupling.map Prod.snd = repaired.environmentStep app command ∧
      ∀ pair ∈ coupling.support,
        Frame runtime leaks memory owner pair.1 pair.2 ∨
          ∃ id packet, command = .include id ∧
            original.network.lookup id = some ⟨id, packet⟩ ∧
              id.1 = owner ∧ SignedContentBreach ⟨id, packet⟩ := by
  let app := runtime.reactiveApplication leaks
  cases command with
  | wait =>
      let waited (execution : app.Execution) : app.Execution :=
        { execution with environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .wait⟩] }
      refine ⟨PMF.pure (waited original, waited repaired), ?_, ?_, ?_⟩
      · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
      · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
      · intro pair supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact Or.inl { frame with
          service := by
            change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
            rw [frame.service, frame.environment] }
  | activate actor =>
      let activated (execution : app.Execution) (selected : Finset (MessageId Player)) :
          app.Execution :=
        { execution with
          network := execution.network.learn actor selected
          environmentRecall := execution.environmentRecall ++
            [⟨execution.observeEnvironment app, .activate actor⟩] }
      let coupling := (leaks actor original.network.pending).map fun selected =>
        (activated original selected, activated repaired selected)
      refine ⟨coupling, ?_, ?_, ?_⟩
      · simp only [coupling, activated, PMF.map_comp, Function.comp_def,
          ReactiveApplication.Execution.environmentStep]
        rfl
      · simp only [coupling, activated, PMF.map_comp, Function.comp_def,
          ReactiveApplication.Execution.environmentStep, ← frame.network]
        rfl
      · intro pair supported
        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact Or.inl (frame.activate actor selected)
  | application command =>
      obtain ⟨coupling, left, right, related⟩ :=
        frame.application_coupling onlyBindings past command
      exact ⟨coupling, left, right, fun pair supported => Or.inl (related pair supported)⟩
  | «include» id =>
      obtain ⟨coupling, left, right, related⟩ := frame.include_coupling_or_owner_breach
        onlyBindings past sound leftBinding rightBinding fixed leftRemembered rightRemembered
          ownerCommitment id
      refine ⟨coupling, left, right, fun pair supported => ?_⟩
      rcases related pair supported with paired | ⟨packet, found, bad⟩
      · exact Or.inl paired
      · exact Or.inr ⟨id, packet, rfl, found, bad⟩

end Vegas.EventGraphRuntime.BindingMemory.Frame
