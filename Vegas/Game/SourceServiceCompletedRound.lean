/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletedCommands
import Vegas.Game.SourceServiceCompletedResume
import Vegas.Game.SourceServiceRetainedLocalSlots

/-! # The actual completed scheduler round of binding repair

One real scheduler draw, environment step and resumption retain both actual
round marginals. The completed ledger consumes actual command provenance;
the same full-effective owner draw gives a copied boundary, genuine pending
default, or classified exit. Foreign policies use arbitrary raw actions.
An exceptional inclusion retains independent actual resumption laws.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Compose the real command and resumption kernels. The pending alternative
retains its actual before-input and selected response for the checked total
segment; it is not a completed-memory assertion or a future-support promise. -/
theorem sourceService_completed_round_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (ledger : OwnerCommitmentsInertOrMatching who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining + 1, none, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining + 1, none, repaired⟩))
    (rightAtTurn : OwnSubmissionsAtTurn setup leaks repaired who)
    (rightSlots : CanonicalSlotsUsed setup leaks repaired who)
    (owner : ((bounds.menu (runtime setup) leaks).information (initialLaw setup) horizon
      scheduler).BehavioralPolicy who)
    (foreign : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall who).length) :
    let app := application setup leaks
    let effectiveMenu := bounds.menu (runtime setup) leaks
    let players := Function.update foreign who
      (app.decodePolicy (effectiveMenu.embedPolicy (initialLaw setup) horizon scheduler who owner))
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
      (players who)
    let outcome := fun (command : app.Command) (beforeLeft beforeRight : app.Execution)
      (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks) =>
      (((command.actor? app) = some who ∧
        ∃ response ∈ (players who (beforeLeft.recall who)
                (beforeLeft.observe app who)).support,
          next.1 = beforeLeft.respond app who response ∧
          (auditableServiceResponse setup leaks who (beforeLeft.recall who)
            (beforeLeft.observe app who) response ∨
            recordedServiceResponse setup leaks (beforeLeft.recall who) response)) ∨
        (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings who ∧
          OwnSubmissionsAtTurn setup leaks next.2.1 who ∧
          CanonicalSlotsUsed setup leaks next.2.1 who ∧
          ((next.2.2.shadow.CompletedAt next.1.application.config ∧
            OwnerCommitmentsInertOrMatching who next.1 next.2.1) ∨
            ((command.actor? app) = some who ∧
              ∃ response ∈ (players who (beforeLeft.recall who)
                (beforeLeft.observe app who)).support,
                response ∈ effectiveMenu.actions who (beforeLeft.recall who)
                  (beforeLeft.observe app who) ∧
                let input := (beforeRight.recall who, beforeRight.observe app who)
                let selected := BindingMemory.retainedResponse (runtime setup) leaks menu who
                  memory input response
                next.1 = beforeLeft.respond app who response ∧
                next.2.1 = beforeRight.respond app who selected.1 ∧
                next.2.2 = ⟨selected.2, memory.responses ++
                  [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩ ∧
                ∃ event, (runtime setup).serviceRisk leaks bound who input.1 input.2 = false ∧
                  unusableServiceBindingResponse setup leaks who input.1 input.2 response ∧
                  (runtime setup).submittedEvent? leaks response = some event ∧
                  next.2.2.shadow.CompletedExcept next.1.application.config event))))
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.round scheduler players original ∧
      coupling.map Prod.snd = strategy.round who players scheduler repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨leftRemaining, none, next.1⟩)) ∧
        Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨rightRemaining, none, next.2.1⟩)) ∧
        ∃ command ∈
          (scheduler original.environmentRecall (original.observeEnvironment app)).support,
          ∃ beforeLeft beforeRight,
            beforeLeft ∈ (original.environmentStep app command).support ∧
            beforeRight ∈ (repaired.environmentStep app command).support ∧
            next.1 ∈ (app.resume players (command.actor? app) beforeLeft).support ∧
            next.2 ∈ (strategy.resume who players (command.actor? app) beforeRight memory).support ∧
            ((∃ id packet, command = .include id ∧
              original.network.lookup id = some ⟨id, packet⟩ ∧ id.1 = who ∧
                SignedContentBreach ⟨id, packet⟩) ∨
              (memory.Frame (runtime setup) leaks who beforeLeft beforeRight ∧
                memory.shadow.CompletedAt beforeLeft.application.config ∧
                OwnerCommitmentsInertOrMatching who beforeLeft beforeRight ∧
                OwnSubmissionsAtTurn setup leaks beforeRight who ∧
                CanonicalSlotsUsed setup leaks beforeRight who ∧
                Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                  (some ⟨leftRemaining, command.actor? app, beforeLeft⟩)) ∧
                Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                  (some ⟨rightRemaining, command.actor? app, beforeRight⟩)) ∧
                outcome command beforeLeft beforeRight next)) := by
  classical
  let app := application setup leaks
  let effectiveMenu := bounds.menu (runtime setup) leaks
  let players := Function.update foreign who
    (app.decodePolicy (effectiveMenu.embedPolicy (initialLaw setup) horizon scheduler who owner))
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
    (players who)
  let outcome := fun (command : app.Command) (beforeLeft beforeRight : app.Execution)
    (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks) =>
    (((command.actor? app) = some who ∧
      ∃ response ∈ (players who (beforeLeft.recall who)
              (beforeLeft.observe app who)).support,
        next.1 = beforeLeft.respond app who response ∧
        (auditableServiceResponse setup leaks who (beforeLeft.recall who)
          (beforeLeft.observe app who) response ∨
          recordedServiceResponse setup leaks (beforeLeft.recall who) response)) ∨
      (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
        next.2.2.shadow.OwnBindings who ∧
        OwnSubmissionsAtTurn setup leaks next.2.1 who ∧
        CanonicalSlotsUsed setup leaks next.2.1 who ∧
        ((next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsInertOrMatching who next.1 next.2.1) ∨
          ((command.actor? app) = some who ∧
            ∃ response ∈ (players who (beforeLeft.recall who)
              (beforeLeft.observe app who)).support,
              response ∈ effectiveMenu.actions who (beforeLeft.recall who)
                (beforeLeft.observe app who) ∧
              let input := (beforeRight.recall who, beforeRight.observe app who)
              let selected := BindingMemory.retainedResponse (runtime setup) leaks menu who
                memory input response
              next.1 = beforeLeft.respond app who response ∧
              next.2.1 = beforeRight.respond app who selected.1 ∧
              next.2.2 = ⟨selected.2, memory.responses ++
                [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩ ∧
              ∃ event, (runtime setup).serviceRisk leaks bound who input.1 input.2 = false ∧
                unusableServiceBindingResponse setup leaks who input.1 input.2 response ∧
                (runtime setup).submittedEvent? leaks response = some event ∧
                next.2.2.shadow.CompletedExcept next.1.application.config event))))
  let law := scheduler original.environmentRecall (original.observeEnvironment app)
  have existsDispatch (command : app.Command) (selected : command ∈ law.support) :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = app.dispatch players command original ∧
        coupling.map Prod.snd = (repaired.environmentStep app command).bind
          (fun next => strategy.resume who players (command.actor? app) next memory) ∧
        ∀ next ∈ coupling.support,
          ∃ beforeLeft beforeRight,
            beforeLeft ∈ (original.environmentStep app command).support ∧
            beforeRight ∈ (repaired.environmentStep app command).support ∧
            next.1 ∈ (app.resume players (command.actor? app) beforeLeft).support ∧
            next.2 ∈ (strategy.resume who players (command.actor? app) beforeRight memory).support ∧
            ((∃ id packet, command = .include id ∧
              original.network.lookup id = some ⟨id, packet⟩ ∧ id.1 = who ∧
                SignedContentBreach ⟨id, packet⟩) ∨
              (memory.Frame (runtime setup) leaks who beforeLeft beforeRight ∧
                memory.shadow.CompletedAt beforeLeft.application.config ∧
                OwnerCommitmentsInertOrMatching who beforeLeft beforeRight ∧
                OwnSubmissionsAtTurn setup leaks beforeRight who ∧
                CanonicalSlotsUsed setup leaks beforeRight who ∧
                Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                  (some ⟨leftRemaining, command.actor? app, beforeLeft⟩)) ∧
                Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                  (some ⟨rightRemaining, command.actor? app, beforeRight⟩)) ∧
                outcome command beforeLeft beforeRight next)) := by
    obtain ⟨environment, first, second, related⟩ := sourceService_completed_environment_coupling
      original repaired who memory frame onlyBindings past ledger leftTrace rightTrace rightAtTurn
        rightSlots command selected
    have leftSupport (pair) (member : pair ∈ environment.support) :
        pair.1 ∈ (original.environmentStep app command).support := by
      rw [← first, PMF.support_map]
      exact ⟨pair, member, rfl⟩
    have rightSupport (pair) (member : pair ∈ environment.support) :
        pair.2 ∈ (repaired.environmentStep app command).support := by
      rw [← second, PMF.support_map]
      exact ⟨pair, member, rfl⟩
    have existsResume (pair) (member : pair ∈ environment.support) :
        ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
          coupling.map Prod.fst = app.resume players (command.actor? app) pair.1 ∧
          coupling.map Prod.snd = strategy.resume who players (command.actor? app) pair.2 memory ∧
          ∀ next ∈ coupling.support,
            next.1 ∈ (app.resume players (command.actor? app) pair.1).support ∧
            next.2 ∈ (strategy.resume who players (command.actor? app) pair.2 memory).support ∧
            ((∃ id packet, command = .include id ∧
              original.network.lookup id = some ⟨id, packet⟩ ∧ id.1 = who ∧
                SignedContentBreach ⟨id, packet⟩) ∨
              (memory.Frame (runtime setup) leaks who pair.1 pair.2 ∧
                memory.shadow.CompletedAt pair.1.application.config ∧
                OwnerCommitmentsInertOrMatching who pair.1 pair.2 ∧
                OwnSubmissionsAtTurn setup leaks pair.2 who ∧
                CanonicalSlotsUsed setup leaks pair.2 who ∧
                Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                  (some ⟨leftRemaining, command.actor? app, pair.1⟩)) ∧
                Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                  (some ⟨rightRemaining, command.actor? app, pair.2⟩)) ∧
                outcome command pair.1 pair.2 next)) := by
      obtain ⟨currentLeft, currentRight, currentPast, currentLedger, currentAtTurn,
        currentSlots, currentFrame | breach⟩ := related pair member
      · obtain ⟨actualLeft⟩ := currentLeft
        obtain ⟨actualRight⟩ := currentRight
        have currentStarted : reference.length ≤ (pair.2.recall who).length := by
          rw [app.environmentStep_recall repaired pair.2 command (rightSupport pair member)]
          exact started
        obtain ⟨resume, left, right, supported⟩ := sourceService_completed_resume_coupling
          bounds bound values pair.1 pair.2 who memory currentFrame onlyBindings currentPast
            currentLedger (command.actor? app) actualLeft actualRight currentAtTurn currentSlots
              owner foreign reference currentStarted
        refine ⟨resume, left, right, ?_⟩
        intro next chosen
        have leftChosen : next.1 ∈ (app.resume players (command.actor? app) pair.1).support := by
          rw [← left, PMF.support_map]
          exact ⟨next, chosen, rfl⟩
        have rightChosen : next.2 ∈
            (strategy.resume who players (command.actor? app) pair.2 memory).support := by
          rw [← right, PMF.support_map]
          exact ⟨next, chosen, rfl⟩
        exact ⟨leftChosen, rightChosen, Or.inr ⟨currentFrame, currentPast, currentLedger,
          currentAtTurn, currentSlots, ⟨actualLeft⟩, ⟨actualRight⟩,
          (supported next chosen).2.2⟩⟩
      · let left := app.resume players (command.actor? app) pair.1
        let right := strategy.resume who players (command.actor? app) pair.2 memory
        refine ⟨bindPairLaw left (fun _ => right), bindPairLaw_map_fst ..,
          bindPairLaw_const_map_snd .., ?_⟩
        intro next chosen
        have leftChosen : next.1 ∈ left.support := by
          rw [← bindPairLaw_map_fst left (fun _ => right), PMF.support_map]
          exact ⟨next, chosen, rfl⟩
        have rightChosen : next.2 ∈ right.support := by
          rw [← bindPairLaw_const_map_snd left right, PMF.support_map]
          exact ⟨next, chosen, rfl⟩
        exact ⟨leftChosen, rightChosen, Or.inl breach⟩
    let resume := fun pair member => (existsResume pair member).choose
    refine ⟨environment.bindOnSupport resume, ?_, ?_, ?_⟩
    · rw [map_bindOnSupport]
      calc
        _ = environment.bind (fun pair => app.resume players (command.actor? app) pair.1) := by
          apply bindOnSupport_eq_bind_of_eq_on_support _
          intro pair member
          exact (existsResume pair member).choose_spec.1
        _ = (environment.map Prod.fst).bind (app.resume players (command.actor? app)) := by
          rw [PMF.bind_map]; rfl
        _ = _ := by rw [first]; rfl
    · rw [map_bindOnSupport]
      calc
        _ = environment.bind (fun pair => strategy.resume who players (command.actor? app)
            pair.2 memory) := by
          apply bindOnSupport_eq_bind_of_eq_on_support _
          intro pair member
          exact (existsResume pair member).choose_spec.2.1
        _ = (environment.map Prod.snd).bind (fun next => strategy.resume who players
            (command.actor? app) next memory) := by rw [PMF.bind_map]; rfl
        _ = _ := by rw [second]
    · intro next supported
      obtain ⟨pair, moved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
      exact ⟨pair.1, pair.2, leftSupport pair moved, rightSupport pair moved,
        (existsResume pair moved).choose_spec.2.2 next resumed⟩
  let dispatch := fun command selected => (existsDispatch command selected).choose
  let joint := law.bindOnSupport dispatch
  have first : joint.map Prod.fst = app.round scheduler players original := by
    rw [map_bindOnSupport]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro command selected
    exact (existsDispatch command selected).choose_spec.1
  have second : joint.map Prod.snd = strategy.round who players scheduler repaired memory := by
    rw [map_bindOnSupport]
    have same : scheduler repaired.environmentRecall (repaired.observeEnvironment app) = law := by
      rw [← frame.service, ← frame.environment]
    change _ = (scheduler repaired.environmentRecall (repaired.observeEnvironment app)).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro command selected
    exact (existsDispatch command selected).choose_spec.2.1
  refine ⟨joint, first, second, ?_⟩
  intro next member
  have leftChosen : next.1 ∈ (app.round scheduler players original).support := by
    rw [← first, PMF.support_map]
    exact ⟨next, member, rfl⟩
  have rightChosen : next.2 ∈ (strategy.round who players scheduler repaired memory).support := by
    rw [← second, PMF.support_map]
    exact ⟨next, member, rfl⟩
  have actualRight := sourceServiceRetained_round_slots bounds bound repaired who memory
    rightTrace (fun _ => ⟨rightAtTurn, rightSlots⟩) players reference next.2 rightChosen
  refine ⟨app.raw_trace_round (initialLaw setup) horizon scheduler players leftRemaining original
    next.1 leftTrace leftChosen, actualRight.1, ?_⟩
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
  exact ⟨command, selected, (existsDispatch command selected).choose_spec.2.2 next dispatched⟩

end Vegas
