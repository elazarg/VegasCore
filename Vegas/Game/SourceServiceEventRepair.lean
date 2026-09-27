/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceProgramRepair
import Vegas.Game.SourceServiceForeignBindingBlock
import Vegas.Pending.ReactiveServiceAudit

/-! # Whole source-event blocks in actual continuation repair

The actual retained history supplies the source boundary before the grant.
Each source constructor then has its exact physical block coupling against the
same repaired policy and unchanged opponents. No payoff comparison is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem event_block_stopped_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event actor payload,
      (graph setup).outputLayout event = .binding actor payload → actor ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (source : ∀ who, ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (target : ∀ who, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (agrees : ((sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).ExtendsProfile source target)
    (owner : Player) (policy : (application setup leaks).Policy)
    (available : ∀ past view response, response ∈ (policy past view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner past view)
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (event : (graph setup).EventId) (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + (rosterBlock setup rosters event).length, none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ rosterBlock setup rosters event ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (rosterBlock setup rosters event) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network)
          (rosterBlock setup rosters event).length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players strategy
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let body : List (ServiceInstruction (graph setup)) :=
    (rosters event).map ServiceInstruction.player ++
      (match (graph setup).actor? event with
      | none => .sample event :: List.replicate (event.val + 1) .tick ++ [.expire event]
      | some actor => .includeLatest event actor ::
          List.replicate (event.val + 1) .tick ++ [.expire event])
  have block : rosterBlock setup rosters event = [.grant event] ++ body := by
    cases owned : (graph setup).actor? event <;>
      simp only [rosterBlock, body, owned, List.append_assoc, List.cons_append, List.nil_append]
  have cursor : repaired.environmentRecall.length = before.length := by
    rw [← frame.service]
    exact position
  have selected : (rosterPlan setup rosters)[repaired.environmentRecall.length]? =
      some (.grant event) := by
    rw [cursor, split, block, List.append_assoc,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨initial, _, Γ, config, refs, boundary⟩ := sourceService_grant_boundary setup leaks
    bounds values capacity rosters opportunities network profile
      ⟨remaining + (rosterBlock setup rosters event).length, none, repaired⟩ trace rfl event
      selected
  have phase := (roster_grant_prefix setup rosters _ event selected).1
  let advance (execution : app.Execution) : app.Execution := {
    execution with
    application := { execution.application with serviceGrant := some event }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant event)⟩] }
  have grantEnvironment (execution : app.Execution) :
      execution.environmentStep app (.application (.grant event)) =
        FinDist.pure (advance execution) := by
    simp only [ReactiveApplication.Execution.environmentStep, app, application,
      reactiveApplication, environmentStep, FinDist.map_pure]
    rfl
  have grantStep (execution : app.Execution) :
      (runtime setup).runInteractionPlan leaks players network [.grant event] execution =
        FinDist.pure (advance execution) := by
    simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    change ((execution.environmentStep app (.application (.grant event))).bind
      (app.resume players none)).bind FinDist.pure = _
    rw [grantEnvironment]
    simp only [FinDist.pure_bind, ReactiveApplication.resume]
  have paired := frame.grant event
  change BindingMemory.Frame (runtime setup) leaks memory owner
    (advance original) (advance repaired) at paired
  have moved (execution : app.Execution) : advance execution ∈
      (execution.environmentStep app (.application (.grant event))).support := by
    rw [grantEnvironment]
    exact FinDist.mem_support_pure.mpr rfl
  have nextTrace :
      (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length scheduler).Trace
      (some ⟨remaining + body.length, none, advance repaired⟩) := by
    apply Classical.choice
    exact menu.trace_environment (initialLaw setup) (rosterPlan setup rosters).length
      scheduler (remaining + body.length) repaired (advance repaired)
      (.application (.grant event)) (by
        have size : remaining + body.length + 1 =
            remaining + (rosterBlock setup rosters event).length := by
          simp only [block, List.length_append, List.length_singleton]
          omega
        rw [size]
        exact trace)
      (by
        simp only [scheduler, rosterScheduler, selected, interactionInstruction]
        exact FinDist.mem_support_pure.mpr rfl) (moved repaired)
  have nextPosition : (advance original).environmentRecall.length =
      (before ++ [ServiceInstruction.grant event]).length := by
    simp only [advance, List.length_append, List.length_singleton, position]
  have nextSplit : rosterPlan setup rosters = (before ++ [.grant event]) ++ body ++ after := by
    simpa only [block, List.append_assoc] using split
  have rightRecall := app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length
    scheduler (menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
      scheduler nextTrace)
  have leftNextRecall := app.environment_inputRecall original (advance original)
    (.application (.grant event)) leftRecall (moved original)
  have leftSound := ((runtime setup).packetEvidence leaks).sound_environment original
    (advance original) (.application (.grant event)) sound (moved original)
  have leftNextBinding : (advance original).application.BindingInvariant :=
    leftBinding.copy rfl rfl rfl
  have total : body.length = (rosters event).length + ((event.val + 1) + 2) := by
    cases owned : (graph setup).actor? event <;>
      simp only [body, owned, List.length_append, List.length_map, List.length_cons,
        List.length_replicate, List.length_nil]
  have phaseTrace :
      (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length scheduler).Trace
      (some ⟨remaining + (rosters event).length + ((event.val + 1) + 2),
        none, advance repaired⟩) := by
    simpa only [total, Nat.add_assoc] using nextTrace
  have nextStarted : reference.length ≤ ((advance repaired).recall owner).length := started
  have granted : (advance repaired).application.serviceGrant = some event := rfl
  have existsBody : ∃ coupling : FinDist
      (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        body (advance original) ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler body.length
        (advance repaired) memory ∧
      ∀ next ∈ coupling.support,
        Nonempty ((menu.protocol (initialLaw setup)
          (rosterPlan setup rosters).length scheduler).Trace
          (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
    cases node : nodeView (graph setup) event with
    | sample payload law outputEq codeEq =>
      have owned : (graph setup).actor? event = none :=
        (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
          (congrArg (fun code : EventCode (graph setup).layout (.publicData payload) =>
            code.actor) codeEq)
      have ready : (advance original).application.config.cut.Ready event := by
        have same := cut_eq_of_completionOrder_eq original.application.config
          repaired.application.config (congrArg
            (fun view : PublicView (graph setup) => view.observation.completionOrder)
            frame.publicView)
        change original.application.config.cut.Ready event
        rw [same]
        exact boundary.ready event rfl
      obtain ⟨coupling, first, second, related⟩ := sample_block_stopped_coupling setup leaks bounds
        rosters network source target agrees owner policy available reference memory
        (advance original) (advance repaired) paired onlyBindings nextStarted leftNextRecall
        rightRecall (by rw [paired.network]; exact boundary.serials)
        event payload law outputEq codeEq node
        rfl ready remaining (rosters event) (event.val + 1) phaseTrace
        (before ++ [.grant event]) after
        (by simpa only [body, owned, List.append_assoc] using nextSplit) nextPosition
      refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
      · simpa only [body, owned] using first
      · simpa only [body, owned] using second
      · exact ⟨(related next member).1, ((related next member).2).imp_right Or.inr⟩
    | bind actor payload outputEq codeEq =>
      have owned : (graph setup).actor? event = some actor :=
        (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
          (congrArg (fun code : EventCode (graph setup).layout (.binding actor payload) =>
            code.actor) codeEq)
      by_cases same : actor = owner
      · subst actor
        have deadline : (runtime setup).deadline event = event.val + 1 := rfl
        obtain ⟨coupling, first, second, related⟩ := binding_phase_stopped_coupling setup leaks
          bounds values capacity rosters opportunities network profile source target agrees owner
          policy available reference memory (advance original) (advance repaired) paired
          nextStarted leftNextRecall event payload outputEq codeEq node granted
          (boundary.unsent owner event (Nat.le_refl _)) remaining phaseTrace
          (before ++ [.grant event]) after
          (by simpa only [body, owned, deadline, List.append_assoc] using nextSplit) nextPosition
          (by simp only [List.length_append, List.length_singleton]; rw [cursor] at phase; omega)
        refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
        · simpa only [body, owned, deadline] using first
        · simpa only [body, owned, deadline] using second
        · refine ⟨(related next member).1, ?_⟩
          rcases (related next member).2 with bad | missed | framed
          · exact Or.inl bad
          · exact Or.inr (Or.inl (PublicView.missedBindingBy_of_event _ owner event owned missed))
          · exact Or.inr (Or.inr framed)
      · obtain ⟨coupling, first, second, related⟩ := foreign_binding_block_stopped_coupling setup
          leaks bounds values capacity rosters opportunities network profile source target agrees
          owner policy available reference memory (advance original) (advance repaired) paired
          onlyBindings nextStarted leftNextRecall event actor same payload outputEq codeEq node
          granted remaining (rosters event) (event.val + 1) phaseTrace
          (before ++ [.grant event]) after
          (by simpa only [body, owned, List.append_assoc] using nextSplit) nextPosition
        refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
        · simpa only [body, owned] using first
        · simpa only [body, owned] using second
        · exact ⟨(related next member).1, ((related next member).2).imp_right Or.inr⟩
    | resolve actor payload binding checks outputEq codeEq =>
      have owned : (graph setup).actor? event = some actor :=
        (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
          (congrArg (fun code : EventCode (graph setup).layout (.publication payload) =>
            code.actor) codeEq)
      obtain ⟨coupling, first, second, related⟩ := resolution_block_stopped_coupling setup leaks
        bounds values capacity rosters opportunities network profile source target agrees owner
        policy available reference memory (advance original) (advance repaired) paired onlyBindings
        nextStarted leftNextRecall leftSound leftNextBinding event actor payload binding checks
        outputEq codeEq node granted remaining (rosters event) (event.val + 1) phaseTrace
        (before ++ [.grant event]) after
        (by simpa only [body, owned, List.append_assoc] using nextSplit) nextPosition
      refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
      · simpa only [body, owned] using first
      · simpa only [body, owned] using second
      · exact ⟨(related next member).1, ((related next member).2).imp_right Or.inr⟩
  obtain ⟨coupling, first, second, related⟩ := existsBody
  refine ⟨coupling, ?_, ?_, related⟩
  · rw [block, runInteractionPlan_append, grantStep, FinDist.pure_bind]
    exact first
  · rw [block, List.length_append, ReactiveApplication.Implementation.runJoint_add,
      roster_segment_runJoint setup leaks rosters network strategy owner players before
        [.grant event] (body ++ after) (by simpa only [block, List.append_assoc] using split)
        (by simp) repaired memory cursor, grantStep, FinDist.map_pure, FinDist.pure_bind]
    exact second

end Vegas.SourceProgram.RevealService
