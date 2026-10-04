/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingWaiting
import Vegas.Game.SourceServiceFinalBindingRepair
import Vegas.Game.SourceServiceFirstBindingBlock

/-! # The stopped arbitrary binding roster

The induction follows the actual remaining response opportunities. Optional
transport defers to the next visit; a first opaque submission uses the same
private repair through the complete tail; final omission has public deadline
evidence. Original opponent laws remain fixed throughout.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] in
private theorem split_at_first (owner : Player) (visits : List Player) (member : owner ∈ visits) :
    ∃ earlier later, visits = earlier ++ owner :: later ∧ owner ∉ earlier := by
  classical
  induction visits with
  | nil => cases member
  | cons who rest ih =>
      by_cases same : who = owner
      · subst who
        exact ⟨[], rest, rfl, List.not_mem_nil⟩
      · obtain ⟨earlier, later, split, absent⟩ := ih (List.mem_of_ne_of_mem (Ne.symm same) member)
        exact ⟨who :: earlier, later, congrArg (List.cons who) split,
          by simpa only [List.mem_cons, not_or] using And.intro (Ne.symm same) absent⟩

theorem binding_window_stopped_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
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
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (remaining : Nat) (prior original repaired : (application setup leaks).Execution)
    (sampled : original ∈
      (prior.environmentStep (application setup leaks) (.activate owner)).support)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, repaired⟩))
    (started : reference.length ≤ (repaired.recall owner).length)
    (recalled : original.InputRecall (application setup leaks))
    (ready : repaired.application.config.cut.Ready event)
    (unsent : (runtime setup).eventRecorded leaks (repaired.recall owner) event = false)
    (visited visits : List Player) (roster : rosters event = visited ++ owner :: visits)
    (slot : original.environmentRecall.length =
      (rosterPlanPrefix setup rosters event.val).length + visited.length + 1)
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ((runtime setup).deadline event) .tick ++
        [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length)
    (enough : visits.length + 1 + (runtime setup).deadline event + 1 ≤ remaining) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        ((runtime setup).runInteractionPlan leaks players network
          (visits.map ServiceInstruction.player ++ (.includeLatest event owner ::
            List.replicate ((runtime setup).deadline event) .tick ++ [.expire event]))) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          strategy.runJoint owner players (rosterScheduler setup leaks rosters network)
            (visits.length + 1 + (runtime setup).deadline event + 1) next.1 next.2) ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining - (visits.length + 1 + (runtime setup).deadline event + 1),
              none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        next.1.application.publicView.missedBinding event = true ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players strategy
  suffices result :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = (app.invoke players owner original).bind
          ((runtime setup).runInteractionPlan leaks players network
            (visits.map ServiceInstruction.player ++ (.includeLatest event owner ::
              List.replicate ((runtime setup).deadline event) .tick ++ [.expire event]))) ∧
        coupling.map Prod.snd =
          (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
            strategy.runJoint owner players (rosterScheduler setup leaks rosters network)
              (visits.length + 1 + (runtime setup).deadline event + 1) next.1 next.2) ∧
        ∀ next ∈ coupling.support,
          (∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
          next.1.application.publicView.missedBinding event = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 by
    obtain ⟨coupling, first, second, related⟩ := result
    let menu := sourceServiceMenu setup leaks bounds rosters
    let scheduler := rosterScheduler setup leaks rosters network
    have opponents : ∀ who, who ≠ owner → menu.Admissible (initialLaw setup)
        (rosterPlan setup rosters).length scheduler who (players who) := by
      intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    have own : ∀ next past view response,
        response ∈ (strategy.respond next (past, view)).support →
          response.1 ∈ menu.actions owner past view := by
      intro next past view response supported
      exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
        owner reference (players owner) next (past, view) response supported
    refine ⟨coupling, first, second, ?_⟩
    intro next supported
    refine ⟨?_, related next supported⟩
    have reached : next.2 ∈ ((strategy.resume owner players (some owner) repaired memory).bind
        (fun pair => strategy.runJoint owner players scheduler
          (visits.length + 1 + (runtime setup).deadline event + 1) pair.1 pair.2)).support := by
      rw [← second, PMF.support_map]
      exact ⟨next, supported, rfl⟩
    obtain ⟨middle, resumed, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    obtain ⟨middleTrace⟩ := menu.trace_implementation_resume (initialLaw setup)
      (rosterPlan setup rosters).length scheduler strategy owner players opponents own remaining
        (some owner) repaired memory trace middle resumed
    exact menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players opponents own
        (remaining - (visits.length + 1 + (runtime setup).deadline event + 1))
        (visits.length + 1 + (runtime setup).deadline event + 1) middle.1 middle.2
        (by rw [Nat.sub_add_cancel enough]; exact middleTrace) next.2 reached
  induction count : visits.length using Nat.strong_induction_on generalizing visits visited
      remaining prior original repaired memory before with
  | h size ih =>
    simp only [← count] at enough ⊢
    let menu := sourceServiceMenu setup leaks bounds rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let tail : List (ServiceInstruction (graph setup)) :=
      .includeLatest event owner :: List.replicate ((runtime setup).deadline event) .tick ++
        [.expire event]
    let plan := visits.map ServiceInstruction.player ++ tail
    have length : plan.length = visits.length + 1 + (runtime setup).deadline event + 1 := by
      simp only [plan, tail, List.length_append, List.length_map, List.length_cons,
        List.length_replicate, List.length_nil]
      omega
    have covered : ∀ past view response, response ∈ (players owner past view).support →
        response ∈ (bounds.menu (runtime setup) leaks).actions owner past view := by
      simpa only [players, Function.update_self] using available
    by_cases last : owner ∉ visits
    · obtain ⟨coupling, first, second, related⟩ := final_binding_history_coupling setup leaks
        bounds values capacity rosters opportunities network players owner remaining
          prior original repaired sampled memory frame trace reference started recalled event
          payload outputEq codeEq node ready unsent (covered _ _) before after visits last
          (by simpa only [List.append_assoc, List.singleton_append, List.cons_append,
            List.nil_append] using split)
          position
      refine ⟨coupling, ?_, ?_, related⟩
      · simpa only [List.append_assoc, List.singleton_append, List.cons_append,
          List.nil_append] using first
      · simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil,
          List.length_replicate, Nat.add_assoc, Nat.zero_add] using second
    · have later : owner ∈ visits := Decidable.byContradiction last
      obtain ⟨foreign, rest, visitsEq, absent⟩ := split_at_first owner visits later
      have owned : (graph setup).actor? event = some owner := by
        have actor := congrArg EventCode.actor codeEq
        rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
        exact actor
      have optional : ¬ bindingRequired setup leaks rosters owner (repaired.recall owner)
          (repaired.observe app owner) := by
        rw [sourceService_bindingRequired_iff_no_later_owner setup leaks bounds values capacity
          rosters opportunities network owner ⟨remaining, some owner, repaired⟩ trace rfl
            event ready payload outputEq owned unsent visited visits roster
            (by rw [← frame.service]; exact slot)]
        exact last
      obtain ⟨ready, timely, _, rightRecall, _, serials, firstResources⟩ :=
        sourceService_binding_decision_resources setup leaks bounds values capacity rosters
          opportunities network owner ⟨remaining, some owner, repaired⟩ trace rfl
            event ready owner payload outputEq codeEq node owned
      obtain ⟨small, selected, fresh, unused, vacant, accounted, published⟩ := firstResources unsent
      have counted : original.application.publicView.bindingCount owner =
          repaired.application.publicView.bindingCount owner :=
        congrArg (fun view => view.bindingCount owner) frame.publicView
      have originalReady : original.application.config.cut.Ready event := by
        rw [← State.publicView_eventReady, frame.publicView, State.publicView_eventReady]
        exact ready
      have originalFresh : original.application.candidates.lookup
          (owner, .prepared (original.application.publicView.bindingCount owner)) = .fresh := by
        rw [counted]
        exact (frame.slots _).mpr fresh
      have originalSerials : original.network.SerialsBeforeNext := frame.network ▸ serials
      have originalTimely : original.application.WithinDeadline (runtime setup) event := by
        unfold State.WithinDeadline
        rw [show original.application.clock = repaired.application.clock from
          congrArg PublicView.clock frame.publicView,
          show original.application.activatedAt = repaired.application.activatedAt from
            congrArg PublicView.activatedAt frame.publicView]
        exact timely
      have originalAccepted : original.application.accepted = repaired.application.accepted :=
        congrArg PublicView.accepted frame.publicView
      have originalVacant : original.application.accepted (.inr event) = none := by
        rw [originalAccepted]
        exact vacant
      have originalUnused : original.application.HandleUnused
          (owner, .prepared (original.application.publicView.bindingCount owner)) := by
        rw [counted]
        intro field same
        exact unused field ((congrFun originalAccepted field).symm.trans same)
      have originalPublished : original.network.Satisfies fun message => message.sender = owner →
          message.id ∈ original.network.ledger.map Message.id := by
        rw [frame.network]
        exact published.mono fun _ known _ => known
      let law := players owner (original.recall owner) (original.observe app owner)
      let proposed (response : app.Action) :=
        let changed := memory.repairResponse (runtime setup) leaks owner
          (repaired.observe app owner) response
        (changed.1, (⟨changed.2, memory.responses ++
          [(memory.shadow.inputView (runtime setup) leaks
            (repaired.observe app owner), response)]⟩ :
            BindingMemory (runtime setup) leaks))
      let adjusted (response : app.Action) :=
        (if (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
            (repaired.observe app owner) then (proposed response).1
          else (menu.nonempty owner (repaired.recall owner) (repaired.observe app owner)).choose,
          (proposed response).2)
      let leftRun (response : app.Action) := (runtime setup).runInteractionPlan leaks players
        network plan (original.respond app owner response)
      let rightRun (response : app.Action) := strategy.runJoint owner players scheduler plan.length
        (repaired.respond app owner (adjusted response).1) (adjusted response).2
      let good (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks) :=
        (∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        next.1.application.publicView.missedBinding event = true ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1
      have responseLaw : strategy.respond memory (repaired.recall owner,
          repaired.observe app owner) = law.map adjusted := by
        change ((BindingMemory.implementation (runtime setup) leaks owner reference
          (players owner)).respond memory
            (repaired.recall owner, repaired.observe app owner)).map _ = _
        rw [BindingMemory.implementation_respond (runtime setup) leaks owner reference
          (players owner) memory (repaired.recall owner) (repaired.observe app owner) started,
          frame.past, frame.observed, PMF.map_comp]
        simp only [law, adjusted, proposed, frame.observed, app, menu, Function.comp_def]
      have existsBranch (response : app.Action) (member : response ∈ law.support) :
          ∃ coupling : PMF (app.Execution × app.Execution ×
            BindingMemory (runtime setup) leaks),
            coupling.map Prod.fst = leftRun response ∧ coupling.map Prod.snd = rightRun response ∧
            ∀ next ∈ coupling.support, good next := by
        rcases (runtime setup).binding_audit_response_cases leaks bounds original owner remaining
            event payload outputEq codeEq node
              ((soleReady_of_ready setup original.application originalReady).ownTurn owned)
              originalFresh recalled originalSerials
              response (covered _ _ response member) with replay | canonical | departure
        · have unchanged : memory.repairResponse (runtime setup) leaks owner
              (repaired.observe app owner) response = (response, memory.shadow) := by
            rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> rfl
          have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
              (repaired.observe app owner) := by
            dsimp only [proposed]
            rw [unchanged]
            change response ∈ sourceServiceActions setup leaks bounds rosters owner _ _
            rw [sourceServiceActions, ite_eq_right optional]
            apply bounds.replay_compiled
            rw [← app.replayPolicy_eq_of_network_eq original repaired owner recalled rightRecall
              frame.network]
            exact replay
          have adjustedEq : adjusted response = proposed response := by
            dsimp only [adjusted]
            rw [ite_eq_left legal]
          have nextEnough : foreign.length + 1 ≤ remaining := by
            simp only [visitsEq, List.length_append, List.length_cons] at enough
            omega
          obtain ⟨step, first, second, related⟩ := binding_waiting_opportunity setup leaks bounds
            rosters network source target agrees owner policy reference memory original repaired
              frame (remaining - (foreign.length + 1)) foreign absent
              (by
                have same : remaining - (foreign.length + 1) + 1 + foreign.length = remaining := by
                  omega
                rw [same]
                exact trace) recalled rightRecall response replay optional
              event ready unsent before
              (rest.map ServiceInstruction.player ++ tail ++ after)
              (by simpa only [tail, visitsEq, List.map_append, List.map_cons, List.append_assoc,
                List.cons_append, List.nil_append] using split) position
          let nextVisited := visited ++ owner :: foreign
          let nextBefore := before ++ foreign.map ServiceInstruction.player ++ [.player owner]
          let restPlan := rest.map ServiceInstruction.player ++ tail
          have restLength : restPlan.length =
              rest.length + 1 + (runtime setup).deadline event + 1 := by
            simp only [restPlan, tail, List.length_append, List.length_map, List.length_cons,
              List.length_replicate, List.length_nil]
            omega
          have existsTail next (chosen : next ∈ step.support) :
              ∃ coupling : PMF (app.Execution × app.Execution ×
                BindingMemory (runtime setup) leaks),
                coupling.map Prod.fst = (app.invoke players owner next.1).bind
                  ((runtime setup).runInteractionPlan leaks players network restPlan) ∧
                coupling.map Prod.snd =
                  (strategy.resume owner players (some owner) next.2.1 next.2.2).bind
                    (fun resumed => strategy.runJoint owner players scheduler restPlan.length
                      resumed.1 resumed.2) ∧
                ∀ final ∈ coupling.support, good final := by
            obtain ⟨paired, memoryEq, ⟨nextTrace⟩, nextRecall, nextReady, nextUnsent,
                predecessor, reached, activated⟩ := related next chosen
            have advanced := (runtime setup).runInteractionPlan_recall leaks players network
              (foreign.map ServiceInstruction.player) (original.respond app owner response)
                predecessor reached
            rw [app.respond_environmentRecall, List.length_map] at advanced
            have cursor : next.1.environmentRecall.length =
                original.environmentRecall.length + foreign.length + 1 := by
              rw [ReactiveApplication.Execution.activation_samples,
                PMF.support_map] at activated
              obtain ⟨selected, _, same⟩ := activated
              rw [← same]
              change (predecessor.environmentRecall ++ [_]).length = _
              simp only [List.length_append, List.length_singleton]
              omega
            have nextStarted : reference.length ≤ (next.2.1.recall owner).length := by
              rw [paired.lengths, memoryEq]
              change reference.length ≤ (memory.responses ++ [_]).length
              rw [List.length_append, List.length_singleton, ← frame.lengths]
              omega
            have newRoster : rosters event = nextVisited ++ owner :: rest := by
              simpa only [nextVisited, visitsEq, List.append_assoc, List.cons_append] using roster
            have newSlot : next.1.environmentRecall.length =
                (rosterPlanPrefix setup rosters event.val).length + nextVisited.length + 1 := by
              simp only [nextVisited, List.length_append, List.length_cons]
              omega
            have newSplit : rosterPlan setup rosters =
                nextBefore ++ rest.map ServiceInstruction.player ++ tail ++ after := by
              simpa only [nextBefore, tail, visitsEq, List.map_append, List.map_cons,
                List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
                using split
            have newPosition : next.1.environmentRecall.length = nextBefore.length := by
              simp only [nextBefore, List.length_append, List.length_map, List.length_singleton]
              omega
            have newEnough : rest.length + 1 + (runtime setup).deadline event + 1 ≤
                remaining - (foreign.length + 1) := by
              simp only [visitsEq, List.length_append, List.length_cons] at enough
              omega
            have shorter : rest.length < size := by
              rw [visitsEq, List.length_append, List.length_cons] at count
              omega
            obtain ⟨coupling, left, right, good⟩ := ih rest.length shorter
              (remaining - (foreign.length + 1)) predecessor next.1 next.2.1 activated next.2.2
              paired nextTrace nextStarted nextRecall nextReady nextUnsent nextVisited rest
              newRoster newSlot nextBefore newSplit newPosition newEnough rfl
            refine ⟨coupling, left, ?_, good⟩
            rw [restLength]
            exact right
          let branch := fun next chosen => (existsTail next chosen).choose
          refine ⟨step.bindOnSupport branch, ?_, ?_, ?_⟩
          · rw [map_bindOnSupport]
            calc
              _ = step.bind (fun next => (app.invoke players owner next.1).bind
                  ((runtime setup).runInteractionPlan leaks players network restPlan)) := by
                apply bindOnSupport_eq_bind_of_eq_on_support _
                intro next chosen
                exact (existsTail next chosen).choose_spec.1
              _ = (step.map Prod.fst).bind (fun execution =>
                  (app.invoke players owner execution).bind
                  ((runtime setup).runInteractionPlan leaks players network restPlan)) := by
                rw [PMF.bind_map]; rfl
              _ = leftRun response := by
                rw [first]
                simp only [leftRun, plan, restPlan, visitsEq, List.map_append, List.map_cons,
                  runInteractionPlan_append, runInteractionPlan, interactionStep,
                  interactionInstruction, PMF.pure_bind, ReactiveApplication.dispatch,
                  ReactiveApplication.Command.actor?, ReactiveApplication.resume,
                  PMF.bind_bind]
                apply bind_congr_on_support _
                intro execution _
                apply bind_congr_on_support _
                intro observed _
                apply bind_congr_on_support _
                intro responded _
                exact (runtime setup).runInteractionPlan_append leaks players network
                  (rest.map ServiceInstruction.player) tail responded
          · rw [map_bindOnSupport]
            calc
              _ = step.bind (fun next =>
                  (strategy.resume owner players (some owner) next.2.1 next.2.2).bind
                    (fun resumed => strategy.runJoint owner players scheduler restPlan.length
                      resumed.1 resumed.2)) := by
                apply bindOnSupport_eq_bind_of_eq_on_support _
                intro next chosen
                exact (existsTail next chosen).choose_spec.2.1
              _ = (step.map Prod.snd).bind (fun next =>
                  (strategy.resume owner players (some owner) next.1 next.2).bind
                    (fun resumed => strategy.runJoint owner players scheduler restPlan.length
                      resumed.1 resumed.2)) := by rw [PMF.bind_map]; rfl
              _ = rightRun response := by
                rw [second]
                have originalPair : proposed response = (response, memory.record (runtime setup)
                    leaks (memory.shadow.inputView (runtime setup) leaks
                      (repaired.observe app owner)) response) := by
                  dsimp only [proposed]
                  rw [unchanged]
                  rfl
                have pairedLaw := roster_runJoint_at_owner setup leaks rosters network strategy
                  owner players before (foreign.map ServiceInstruction.player) restPlan after
                  (by simpa only [restPlan, tail, visitsEq, List.map_append, List.map_cons,
                    List.append_assoc, List.cons_append] using split)
                  (repaired.respond app owner response)
                  (memory.record (runtime setup) leaks
                    (memory.shadow.inputView (runtime setup) leaks
                      (repaired.observe app owner)) response)
                  (by rw [app.respond_environmentRecall, ← frame.service]; exact position)
                have totalLength : plan.length = foreign.length + 1 + restPlan.length := by
                  simp only [plan, restPlan, visitsEq, List.map_append, List.map_cons,
                    List.length_append, List.length_map, List.length_cons]
                  omega
                simpa only [rightRun, adjustedEq, originalPair, totalLength,
                  PMF.bind_bind, PMF.bind_map, Function.comp_def, List.length_map]
                  using pairedLaw.symm
          · intro final supported
            obtain ⟨next, chosen, reached⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
            exact (existsTail next chosen).choose_spec.2.2 final reached
        · obtain ⟨opening, bounded, countedSerial, rfl⟩ := canonical
          let action : app.Action := ⟨some (.submit ⟨⟨.commitment event
            (owner, .prepared (original.application.publicView.bindingCount owner)), opening⟩,
              .none⟩)⟩
          have legal : (proposed action).1 ∈ menu.actions owner (repaired.recall owner)
              (repaired.observe app owner) := by
            apply required_binding_sourceService
            apply BindingMemory.repairResponse_binding_available (runtime setup) leaks bounds
              owner memory (repaired.recall owner) (repaired.observe app owner) event payload
              outputEq codeEq node
              ((soleReady_of_ready setup repaired.application ready).ownTurn owned) owned
              ((repaired.application.publicView_eventReady event).mpr ready) unsent
              (original.application.publicView.bindingCount owner)
            · rw [counted]
              exact selected
            · rw [counted]
              exact small
            · have coveredValue := values event
              rw [outputEq] at coveredValue
              exact coveredValue (L.someValue payload)
            · exact bounded
            · rw [frame.observed]
              exact originalFresh
          have adjustedEq : adjusted action = proposed action := by
            dsimp only [adjusted]
            rw [ite_eq_left legal]
          obtain ⟨coupling, first, second, related⟩ := first_binding_block_coupling setup leaks
            bounds rosters network players owner event payload outputEq codeEq node
              (original.application.publicView.bindingCount owner) opening memory original repaired
              frame reference started recalled rightRecall originalSerials countedSerial
              originalFresh originalReady originalTimely originalVacant originalUnused
              originalPublished covered before after visits ((runtime setup).deadline event)
              split position
          refine ⟨coupling, first, ?_, ?_⟩
          · change _ = rightRun action
            dsimp only [rightRun]
            rw [adjustedEq]
            exact second
          · intro next supported
            rcases related next supported with bad | framed
            · exact Or.inl bad
            · exact Or.inr (Or.inr framed)
        · obtain ⟨record, emitted, author, forbidden⟩ := departure
          refine ⟨bindPairLaw (leftRun response) (fun _ => (rightRun response)),
            bindPairLaw_map_fst .., bindPairLaw_const_map_snd .., ?_⟩
          intro next supported
          have reached : next.1 ∈ (leftRun response).support := by
            rw [← bindPairLaw_map_fst (leftRun response) (fun _ => rightRun response),
              PMF.support_map]
            exact ⟨next, supported, rfl⟩
          left
          refine ⟨record, ?_, author, forbidden⟩
          apply (runtime setup).trafficRecord_after_activation_plan leaks players network plan
            prior original next.1 owner response remaining sampled record _ reached
          rw [ReactiveApplication.Execution.activation_samples] at sampled
          obtain ⟨selected, _, same⟩ := PMF.support_map .. ▸ sampled
          rw [← same] at emitted ⊢
          exact emitted ▸ List.mem_singleton_self _
      let branch := fun response member => (existsBranch response member).choose
      refine ⟨law.bindOnSupport branch, ?_, ?_, ?_⟩
      · rw [map_bindOnSupport]
        change _ = (law.map (original.respond app owner)).bind _
        rw [PMF.bind_map]
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro response member
        exact (existsBranch response member).choose_spec.1
      · rw [map_bindOnSupport]
        simp only [ReactiveApplication.Implementation.resume, ↓reduceIte, PMF.bind_map]
        change _ = (strategy.respond memory (repaired.recall owner,
          repaired.observe app owner)).bind _
        rw [responseLaw, PMF.bind_map, ← length]
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro response member
        exact (existsBranch response member).choose_spec.2.1
      · intro next supported
        obtain ⟨response, member, reached⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
        exact (existsBranch response member).choose_spec.2.2 next reached

end Vegas
