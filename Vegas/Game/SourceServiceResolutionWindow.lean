/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionRepair
import Vegas.Pending.ReactiveBindingForeignWindow
import Vegas.Pending.ReactiveServiceTraffic

/-! # Stopped repair through repeated guarded-resolution visits

The proof follows the real roster. At every owner visit its actual repaired
history supplies the operational resources; arbitrary foreign responses keep
their original laws. A forbidden record survives the remaining raw service.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem resolution_dispatch_resources
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (original next : (application setup leaks).Execution) (actor : Player)
    (recalled : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (binding : original.application.BindingInvariant)
    (supported : next ∈ ((application setup leaks).dispatch players (.activate actor)
      original).support) :
    next.InputRecall (application setup leaks) ∧
      ((runtime setup).packetEvidence leaks).Sound next ∧
      next.application.BindingInvariant := by
  let app := application setup leaks
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
  exact ⟨app.respond_inputRecall middle actor response
    (app.environment_inputRecall original middle (.activate actor) recalled moved),
    ((runtime setup).packetEvidence leaks).sound_respond middle actor response
      (((runtime setup).packetEvidence leaks).sound_environment original middle
        (.activate actor) sound moved),
    ((runtime setup).reactiveBindingInvariant leaks).respond middle actor response
      (((runtime setup).reactiveBindingInvariant leaks).environmentStep original middle
        (.activate actor) binding moved)⟩

theorem resolution_roster_stopped_coupling
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
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (remaining : Nat) (visits : List Player)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (granted : repaired.application.serviceGrant = some event)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + visits.length, none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) visits.length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length) := by
  classical
  intro app players strategy
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  have opponents : ∀ who, who ≠ owner → menu.Admissible (initialLaw setup)
      (rosterPlan setup rosters).length scheduler who (players who) := by
    intro who different
    simpa only [players, Function.update_of_ne different] using
      (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
        (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
  have own : ∀ next past view response, response ∈ (strategy.respond next (past, view)).support →
      response.1 ∈ menu.actions owner past view := by
    intro next past view response member
    exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
      owner reference (players owner) next (past, view) response member
  induction visits generalizing original repaired memory before with
  | nil =>
      refine ⟨PMF.pure (original, repaired, memory), PMF.pure_map ..,
        PMF.pure_map .., ?_⟩
      intro next member
      cases (PMF.mem_support_pure_iff _ _).mp member
      exact ⟨⟨trace⟩, Or.inr ⟨frame, started⟩⟩
  | cons actor rest ih =>
      have cursor : repaired.environmentRecall.length = before.length := by
        rw [← frame.service]
        exact position
      have selected : (rosterPlan setup rosters)[repaired.environmentRecall.length]? =
          some (.player actor) := by
        rw [cursor, split, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self]
        rfl
      have command : scheduler repaired.environmentRecall (repaired.observeEnvironment app) =
          PMF.pure (.activate actor) := by
        simp only [scheduler, rosterScheduler, selected, interactionInstruction]
      have currentTrace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
          scheduler).Trace (some ⟨(remaining + rest.length) + 1, none, repaired⟩) := by
        simpa only [List.length_cons, Nat.add_assoc] using trace
      have existsStep : ∃ coupling : PMF (app.Execution × app.Execution ×
          BindingMemory (runtime setup) leaks),
          coupling.map Prod.fst = app.dispatch players (.activate actor) original ∧
          coupling.map Prod.snd = strategy.round owner players scheduler repaired memory ∧
          ∀ next ∈ coupling.support,
            Nonempty ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
              scheduler).Trace (some ⟨remaining + rest.length, none, next.2.1⟩)) ∧
            ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
              (runtime setup).permittedServiceEnvelope record.observation record.ledger
                record.input.envelope = false) ∨
              BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
                reference.length ≤ (next.2.1.recall owner).length) := by
        by_cases same : actor = owner
        · subst actor
          exact resolution_history_activation_coupling setup leaks bounds values capacity rosters
            opportunities network source target agrees owner policy available reference
              memory original repaired frame started leftRecall sound leftBinding event payload
                binding checks outputEq codeEq node granted (remaining + rest.length)
                  currentTrace selected
        · obtain ⟨physical, first, second, related⟩ :=
            frame.foreign_activation_coupling players actor same
          let step := physical.map fun pair => (pair.1, pair.2, memory)
          have actualRound : strategy.round owner players scheduler repaired memory =
              (app.dispatch players (.activate actor) repaired).map (fun next => (next, memory)) :=
            by
              change (scheduler repaired.environmentRecall (repaired.observeEnvironment app)).bind
                (fun command => (repaired.environmentStep app command).bind
                  (fun next => strategy.resume owner players (command.actor? app) next memory)) = _
              rw [command, PMF.pure_bind]
              simp only [ReactiveApplication.Implementation.resume,
                ReactiveApplication.Command.actor?, same, ↓reduceIte,
                ReactiveApplication.dispatch, ReactiveApplication.resume, PMF.map_bind]
              rfl
          have right : step.map Prod.snd = strategy.round owner players scheduler repaired memory :=
            by
              rw [actualRound]
              calc
                _ = (physical.map Prod.snd).map (fun next => (next, memory)) := by
                  simp only [step, PMF.map_comp]
                  rfl
                _ = _ := congrArg (fun law : PMF app.Execution =>
                  law.map (fun next => (next, memory))) second
          refine ⟨step, ?_, right, ?_⟩
          · simpa only [step, PMF.map_comp, Function.comp_def] using first
          · intro next member
            obtain ⟨pair, supported, rfl⟩ := PMF.support_map .. ▸ member
            have rightSupport : (pair.2, memory) ∈
                (strategy.round owner players scheduler repaired memory).support := by
              rw [← right, PMF.support_map]
              refine ⟨(pair.1, pair.2, memory), ?_, rfl⟩
              rw [PMF.support_map]
              exact ⟨pair, supported, rfl⟩
            refine ⟨menu.trace_implementation_round (initialLaw setup)
              (rosterPlan setup rosters).length scheduler strategy owner players opponents own
                (remaining + rest.length) repaired memory currentTrace _ rightSupport,
              Or.inr ⟨related pair supported, ?_⟩⟩
            have reached : pair.2 ∈ (app.dispatch players (.activate actor) repaired).support := by
              rw [← second, PMF.support_map]
              exact ⟨pair, supported, rfl⟩
            obtain ⟨middle, moved, resumed⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
            obtain ⟨response, _, equal⟩ := PMF.support_map .. ▸ resumed
            change reference.length ≤ (pair.2.recall owner).length
            rw [← equal, app.respond_recall_other middle actor owner (Ne.symm same) response,
              app.environmentStep_recall repaired middle (.activate actor) moved]
            exact started
      obtain ⟨step, first, second, related⟩ := existsStep
      have existsTail next (member : next ∈ step.support) :
          ∃ coupling : PMF (app.Execution × app.Execution ×
            BindingMemory (runtime setup) leaks),
            coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) next.1 ∧
            coupling.map Prod.snd = strategy.runJoint owner players scheduler rest.length
              next.2.1 next.2.2 ∧
            ∀ final ∈ coupling.support,
              (∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
                (runtime setup).permittedServiceEnvelope record.observation record.ledger
                  record.input.envelope = false) ∨
              BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1 ∧
                reference.length ≤ (final.2.1.recall owner).length := by
        by_cases bad : ∃ record ∈ app.executionTraffic next.1,
            record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false
        · let left := (runtime setup).runInteractionPlan leaks players network
            (rest.map ServiceInstruction.player) next.1
          let right := strategy.runJoint owner players scheduler rest.length next.2.1 next.2.2
          refine ⟨bindPairLaw left (fun _ => right), bindPairLaw_map_fst ..,
            bindPairLaw_const_map_snd .., ?_⟩
          intro final supported
          obtain ⟨record, present, authored, rejected⟩ := bad
          have reached : final.1 ∈ left.support := by
            rw [← bindPairLaw_map_fst left (fun _ => right), PMF.support_map]
            exact ⟨final, supported, rfl⟩
          exact Or.inl ⟨record, ((runtime setup).executionTraffic_runInteractionPlan leaks players
            network (rest.map ServiceInstruction.player) next.1 final.1 reached).subset present,
              authored, rejected⟩
        · obtain ⟨nextTrace⟩ := (related next member).1
          obtain ⟨paired, begun⟩ := ((related next member).2).resolve_left bad
          have reached : next.1 ∈ (app.dispatch players (.activate actor) original).support := by
            rw [← first, PMF.support_map]
            exact ⟨next, member, rfl⟩
          obtain ⟨recalled, certified, valid⟩ := resolution_dispatch_resources setup leaks players
            original next.1 actor leftRecall sound leftBinding reached
          have single : next.1 ∈ ((runtime setup).runInteractionPlan leaks players network
              ([actor].map ServiceInstruction.player) original).support := by
            simpa only [List.map_cons, List.map_nil, runInteractionPlan, interactionStep,
              interactionInstruction, PMF.pure_bind, PMF.bind_pure] using reached
          have publicEq := ((runtime setup).player_window_application leaks players network [actor]
            original next.1 single).2
          have nextGrant : next.2.1.application.serviceGrant = some event :=
            (congrArg PublicView.serviceGrant paired.publicView).symm.trans
              ((congrArg PublicView.serviceGrant publicEq).trans
                ((congrArg PublicView.serviceGrant frame.publicView).trans granted))
          have nextPosition : next.1.environmentRecall.length =
              (before ++ [ServiceInstruction.player actor]).length := by
            rw [app.dispatch_environmentRecall players (.activate actor) original next.1 reached]
            simp only [List.length_append, List.length_singleton, position]
          obtain ⟨coupling, leftLaw, rightLaw, connected⟩ := ih next.2.2 next.1 next.2.1
            paired begun recalled certified valid nextGrant nextTrace
              (before ++ [ServiceInstruction.player actor])
              (by simpa only [List.map_cons, List.append_assoc, List.singleton_append] using split)
                nextPosition
          exact ⟨coupling, leftLaw, rightLaw, fun final supported =>
            (connected final supported).2⟩
      let tail := fun next member => (existsTail next member).choose
      let coupling := step.bindOnSupport tail
      have leftLaw : coupling.map Prod.fst =
          (runtime setup).runInteractionPlan leaks players network
          ((actor :: rest).map ServiceInstruction.player) original := by
        rw [map_bindOnSupport]
        calc
          _ = step.bind (fun next => (runtime setup).runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) next.1) := by
            apply bindOnSupport_eq_bind_of_eq_on_support _
            intro next member
            exact (existsTail next member).choose_spec.1
          _ = _ := by
            refine (PMF.bind_map _ Prod.fst _).symm.trans ?_
            rw [first]
            simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
              PMF.pure_bind]
            rfl
      have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
          (actor :: rest).length repaired memory := by
        rw [map_bindOnSupport]
        calc
          _ = step.bind (fun next =>
              strategy.runJoint owner players scheduler rest.length next.2.1 next.2.2) := by
            apply bindOnSupport_eq_bind_of_eq_on_support _
            intro next member
            exact (existsTail next member).choose_spec.2.1
          _ = (step.map Prod.snd).bind (fun next =>
              strategy.runJoint owner players scheduler rest.length next.1 next.2) := by
            rw [PMF.bind_map]; rfl
          _ = _ := by rw [second]; rfl
      refine ⟨coupling, leftLaw, rightLaw, ?_⟩
      intro final supported
      have rightSupport : final.2 ∈ (strategy.runJoint owner players scheduler
          (actor :: rest).length repaired memory).support := by
        rw [← rightLaw, PMF.support_map]
        exact ⟨final, supported, rfl⟩
      refine ⟨menu.trace_implementation_runJoint (initialLaw setup)
        (rosterPlan setup rosters).length scheduler strategy owner players opponents own remaining
          (actor :: rest).length repaired memory trace final.2 rightSupport, ?_⟩
      obtain ⟨next, member, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
      exact (existsTail next member).choose_spec.2.2 final reached

end Vegas
