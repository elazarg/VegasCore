/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceStoppedBindingWindow
import Vegas.Game.SourceServiceResolutionBlock
import Vegas.Game.SourceServiceSampleRepair
import Vegas.Game.SourceServiceForeignBindingRepair
import Vegas.Game.SourceServiceGrantSupport

/-! # Composing the actual service blocks in private continuation repair

The binding entry below follows the real foreign window to the first owner
opportunity, then uses the stopped repeated-binding window. All laws retain
the same implementation memory and the same opponent policies.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem foreign_roster_recall
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (owner : Player)
    (visits : List Player) (absent : owner ∉ visits)
    (original final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) original).support) :
    final.recall owner = original.recall owner := by
  let app := application setup leaks
  induction visits generalizing original with
  | nil => cases FinDist.mem_support_pure.mp reached; rfl
  | cons actor rest ih =>
      obtain ⟨middle, moved, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      rw [ih (fun member => absent (List.mem_cons_of_mem _ member)) middle continued]
      simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at moved
      change middle ∈ (app.dispatch players (.activate actor) original).support at moved
      obtain ⟨activated, sampled, resumed⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
      obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ resumed
      rw [app.respond_recall_other activated actor owner
        (fun same => absent (by simp only [same, List.mem_cons_self])) response,
        app.environmentStep_recall original activated (.activate actor) sampled]

omit [DecidableEq Player] [Fintype Player] in
private theorem split_owner (owner : Player) (visits : List Player) (member : owner ∈ visits) :
    ∃ earlier later, visits = earlier ++ owner :: later ∧ owner ∉ earlier := by
  classical
  induction visits with
  | nil => cases member
  | cons actor rest ih =>
      by_cases same : actor = owner
      · subst actor
        exact ⟨[], rest, rfl, List.not_mem_nil⟩
      · obtain ⟨earlier, later, split, absent⟩ := ih
          (List.mem_of_ne_of_mem (Ne.symm same) member)
        exact ⟨actor :: earlier, later, congrArg (List.cons actor) split,
          by simpa only [List.mem_cons, not_or] using And.intro (Ne.symm same) absent⟩

theorem binding_phase_stopped_coupling
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
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (granted : repaired.application.serviceGrant = some event)
    (unsent : (runtime setup).eventRecorded leaks (repaired.recall owner) event = false)
    (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + (rosters event).length + ((runtime setup).deadline event + 2),
          none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ (rosters event).map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ((runtime setup).deadline event) .tick ++
        [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length)
    (phase : before.length = (rosterPlanPrefix setup rosters event.val).length + 1) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let ending : List (ServiceInstruction (graph setup)) :=
      .includeLatest event owner :: List.replicate ((runtime setup).deadline event) .tick ++
        [.expire event]
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        ((rosters event).map ServiceInstruction.player ++ ending) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network)
          ((rosters event).map ServiceInstruction.player ++ ending).length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBinding event = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players strategy ending
  let scheduler := rosterScheduler setup leaks rosters network
  obtain ⟨foreign, rest, roster, absent⟩ := split_owner owner (rosters event)
    (opportunities event owner payload outputEq)
  let suffix := rest.map ServiceInstruction.player ++ ending
  let rank := remaining + rest.length + ((runtime setup).deadline event + 2)
  have suffixLength : suffix.length = rest.length + 1 + (runtime setup).deadline event + 1 := by
    simp only [suffix, ending, List.length_append, List.length_map, List.length_cons,
      List.length_replicate, List.length_nil]
    omega
  have arranged : rosterPlan setup rosters = before ++
      foreign.map ServiceInstruction.player ++ (.player owner :: suffix) ++ after := by
    simpa only [roster, suffix, ending, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append] using split
  obtain ⟨window, first, second, related⟩ := repair_next_owner_opportunity setup leaks bounds
    rosters network source target agrees owner policy reference memory original repaired frame
      rank foreign absent (by
        have same : rank + 1 + foreign.length = remaining + (rosters event).length +
            ((runtime setup).deadline event + 2) := by
          simp only [rank, roster, List.length_append, List.length_cons]
          omega
        rw [same]
        exact trace)
      before (suffix ++ after) (by simpa only [List.append_assoc, List.cons_append,
        List.nil_append] using arranged)
        position
  have existsTail next (member : next ∈ window.support) :
      ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = (app.invoke players owner next.1).bind
          ((runtime setup).runInteractionPlan leaks players network suffix) ∧
        coupling.map Prod.snd =
          (strategy.resume owner players (some owner) next.2.1 next.2.2).bind
            (fun middle => strategy.runJoint owner players scheduler suffix.length
              middle.1 middle.2) ∧
        ∀ final ∈ coupling.support,
          Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
            (rosterPlan setup rosters).length scheduler).Trace
              (some ⟨rank - (rest.length + 1 + (runtime setup).deadline event + 1),
                none, final.2.1⟩)) ∧
          ((∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
            final.1.application.publicView.missedBinding event = true ∨
            BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1) := by
    obtain ⟨paired, sameMemory, nextTrace, prior, priorSupport, sampled⟩ := related next member
    obtain ⟨nextTrace⟩ := nextTrace
    have priorRecall := foreign_roster_recall setup leaks players network owner foreign absent
      original prior priorSupport
    have currentRecall := app.environmentStep_recall prior next.1 (.activate owner) sampled
    have nextUnsent : (runtime setup).eventRecorded leaks (next.2.1.recall owner) event = false :=
      by
      rw [← (runtime setup).eventRecorded_congr leaks _ _ paired.submissions event,
        currentRecall, priorRecall,
        (runtime setup).eventRecorded_congr leaks _ _ frame.submissions event]
      exact unsent
    have nextStarted : reference.length ≤ (next.2.1.recall owner).length := by
      rw [paired.lengths, sameMemory, ← frame.lengths]
      exact started
    have recalled := app.environment_inputRecall prior next.1 (.activate owner)
      ((runtime setup).runInteractionPlan_inputRecall leaks players network
        (foreign.map ServiceInstruction.player) original prior leftRecall priorSupport) sampled
    have priorPublic := ((runtime setup).player_window_application leaks players network foreign
      original prior priorSupport).2
    have currentPublic : next.1.application.publicView = prior.application.publicView := by
      rw [ReactiveApplication.Execution.activation_samples] at sampled
      obtain ⟨observed, _, equal⟩ := FinDist.support_map .. ▸ sampled
      rw [← equal]
      rfl
    have nextGrant : next.2.1.application.serviceGrant = some event :=
      (congrArg PublicView.serviceGrant paired.publicView).symm.trans
        ((congrArg PublicView.serviceGrant currentPublic).trans
          ((congrArg PublicView.serviceGrant priorPublic).trans
            ((congrArg PublicView.serviceGrant frame.publicView).trans granted)))
    have currentPosition : next.1.environmentRecall.length = before.length + foreign.length + 1 :=
      by
        have priorPosition := (runtime setup).runInteractionPlan_recall leaks players network
          (foreign.map ServiceInstruction.player) original prior priorSupport
        obtain ⟨raw, _, equal⟩ := FinDist.support_map .. ▸ sampled
        rw [← equal]
        simp only [List.length_append, List.length_singleton, priorPosition,
          List.length_map, position]
    simpa only [suffixLength] using binding_window_stopped_coupling setup leaks bounds values
      capacity rosters opportunities
      network source target agrees owner policy available reference event payload outputEq
        codeEq node rank prior next.1 next.2.1 sampled next.2.2 paired nextTrace nextStarted
          recalled
        nextGrant nextUnsent foreign rest roster
        (by rw [currentPosition, phase])
        (before ++ foreign.map ServiceInstruction.player ++ [.player owner]) after
        (by simpa only [suffix, ending, List.append_assoc, List.singleton_append,
          List.cons_append, List.nil_append] using arranged)
        (by rw [currentPosition]; simp only [List.length_append, List.length_map,
          List.length_singleton]) (by dsimp only [rank]; omega)
  let tail := fun next member => (existsTail next member).choose
  let coupling := window.bindOnSupport tail
  have leftLaw : coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
      ((rosters event).map ServiceInstruction.player ++ ending) original := by
    rw [FinDist.map_bindOnSupport]
    calc
      _ = window.bind (fun next => (app.invoke players owner next.1).bind
          ((runtime setup).runInteractionPlan leaks players network suffix)) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.1
      _ = (window.map Prod.fst).bind (fun execution => (app.invoke players owner execution).bind
          ((runtime setup).runInteractionPlan leaks players network suffix)) := by
        rw [FinDist.bind_map]
      _ = _ := by
        rw [first, FinDist.bind_bind, roster, List.map_append, List.map_cons,
          List.append_assoc, (runtime setup).runInteractionPlan_append]
        apply FinDist.bind_congr
        intro prior _
        change _ = ((runtime setup).interactionStep leaks players network (.player owner)
          prior).bind ((runtime setup).runInteractionPlan leaks players network suffix)
        simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
          ReactiveApplication.resume, FinDist.bind_bind]
        rfl
  have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
      ((rosters event).map ServiceInstruction.player ++ ending).length repaired memory := by
    have length : ((rosters event).map ServiceInstruction.player ++ ending).length =
        (foreign.map (ServiceInstruction.player (graph := graph setup))).length + 1 +
          suffix.length := by
      simp only [roster, List.length_append, List.length_map, List.length_cons, suffix]
      omega
    rw [length, roster_runJoint_at_owner setup leaks rosters network strategy owner players before
      (foreign.map ServiceInstruction.player) suffix after arranged repaired memory
      (by rw [← frame.service]; exact position), FinDist.map_bindOnSupport]
    calc
      _ = window.bind (fun next => (strategy.resume owner players (some owner) next.2.1
        next.2.2).bind
          (fun middle => strategy.runJoint owner players scheduler suffix.length middle.1
            middle.2)) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.2.1
      _ = (window.map Prod.snd).bind (fun next =>
          (strategy.resume owner players (some owner) next.1 next.2).bind (fun middle =>
            strategy.runJoint owner players scheduler suffix.length middle.1 middle.2)) := by
        rw [FinDist.bind_map]
      _ = _ := by
        rw [second, FinDist.bind_bind]
        simp only [FinDist.bind_map, List.length_map]
        rfl
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro final supported
  obtain ⟨next, member, reached⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ supported)
  have connected := (existsTail next member).choose_spec.2.2 final reached
  have finished : rank - (rest.length + 1 + (runtime setup).deadline event + 1) = remaining := by
    dsimp only [rank]
    omega
  exact ⟨finished ▸ connected.1, connected.2⟩

end Vegas.SourceProgram.RevealService
