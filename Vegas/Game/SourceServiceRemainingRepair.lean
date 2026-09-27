/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEventRepair
import Vegas.Pending.ReactiveServiceAudit

/-! # Stopped repair through every remaining source event

The induction executes the existing service plan. It preserves both complete
marginal laws, the fixed repair implementation's private memory, and actual
retained-history reachability. Once a first departure is certified, its real
traffic or public omission evidence survives the arbitrary physical suffix.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
theorem frame_recall_length
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (memory : BindingMemory (runtime setup) leaks) (owner : Player)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired) :
    (original.recall owner).length = (repaired.recall owner).length := by
  rw [← frame.past, BindingMemory.restoreRecall, List.length_zipWith, ← frame.lengths]
  exact Nat.min_self _

omit [Fintype Player] in
theorem omission_plan_persistent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (plan : List (ServiceInstruction (graph setup))) (owner : Player)
    (original final : (application setup leaks).Execution)
    (missed : original.application.publicView.missedBindingBy owner = true)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network plan
      original).support) : final.application.publicView.missedBindingBy owner = true := by
  classical
  obtain ⟨event, owned, missing⟩ := of_decide_eq_true missed
  apply PublicView.missedBindingBy_of_event _ owner event owned
  cases shape : (graph setup).outputLayout event with
  | binding actor payload =>
      exact (runtime setup).runInteractionPlan_preserves leaks players network _
        (ReactiveApplication.Invariant.policyInvariant (application setup leaks)
          ((runtime setup).reactiveMissedBindingInvariant leaks event actor payload shape) players)
        plan original final missing reached
  | publicData payload =>
      simp only [PublicView.missedBinding, shape, Bool.false_eq_true] at missing
  | privateInput actor payload =>
      simp only [PublicView.missedBinding, shape, Bool.false_eq_true] at missing
  | publication payload =>
      simp only [PublicView.missedBinding, shape, Bool.false_eq_true] at missing

theorem remaining_events_stopped_coupling
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
    (onlyBindings : memory.shadow.OwnBindings owner)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (events : List (graph setup).EventId) (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + (events.flatMap (rosterBlock setup rosters)).length, none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ events.flatMap (rosterBlock setup rosters) ++
      after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (events.flatMap (rosterBlock setup rosters)) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network)
          (events.flatMap (rosterBlock setup rosters)).length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        next.2.2.shadow.OwnBindings owner ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
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
  have covered := BindingMemory.retainedImplementation_response_available
    (runtime setup) leaks menu owner reference (players owner)
  induction events generalizing original repaired memory before with
  | nil =>
      refine ⟨FinDist.pure (original, repaired, memory), ?_, ?_, ?_⟩
      · simp only [List.flatMap_nil, runInteractionPlan, FinDist.map_pure]
      · simp only [List.flatMap_nil, List.length_nil,
          ReactiveApplication.Implementation.runJoint, FinDist.map_pure]
      · intro next reached
        cases FinDist.mem_support_pure.mp reached
        exact ⟨⟨trace⟩, onlyBindings, Or.inr (Or.inr frame)⟩
  | cons event rest ih =>
      let block := rosterBlock setup rosters event
      let suffix := rest.flatMap (rosterBlock setup rosters)
      obtain ⟨step, first, second, related⟩ := event_block_stopped_coupling setup leaks bounds
        values capacity rosters opportunities network source target agrees owner policy
          available reference memory original repaired frame onlyBindings started leftRecall sound
            leftBinding event (remaining + suffix.length) (by
              have equal : remaining + suffix.length + block.length =
                  remaining + ((event :: rest).flatMap (rosterBlock setup rosters)).length := by
                simp only [List.flatMap_cons, List.length_append]
                dsimp only [suffix, block]
                omega
              rw [equal]
              exact trace)
            before (suffix ++ after)
            (by simpa only [List.flatMap_cons, List.append_assoc, block, suffix] using split)
            position
      have existsTail next (member : next ∈ step.support) :
          ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup)
            leaks),
            coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
              suffix next.1 ∧
            coupling.map Prod.snd = strategy.runJoint owner players scheduler suffix.length
              next.2.1 next.2.2 ∧
            ∀ final ∈ coupling.support,
              ((∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
                (runtime setup).permittedServiceEnvelope record.observation record.ledger
                  record.input.envelope = false) ∨
                final.1.application.publicView.missedBindingBy owner = true ∨
                BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1) := by
        by_cases bad : (∃ record ∈ app.executionTraffic next.1,
            record.input.envelope.sender = owner ∧
              (runtime setup).permittedServiceEnvelope record.observation record.ledger
                record.input.envelope = false) ∨
            next.1.application.publicView.missedBindingBy owner = true
        · let left := (runtime setup).runInteractionPlan leaks players network suffix next.1
          let right := strategy.runJoint owner players scheduler suffix.length next.2.1 next.2.2
          refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
            FinDist.map_snd_product .., ?_⟩
          intro final supported
          have reached : final.1 ∈ left.support := by
            rw [← FinDist.map_fst_product left right, FinDist.support_map]
            exact ⟨final, supported, rfl⟩
          rcases bad with ⟨record, present, authored, forbidden⟩ | missed
          · exact Or.inl ⟨record, ((runtime setup).executionTraffic_runInteractionPlan leaks
              players network suffix next.1 final.1 reached).subset present, authored, forbidden⟩
          · exact Or.inr (Or.inl (omission_plan_persistent setup leaks players network suffix
              owner next.1 final.1 missed reached))
        · have connected := related next member
          obtain ⟨nextTrace⟩ := connected.1
          have paired := (connected.2.resolve_left (fun traffic => bad (Or.inl
            traffic))).resolve_left
            (fun omission => bad (Or.inr omission))
          have leftSupport : next.1 ∈
              ((runtime setup).runInteractionPlan leaks players network block original).support :=
                by
            rw [← first, FinDist.support_map]
            exact ⟨next, member, rfl⟩
          have rightSupport : next.2 ∈
              (strategy.runJoint owner players scheduler block.length repaired memory).support := by
            rw [← second, FinDist.support_map]
            exact ⟨next, member, rfl⟩
          have nextMemory := BindingMemory.retainedImplementation_runJoint_ownBindings
            (runtime setup) leaks menu owner reference (players owner) players scheduler
              block.length
              repaired memory onlyBindings next.2 rightSupport
          have nextStarted : reference.length ≤ (next.2.1.recall owner).length := by
            have prefixRecall := (runtime setup).runInteractionPlan_recall_prefix leaks players
              network block original next.1 leftSupport owner
            have initialLength := frame_recall_length setup leaks memory owner original repaired
              frame
            have finalLength := frame_recall_length setup leaks next.2.2 owner next.1 next.2.1
              paired
            have monotone := prefixRecall.length_le
            omega
          have nextRecall := (runtime setup).runInteractionPlan_inputRecall leaks players network
            block original next.1 leftRecall leftSupport
          have soundInvariant : app.PolicyInvariant players
              (((runtime setup).packetEvidence leaks).Sound) := {
            respond := fun execution who response valid _ =>
              ((runtime setup).packetEvidence leaks).sound_respond execution who response valid
            environment := ((runtime setup).packetEvidence leaks).sound_environment }
          have nextSound := (runtime setup).runInteractionPlan_preserves leaks players network _
            soundInvariant block original next.1 sound leftSupport
          have nextBinding := (runtime setup).runInteractionPlan_preserves leaks players network _
            (ReactiveApplication.Invariant.policyInvariant app
              ((runtime setup).reactiveBindingInvariant leaks) players)
            block original next.1 leftBinding leftSupport
          have nextPosition : next.1.environmentRecall.length = (before ++ block).length := by
            rw [(runtime setup).runInteractionPlan_recall leaks players network block original
              next.1 leftSupport, position, List.length_append]
          obtain ⟨coupling, leftLaw, rightLaw, connected⟩ := ih next.2.2 next.1 next.2.1 paired
            nextMemory nextStarted nextRecall nextSound nextBinding nextTrace (before ++ block)
            (by simpa only [List.flatMap_cons, List.append_assoc, block, suffix] using split)
            nextPosition
          exact ⟨coupling, leftLaw, rightLaw, fun final supported =>
            (connected final supported).2.2⟩
      let tail := fun next member => (existsTail next member).choose
      let coupling := step.bindOnSupport tail
      have leftLaw : coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players
          network ((event :: rest).flatMap (rosterBlock setup rosters)) original := by
        rw [FinDist.map_bindOnSupport]
        calc
          _ = step.bind (fun next =>
              (runtime setup).runInteractionPlan leaks players network suffix next.1) := by
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro next member
            exact (existsTail next member).choose_spec.1
          _ = _ := by
            rw [← FinDist.bind_map, first, ← (runtime setup).runInteractionPlan_append]
            rfl
      have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
          ((event :: rest).flatMap (rosterBlock setup rosters)).length repaired memory := by
        rw [List.flatMap_cons, List.length_append,
          ReactiveApplication.Implementation.runJoint_add, FinDist.map_bindOnSupport]
        calc
          _ = step.bind (fun next => strategy.runJoint owner players scheduler suffix.length
              next.2.1 next.2.2) := by
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro next member
            exact (existsTail next member).choose_spec.2.1
          _ = (step.map Prod.snd).bind (fun next =>
              strategy.runJoint owner players scheduler suffix.length next.1 next.2) := by
            rw [FinDist.bind_map]
          _ = _ := by rw [second]
      refine ⟨coupling, leftLaw, rightLaw, ?_⟩
      intro final supported
      have reached : final.2 ∈ (strategy.runJoint owner players scheduler
          ((event :: rest).flatMap (rosterBlock setup rosters)).length repaired memory).support :=
            by
        rw [← rightLaw, FinDist.support_map]
        exact ⟨final, supported, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · exact menu.trace_implementation_runJoint (initialLaw setup)
          (rosterPlan setup rosters).length scheduler strategy owner players opponents
          (fun next past view response supported => covered next (past, view) response supported)
          remaining _ repaired memory trace final.2 reached
      · exact BindingMemory.retainedImplementation_runJoint_ownBindings (runtime setup) leaks menu
          owner reference (players owner) players scheduler _ repaired memory onlyBindings final.2
          reached
      · obtain ⟨next, member, tailSupport⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ supported)
        exact (existsTail next member).choose_spec.2.2 final tailSupport

end Vegas.SourceProgram.RevealService
