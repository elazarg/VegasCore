/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRepeatedWindow
import Vegas.Game.SourceServiceImplementationSegment
import Vegas.Pending.ReactiveRepeatedSubmissionData
import Vegas.Pending.ReactiveBindingForeignInclusion
import Vegas.Pending.ReactiveBindingFrameForeign

/-! # Protected settlement after a stopped repeated binding window

The first opaque envelope and its private repair are retained through every
remaining owner or foreign visit. The actual protected inclusion and clock
tail either preserve their joint frame or retain a real audit departure.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem repeated_binding_block_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (slot : CandidateSlot (graph setup)) (nonce : Nat)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (rightRecall : repaired.InputRecall (application setup leaks))
    (serials : original.network.SerialsBeforeNext)
    (repeated : original.network.nextSerial owner ≠
      original.network.ledger.countP (fun message => message.sender = owner))
    (granted : original.application.serviceGrant = some event)
    (recorded : (runtime setup).eventRecorded leaks (repaired.recall owner) event = true)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline (runtime setup) event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused (owner, slot))
    (leftFixed : original.application.candidates.lookup (owner, slot) ≠ .fresh)
    (rightFixed : repaired.application.candidates.lookup (owner, slot) ≠ .fresh)
    (aligned :
      (memory.shadow.actions event = some (cast (congrArg EventField.Action outputEq.symm)
          (original.application.bindingResult (owner, slot) payload)) ∧
        memory.shadow.values (.inr event) = some (cast (congrArg EventField.Value outputEq.symm)
          (original.application.bindingResult (owner, slot) payload)) ∧
        ∀ value, original.application.bindingResult (owner, slot) payload = .success value →
          repaired.application.bindingResult (owner, slot) payload = .success value) ∨
      (memory.shadow.actions event = none ∧ memory.shadow.values (.inr event) = none ∧
        repaired.application.bindingResult (owner, slot) payload =
          original.application.bindingResult (owner, slot) payload))
    (pending : (⟨(owner, nonce), ⟨.commitment event (owner, slot), none⟩⟩ :
      Message Player (WitnessedPacket (graph setup))) ∈ original.network.pending)
    (unpublished : (owner, nonce) ∉ original.network.ledger.map Message.id)
    (packets : original.network.Satisfies fun packet => packet.sender = owner →
      packet.id ∈ original.network.ledger.map Message.id ∨
        packet = ⟨(owner, nonce), ⟨.commitment event (owner, slot), none⟩⟩)
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner past view)
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player)
    (ticks : Nat)
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let ending : List (ServiceInstruction (graph setup)) :=
      .includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player ++ ending) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network)
          (visits.map ServiceInstruction.player ++ ending).length repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 := by
  classical
  intro app strategy ending
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, nonce), ⟨.commitment event (owner, slot), none⟩⟩
  let finish (execution : app.Execution) : app.Execution :=
    { execution.includePending app message.id with environmentRecall :=
      execution.environmentRecall ++ [⟨execution.observeEnvironment app, .include message.id⟩] }
  obtain ⟨window, first, second, related⟩ := repeated_roster_stopped_coupling setup leaks bounds
    rosters network players owner event memory original repaired frame reference started
    leftRecall rightRecall serials repeated granted recorded available before (ending ++ after)
    visits (by simpa only [ending, List.append_assoc] using split) position
  have leftReach (next) (supported : next ∈ window.support) :
      next.1 ∈ ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original).support := by
    rw [← first, PMF.support_map]
    exact ⟨next, supported, rfl⟩
  have includeLaw (execution : app.Execution)
      (selected : (runtime setup).reactiveLatest leaks event owner
        (execution.observeEnvironment app) = .include message.id) :
      (runtime setup).interactionStep leaks players network (.includeLatest event owner)
        execution = PMF.pure (finish execution) := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind]
    change app.dispatch players ((runtime setup).reactiveLatest leaks event owner
      (execution.observeEnvironment app)) execution = _
    rw [selected]
    change (execution.environmentStep app (.include message.id)).bind PMF.pure = _
    rw [PMF.bind_pure]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have existsTail (next) (supported : next ∈ window.support) :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst =
          (runtime setup).runInteractionPlan leaks players network ending next.1 ∧
        coupling.map Prod.snd =
          ((runtime setup).runInteractionPlan leaks players network ending next.2.1).map
            (fun final => (final, next.2.2)) ∧
        ∀ final ∈ coupling.support,
          (∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
          BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1 := by
    by_cases bad : ∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false
    · let leftLaw := (runtime setup).runInteractionPlan leaks players network ending next.1
      let rightLaw := ((runtime setup).runInteractionPlan leaks players network ending next.2.1).map
        fun final => (final, next.2.2)
      refine ⟨bindPairLaw leftLaw (fun _ => rightLaw), bindPairLaw_map_fst ..,
        FinDist.map_snd_product .., ?_⟩
      intro final member
      left
      obtain ⟨record, present, authored, rejected⟩ := bad
      refine ⟨record, ?_, authored, rejected⟩
      have reached : final.1 ∈ leftLaw.support := by
        rw [← bindPairLaw_map_fst leftLaw rightLaw, PMF.support_map]
        exact ⟨final, member, rfl⟩
      exact ((runtime setup).executionTraffic_runInteractionPlan leaks players network ending
        next.1 final.1 reached).subset present
    · obtain ⟨paired, shadow, rightView⟩ := (related next supported).resolve_left bad
      have clean : ∀ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner →
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = true := by
        intro record present authored
        cases value : (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope with
        | true => rfl
        | false => exact (bad ⟨record, present, authored, value⟩).elim
      obtain ⟨leftView, _, _, _, _, _⟩ := (runtime setup).repeated_window_clean_data leaks bounds
        players network owner _ (fun packet different same => (different same).elim) visits original
          next.1 packets leftRecall serials repeated available (leftReach next supported) clean
      have publicEq : next.1.application.publicView = original.application.publicView :=
        congrArg PlayerView.publicView leftView
      have leftCandidate : next.1.application.candidates.lookup (owner, slot) =
          original.application.candidates.lookup (owner, slot) :=
        congrFun (congrArg PlayerView.candidates leftView) slot
      have rightCandidate : next.2.1.application.candidates.lookup (owner, slot) =
          repaired.application.candidates.lookup (owner, slot) :=
        congrFun (congrArg PlayerView.candidates rightView) slot
      have leftResult : next.1.application.bindingResult (owner, slot) payload =
          original.application.bindingResult (owner, slot) payload := by
        unfold State.bindingResult
        rw [leftCandidate]
      have rightResult : next.2.1.application.bindingResult (owner, slot) payload =
          repaired.application.bindingResult (owner, slot) payload := by
        unfold State.bindingResult
        rw [rightCandidate]
      have readyNow : next.1.application.config.cut.Ready event := by
        rw [← State.publicView_eventReady, publicEq, State.publicView_eventReady]
        exact ready
      have timelyNow : next.1.application.WithinDeadline (runtime setup) event := by
        unfold State.WithinDeadline
        rw [show next.1.application.clock = original.application.clock from
          congrArg PublicView.clock publicEq,
          show next.1.application.activatedAt = original.application.activatedAt from
            congrArg PublicView.activatedAt publicEq]
        exact timely
      have accepted : next.1.application.accepted = original.application.accepted :=
        congrArg PublicView.accepted publicEq
      have vacantNow : next.1.application.accepted (.inr event) = none := by
        rw [accepted]
        exact vacant
      have unusedNow : next.1.application.HandleUnused (owner, slot) := by
        intro field associated
        exact unused field ((congrFun accepted field).symm.trans associated)
      have selection := (runtime setup).repeated_window_clean_selection leaks bounds players
        network owner original event message rfl rfl packets pending unpublished leftRecall serials
          repeated available visits next.1 (leftReach next supported) clean
      have included : BindingMemory.Frame (runtime setup) leaks next.2.2 owner
          (finish next.1) (finish next.2.1) := by
        rcases aligned with ⟨rememberedAction, rememberedValue, successful⟩ |
            ⟨noAction, noValue, sameResult⟩
        · exact paired.pending_binding_inclusion event payload outputEq codeEq node
            message.id (owner, slot) rfl rfl selection.2 readyNow timelyNow vacantNow unusedNow
            (by rwa [leftCandidate]) (by rwa [rightCandidate])
            (by rw [shadow, leftResult]; exact rememberedAction)
            (by rw [shadow, leftResult]; exact rememberedValue)
            (by intro value success; rw [leftResult] at success; rw [rightResult];
                exact successful value success)
        · exact paired.binding_inclusion_unmodified message.id event (owner, slot) owner payload
            outputEq codeEq node readyNow timelyNow rfl rfl vacantNow unusedNow
            (by rwa [leftCandidate]) (by rwa [rightCandidate])
            (by rw [leftResult, rightResult]; exact sameResult)
            (by rw [shadow]; exact noValue) (by rw [shadow]; exact noAction) none selection.2
      have completed : event ∈ (finish next.1).application.config.cut.completed := by
        have handled := (runtime setup).handle_commitment_eq next.1.application message.id event
          (owner, slot) owner payload outputEq codeEq node readyNow timelyNow rfl rfl vacantNow
            unusedNow
        simp only [finish, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, selection.2]
        change event ∈ (((runtime setup).handle next.1.application
          ⟨message.id, .commitment event (owner, slot)⟩).getD
            next.1.application).config.cut.completed
        rw [handled]
        exact Finset.mem_insert_self _ _
      obtain ⟨left, right, leftClock, rightClock, connected⟩ :=
        included.completed_clock_tail players network event completed ticks
      have leftLaw : (runtime setup).runInteractionPlan leaks players network ending next.1 =
          PMF.pure left := by
        change ((runtime setup).interactionStep leaks players network (.includeLatest event owner)
          next.1).bind _ = _
        rw [includeLaw next.1 selection.1, PMF.pure_bind]
        exact leftClock
      have rightLaw : (runtime setup).runInteractionPlan leaks players network ending next.2.1 =
          PMF.pure right := by
        change ((runtime setup).interactionStep leaks players network (.includeLatest event owner)
          next.2.1).bind _ = _
        have selected : (runtime setup).reactiveLatest leaks event owner
            (next.2.1.observeEnvironment app) = .include message.id := by
          rw [← paired.environment]
          exact selection.1
        rw [includeLaw next.2.1 selected, PMF.pure_bind]
        exact rightClock
      refine ⟨PMF.pure (left, right, next.2.2), ?_, ?_, ?_⟩
      · rw [PMF.pure_map, leftLaw]
      · rw [PMF.pure_map, rightLaw, PMF.pure_map]
      · intro final member
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact Or.inr connected
  let tail := fun next supported => (existsTail next supported).choose
  refine ⟨window.bindOnSupport tail, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    calc
      _ = window.bind (fun next =>
          (runtime setup).runInteractionPlan leaks players network ending next.1) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro next supported
        exact (existsTail next supported).choose_spec.1
      _ = (window.map Prod.fst).bind
          ((runtime setup).runInteractionPlan leaks players network ending) :=
        (PMF.bind_map ..).symm
      _ = _ := by rw [first, ← (runtime setup).runInteractionPlan_append]
  · rw [roster_runJoint_append_reserved setup leaks rosters network strategy owner players
      before (visits.map ServiceInstruction.player) ending after split
      (by simp [ending]) repaired memory (by rw [← frame.service]; exact position),
      List.length_map, map_bindOnSupport]
    calc
      _ = window.bind (fun next =>
          ((runtime setup).runInteractionPlan leaks players network ending next.2.1).map
            fun final => (final, next.2.2)) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro next supported
        exact (existsTail next supported).choose_spec.2.1
      _ = (window.map Prod.snd).bind (fun next =>
          ((runtime setup).runInteractionPlan leaks players network ending next.1).map
            fun final => (final, next.2)) := by rw [PMF.bind_map]
      _ = _ := by rw [second]
  · intro final member
    obtain ⟨next, supported, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
    exact (existsTail next supported).choose_spec.2.2 final reached

end Vegas
