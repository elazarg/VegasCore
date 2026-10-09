/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceContract
import Vegas.Examples.LateOpeningRuntimeReadout
import Vegas.Pending.ReactiveCanonicalResolution
import Interaction.ReactivePassiveContinuation
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveMonitoring
import Interaction.ReactiveRawRoundTrace

/-! # The final truthful response in the late-opening native game

At the final Bob callback a ready, timely opening of a successfully bound
answer receives actual immediate service. The remaining scheduler commands are
passive, so all future policies retain the accepted answer and receipt. These
are operational facts about legal raw histories, not equilibrium assumptions.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobService

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
  rw [PMF.map_comp]
  rfl

abbrev bobChecks : List (GuardCheck nativeGraph.layout (.range 0 5)) :=
  match (show EventCode nativeGraph.layout (.publication (.range 0 5)) from
    nativeGraph.nodes bobRevealEvent) with
  | .resolve _ _ _ checks => checks

theorem bob_checks_accept (store : Store nativeGraph.layout) (answer : Answer) :
    GuardCheck.allAccepted? bobChecks store (.success answer) = some true := rfl

/-- The last native callback leaves exactly the six final scheduler rounds. -/
theorem final_cursor (weight : ℝ) (nonnegative : 0 ≤ weight) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨6, some bob, execution⟩)) : execution.environmentRecall.length = 20 := by
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change execution.environmentRecall.length + 6 = 26 at accounted
  omega

/-- Every scheduler command after the final Bob activation is passive. -/
theorem final_passive (weight : ℝ) (nonnegative : 0 ≤ weight)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (later : 20 ≤ past.length) (command : app.Command)
    (selected : command ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative past view).support) :
    command.actor? app = none := by
  change command ∈ (stageChoice weight nonnegative past.length view).support at selected
  generalize located : past.length = position at later selected
  by_cases inside : position < 26
  · interval_cases position
    all_goals simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    case «20» =>
      rw [selected]
      exact (latestAuthor_passive bob view).1
    all_goals subst command; rfl
  · have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    subst command
    rfl

/-- The physical terminal suffix adds no further authored envelopes. -/
theorem final_preserves_inputs (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution final : app.Execution)
    (later : 20 ≤ execution.environmentRecall.length)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : final.network.inputs = execution.network.inputs :=
  (app.passive_continuation_preserves_traffic
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20
    (final_passive weight nonnegative) players count execution final later reached).2

def openingPacket (candidate : Handle nativeGraph) (answer : Answer) :
    WitnessedPacket nativeGraph :=
  ⟨.opening bobRevealEvent candidate ⟨.range 0 5, answer⟩,
    some ⟨candidate, ⟨.range 0 5, answer⟩⟩, some ⟨bobRevealEvent⟩⟩

def openingMessage (execution : app.Execution) (candidate : Handle nativeGraph)
    (answer : Answer) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(bob, execution.network.nextSerial bob), openingPacket candidate answer⟩

/-- Actual canonical normalization emits the binding's certified answer, and
the application accepts it at every ready and timely Bob disclosure callback. -/
theorem canonical_response (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobRevealEvent) :
    ∃ candidate material,
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (execution.recall bob)
        (execution.observe app bob) bobRevealEvent true = ⟨some material⟩ ∧
      app.submit execution.application bob material = execution.application ∧
      app.packet (app.submit execution.application bob material) bob
        (execution.network.known bob) material = openingPacket candidate answer ∧
      ∃ next : EventGraphRuntime.State nativeGraph,
        app.handle (app.submit execution.application bob material)
          (openingMessage execution candidate answer) = some next ∧
        next.config.store (.inr bobRevealEvent) = some (.success answer) := by
  have aligned : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph))) LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨remaining, some bob, execution⟩) := by
    rwa [initial_law_eq]
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) aligned
  obtain ⟨candidate, associated, owned, fixed⟩ := valid.success_provenance bobBinding answer bound
  have resolved : EventCode.resolveOutput? bobBinding bobChecks true
      execution.application.config.store =
      some (.success answer) := by
    simp only [EventCode.resolveOutput?, show bobBinding.get? execution.application.config.store =
      some (.success answer) from bound, ↓reduceIte]
    exact congrArg
      (fun accepted : Option Bool => accepted.bind fun good =>
        some (if good then PublicationResult.success answer else .failure))
      (bob_checks_accept execution.application.config.store answer)
  have validated : EventCode.resolveOutput? bobBinding bobChecks true
      (execution.observe app bob).application.observation.store = some (.success answer) := by
    change EventCode.resolveOutput? bobBinding bobChecks true
      (nativeGraph.playerStore bob execution.application.config.store) = _
    rwa [EventCode.resolveOutput?_playerStore]
  obtain ⟨material, decision, emitted⟩ :=
    LateOpeningRuntimeService.runtime.history_canonicalServiceDecision_resolution_validated leaks
      (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) aligned
      bob bobRevealEvent (.range 0 5) bobBinding bobChecks rfl rfl rfl candidate answer validated
      associated owned
  rw [execution.application.publicView_tokenFor_of_ready _ bobRevealEvent rfl ready] at emitted
  change app.packet (app.submit execution.application bob material) bob
    (execution.network.known bob) material = openingPacket candidate answer at emitted
  have call : material.call.packet = .opening bobRevealEvent candidate ⟨.range 0 5, answer⟩ :=
    congrArg WitnessedPacket.call emitted
  have unchanged : app.submit execution.application bob material = execution.application := by
    rcases material with ⟨⟨packet, opening⟩, evidence⟩
    dsimp only at call
    subst packet
    cases opening <;> rfl
  let next := execution.application.complete bobRevealEvent ready true (.success answer)
  refine ⟨candidate, material, decision, unchanged, emitted, next, ?_, ?_⟩
  · rw [unchanged, reactiveApplication_handle_of_tokenValid LateOpeningRuntimeService.runtime
      leaks _ _ (by rfl)]
    exact LateOpeningRuntimeService.runtime.handle_opening_eq execution.application _
      bobRevealEvent candidate bob (.range 0 5) bobBinding bobChecks rfl rfl rfl ready timely rfl
      owned associated answer fixed bound (.success answer) resolved
  · change next.config.outputs bobRevealEvent = _
    simp [next, EventGraphRuntime.State.complete, Config.complete]

/-- The guard-free certified answer is permanently permitted once accepted. -/
theorem opening_permitted (execution : app.Execution) (candidate : Handle nativeGraph)
    (answer : Answer) (record : SettledRecord nativeGraph)
    (accepted : ((openingMessage execution candidate answer).id, true) ∈ record.receipts) :
    record.permits (openingMessage execution candidate answer) = true := by
  apply SettledRecord.permits_of_accepted record _ bobRevealEvent rfl accepted
  refine ⟨by simp [openingMessage, openingPacket, certifiedOpening], ?_⟩
  exact (record.view.openingGuardsAccepted_iff bob bobRevealEvent (.range 0 5) bobBinding bobChecks
    rfl rfl rfl candidate ⟨.range 0 5, answer⟩
      (some ⟨candidate, ⟨.range 0 5, answer⟩⟩)).mpr
        ⟨answer, rfl, bob_checks_accept _ answer⟩

/-- The actual next author service accepts the canonical answer with
probability one, even after arbitrary earlier raw responses. -/
theorem canonical_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobRevealEvent) :
    ∃ candidate material next,
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (execution.recall bob)
        (execution.observe app bob) bobRevealEvent true = ⟨some material⟩ ∧
      app.packet (app.submit execution.application bob material) bob
        (execution.network.known bob) material = openingPacket candidate answer ∧
      app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (execution.respond app bob ⟨some material⟩) = PMF.pure next ∧
      next.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      ((openingMessage execution candidate answer).id, true) ∈ next.receipts := by
  obtain ⟨candidate, material, decision, _unchanged, emitted, state, accepted, output⟩ :=
    canonical_response weight nonnegative remaining execution trace answer bound ready timely
  let submitted := execution.respond app bob ⟨some material⟩
  let identifier := (openingMessage execution candidate answer).id
  let included := submitted.includePending app identifier
  let next : app.Execution := { included with environmentRecall :=
    submitted.environmentRecall ++ [⟨submitted.observeEnvironment app, .include identifier⟩] }
  have serials := (app.messageIdentityInvariant
    (LateOpeningRuntimeService.scheduler weight nonnegative)).history initial
      LateOpeningRuntimeService.horizon
      (by intro state _; exact ⟨MessageNetwork.SerialsBeforeNext.empty,
        MessageNetwork.UniqueIds.empty⟩) trace
  have selected := latestAuthor_after_submit execution bob material serials.1
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative submitted.environmentRecall
      (submitted.observeEnvironment app) = PMF.pure (.include identifier) := by
    exact (protected_response_scheduler weight nonnegative
      ⟨remaining, some bob, execution⟩ trace bob rfl ⟨some material⟩ (Or.inl rfl)).trans
        (congrArg PMF.pure selected)
  have actual : app.handle submitted.application (openingMessage execution candidate answer) =
      some state := accepted
  have found : submitted.network.lookup identifier =
      some (openingMessage execution candidate answer) := by
    change (execution.network.submit bob
      (app.packet (app.submit execution.application bob material) bob
        (execution.network.known bob) material)).2.lookup
          (bob, execution.network.nextSerial bob) = _
    rw [serials.1.lookup_submit, emitted]
    rfl
  have pending : included.application = state := by
    change (submitted.includePending app identifier).application = state
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (app.handle submitted.application (openingMessage execution candidate answer)).getD _ = _
    rw [actual]
    rfl
  have receipt : (identifier, true) ∈ next.receipts := by
    change (identifier, true) ∈ (submitted.includePending app identifier).receipts
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (identifier, true) ∈ submitted.receipts ++
      [(identifier,
        (app.handle submitted.application (openingMessage execution candidate answer)).isSome)]
    rw [actual]
    simp
  refine ⟨candidate, material, next, decision, emitted, ?_, ?_, receipt⟩
  · rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  · change included.application.config.store _ = _
    rw [pending]
    exact output

/-- Canonical final publication retains the accepted answer, its receipt and
exact authored traffic throughout the physical terminal continuation. -/
theorem canonical_terminal (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨6, some bob, execution⟩))
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobRevealEvent) :
    ∃ candidate material,
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (execution.recall bob)
        (execution.observe app bob) bobRevealEvent true = ⟨some material⟩ ∧
      ∀ (players : Player → app.Policy) final,
        final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 6
          (execution.respond app bob ⟨some material⟩)).support →
        final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
        ((openingMessage execution candidate answer).id, true) ∈ final.receipts ∧
        final.network.inputs = execution.network.inputs ++
          [(show Message Player app.Payload from openingMessage execution candidate answer)] := by
  obtain ⟨candidate, material, next, decision, emitted, moved, published, accepted⟩ :=
    canonical_round weight nonnegative (fun _ => app.silentPolicy) 6 execution trace answer
      bound ready timely
  refine ⟨candidate, material, decision, ?_⟩
  intro players final reached
  have rawReached := reached
  have cursor := final_cursor weight nonnegative execution trace
  have later : 20 ≤ (execution.respond app bob ⟨some material⟩).environmentRecall.length := by
    rw [app.respond_environmentRecall, cursor]
  have independent := app.passive_continuation_policy_independent
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20
    (final_passive weight nonnegative) players (fun _ => app.silentPolicy) 6 _ later
  rw [independent, ReactiveApplication.runRounds] at reached
  obtain ⟨first, firstReached, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [moved, PMF.mem_support_pure_iff] at firstReached
  subst first
  have retained := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
      (.success answer)) (fun _ => app.silentPolicy)).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 5 next final published continued
  have receipt := (app.receipt_policyInvariant (fun _ => app.silentPolicy)
    ((openingMessage execution candidate answer).id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 5 next final accepted continued
  have inputs := final_preserves_inputs weight nonnegative players 6 _ final later rawReached
  refine ⟨retained, receipt, inputs.trans ?_⟩
  change (execution.network.submit bob
    (app.packet (app.submit execution.application bob material) bob
      (execution.network.known bob) material)).2.inputs = _
  rw [emitted]
  rfl

end Vegas.Examples.LateOpeningRuntimeBobService
