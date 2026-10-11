/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy
import Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix
import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation
import Interaction.ReactivePolicyInvariant

/-! # Clean protected binding and source-canonical publication continuations

At the genuine first ready Bob callback, the existing source-canonical policy
binds the chosen answer. Arbitrary future Alice play and actual pending samples
preserve its protected opening opportunity. The complete supported continuation
publishes that answer with zero Bob audit charge for every authentic sampler.
On the already-successful Alice branch, choosing Safe attains exactly two fifths.
These are continuation laws and payoff attainment, not optimality or equilibrium.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation

open Interaction SourceProgram Vegas Vegas.EventGraph Vegas.EventGraphRuntime
open GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService

private theorem completed_of_store (execution : app.Execution)
    (event : nativeGraph.EventId) (value : (nativeGraph.outputLayout event).Value)
    (stored : execution.application.config.store (.inr event) = some value) :
    event ∈ execution.application.config.cut.completed := by
  apply (execution.application.config.output_available event).mp
  rw [← EventGraph.Config.store_output, stored]
  rfl

/-- Once the canonical answer is published, every subsequent supported native
continuation keeps the typed answer and adds no Bob-authored envelopes. -/
theorem after_opening (answer : Answer) (players : Player → app.Policy)
    (bobPolicy : players bob = serviceCanonicalPolicy setup .sequential deadline leaks
      (constantProfile true answer true) bob)
    (schedule : app.Scheduler) (execution final : app.Execution) (count : Nat)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (opened : execution.application.config.store (.inr bobRevealEvent) = some (.success answer))
    (reached : final ∈ (app.runRounds schedule players count execution).support) :
    final.application.config.store (.inr bobBindEvent) = some (.success answer) ∧
      final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      ∀ message ∈ final.network.inputs, message.sender = bob →
        message ∈ execution.network.inputs := by
  let predicate := fun next : app.Execution =>
    next.application.config.store (.inr bobBindEvent) = some (.success answer) ∧
      next.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      ∀ message ∈ next.network.inputs, message.sender = bob →
        message ∈ execution.network.inputs
  have invariant : app.PolicyInvariant players predicate := by
    constructor
    · intro before who action valid supported
      refine ⟨(LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobBindEvent)
        (.success answer)).respond before who action valid.1,
        (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
          (.success answer)).respond before who action valid.2.1, ?_⟩
      by_cases same : who = bob
      · subst who
        have silent := LateOpeningRuntimeProtectedBobPolicy.canonical_silent_after_completed
          answer before (completed_of_store before bobBindEvent _ valid.1)
          (completed_of_store before bobRevealEvent _ valid.2.1)
        rw [bobPolicy, silent, PMF.mem_support_pure_iff] at supported
        subst action
        exact valid.2.2
      · intro message member author
        rcases action with ⟨transmission⟩
        cases transmission with
        | none => exact valid.2.2 message member author
        | some material =>
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
            List.mem_append, List.mem_singleton] at member
          rcases member with prior | rfl
          · exact valid.2.2 message prior author
          · exact False.elim (same author)
    · intro before next command valid moved
      refine ⟨(LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobBindEvent)
        (.success answer)).environmentStep before next command valid.1 moved,
        (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
          (.success answer)).environmentStep before next command valid.2.1 moved, ?_⟩
      intro message member author
      rw [app.environmentStep_inputs before next command moved] at member
      exact valid.2.2 message member author
  exact invariant.runRounds _ count execution final
    ⟨bound, opened, by intro message member _; exact member⟩ reached

/-- A ready clock-three canonical opening followed by the same source policy
settles the chosen answer with zero Bob charge under any authentic audit sampler. -/
theorem opening_continuation_clean (weight : ℝ) (nonnegative : 0 ≤ weight)
    (answer : Answer) (players : Player → app.Policy)
    (bobPolicy : players bob = serviceCanonicalPolicy setup .sequential deadline leaks
      (constantProfile true answer true) bob)
    (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
    (clean : LateOpeningRuntimeBobAudit.CleanBindings execution)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob
        (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
          (execution.recall bob) (execution.observe app bob) bobRevealEvent true))).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample)
          (app.finished final) bob = 0 := by
  obtain ⟨candidate, material, served, decision, emitted, law, published, accepted⟩ :=
    LateOpeningRuntimeBobService.canonical_round weight nonnegative players 14 execution trace
      answer bound ready timely
  rw [decision] at reached
  have whole := reached
  obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [law, PMF.mem_support_pure_iff] at moved
  subst middle
  have servedReached : served ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players (execution.respond app bob ⟨some material⟩)).support := by
    rw [law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob ⟨some material⟩ trace
  obtain ⟨servedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 13 _ served
      respondedTrace servedReached
  obtain ⟨bit, label, valid⟩ := LateOpeningRuntimeReadout.history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨13, none, served⟩ servedTrace
  have servedBound := LateOpeningRuntimeReadout.bob_success_from_binding served.application
    _ valid.reachable answer published
  obtain ⟨finalBound, finalPublished, prior⟩ := after_opening answer players bobPolicy
    (LateOpeningRuntimeService.scheduler weight nonnegative) served final 13 servedBound
      published continued
  have finalAccepted := (app.receipt_policyInvariant players
    ((LateOpeningRuntimeBobService.openingMessage execution candidate answer).id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 13 served final accepted continued
  have inputs : served.network.inputs = execution.network.inputs ++
      [(show Message Player app.Payload from
        LateOpeningRuntimeBobService.openingMessage execution candidate answer)] := by
    rw [LateOpeningRuntimeBobSafeContinuation.protected_round_inputs weight nonnegative
      14 execution trace ⟨some material⟩ players served servedReached]
    change execution.network.inputs ++ [⟨(bob, execution.network.nextSerial bob),
      app.packet (app.submit execution.application bob material) bob
        (execution.network.known bob) material⟩] = _
    rw [emitted]
    rfl
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final
      respondedTrace whole
  refine ⟨finalPublished, LateOpeningRuntimeBobAudit.charge_zero weight nonnegative
    ⟨0, none, final⟩ finalTrace answer finalBound execution candidate finalAccepted
      ?_ sample authentic⟩
  intro message member owner
  have earlier := prior message member owner
  rw [inputs, List.mem_append, List.mem_singleton] at earlier
  rcases earlier with old | rfl
  · obtain ⟨token, content, receipt⟩ := clean message old owner
    refine Or.inl ⟨token, content, ?_⟩
    exact (app.receipt_policyInvariant players (message.id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 14
        (execution.respond app bob ⟨some material⟩) final receipt whole
  · exact Or.inr rfl

/-- The actual first protected binding and source-canonical continuation settle
any chosen answer without Bob audit charge, despite arbitrary future Alice play. -/
theorem binding_continuation_clean (weight : ℝ) (nonnegative : 0 ≤ weight)
    (answer : Answer) (players : Player → app.Policy)
    (bobPolicy : players bob = serviceCanonicalPolicy setup .sequential deadline leaks
      (constantProfile true answer true) bob)
    (execution final : app.Execution) (response : app.Action)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (responseSupported : response ∈
      (players bob (execution.recall bob) (execution.observe app bob)).support)
    (reached : final ∈ (app.runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 21
        (execution.respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample)
          (app.finished final) bob = 0 := by
  rw [bobPolicy, LateOpeningRuntimeProtectedBobPolicy.canonical_binding weight nonnegative
    answer 21 execution trace quiet ready, PMF.mem_support_pure_iff] at responseSupported
  subst response
  obtain ⟨bound, binding, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨served, service, value, _, openingReady, _, clean, _⟩ :=
    LateOpeningRuntimeBobBindingService.binding_round weight nonnegative 21 execution trace
      quiet ready timely answer
  rw [service players, PMF.mem_support_pure_iff] at binding
  subst bound
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 execution bob
      (LateOpeningRuntimeBobSuffix.binding answer) trace
  obtain ⟨servedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 20 _ served respondedTrace
      (by rw [service players]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 5 15] at rest
  obtain ⟨after, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  obtain ⟨afterTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 15 5 served after
      servedTrace prefixReached
  have cursor : after.environmentRecall.length = 11 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) afterTrace
    change after.environmentRecall.length + 15 = 26 at counted
    omega
  obtain ⟨next, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffixReached)
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  change command ∈ (LateOpeningRuntimeService.stageChoice weight nonnegative
    after.environmentRecall.length (after.observeEnvironment app)).support at selected
  rw [cursor] at selected
  change command ∈ (PMF.pure (.activate bob : app.Command)).support at selected
  cases (PMF.mem_support_pure_iff _ _).mp selected
  obtain ⟨observed, sampled, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨⟨observedTrace⟩, configEq, observedClean, observedReady, observedTimely, _⟩ :=
    LateOpeningRuntimeProtectedBobPrefix.opening_callback_after_binding weight nonnegative
      players served after observed servedTrace openingReady clean prefixReached sampled
  have observedValue : observed.application.config.store (.inr bobBindEvent) =
      some (.success answer) := configEq ▸ value
  change next ∈ ((players bob (observed.recall bob) (observed.observe app bob)).map
    (observed.respond app bob)).support at resumed
  rw [bobPolicy, LateOpeningRuntimeProtectedBobPolicy.canonical_opening answer observed
    observedReady, PMF.pure_map, PMF.mem_support_pure_iff] at resumed
  subst next
  exact opening_continuation_clean weight nonnegative answer players bobPolicy observed final
    observedTrace observedValue observedReady observedTimely observedClean
      sample authentic continued

/-- On the actual already-published branch, the source-canonical Safe comparator
attains exactly two fifths, with no reward, forfeit or deposit restrictions. -/
theorem safe_continuation_payoff (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (bobPolicy : players bob = serviceCanonicalPolicy setup .sequential deadline leaks
      (constantProfile true safe true) bob)
    (execution final : app.Execution) (response : app.Action)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (publishedBit : Bool)
    (alicePublished : execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit))
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (responseSupported : response ∈
      (players bob (execution.recall bob) (execution.observe app bob)).support)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 21 (execution.respond app bob response)).support) :
    LateOpeningRuntimeGame.payoff reward forfeit sample deposit
      (app.finished final) bob = 2 / 5 := by
  obtain ⟨published, clear⟩ := binding_continuation_clean weight nonnegative safe players bobPolicy
    execution final response trace quiet ready timely sample authentic responseSupported reached
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 execution bob response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 21 _ final
      respondedTrace reached
  have completed := (LateOpeningRuntimeService.contract weight nonnegative).completes
    ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨bit, label, valid⟩ := LateOpeningRuntimeReadout.history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨0, none, final⟩ finalTrace
  have invariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.success publishedBit)
  have initialStored := invariant.respond execution bob response alicePublished
  have finalAlice := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 _ final initialStored reached
  have decoded := LateOpeningRuntimeUtility.nativeReadout_success ⟨0, none, final⟩ bit label
    valid completed publishedBit safe finalAlice published
  unfold LateOpeningRuntimeGame.payoff TerminalAudit.utility
  rw [clear, zero_mul, sub_zero]
  erw [LateOpeningRuntimeUtility.nativeBaseUtility_of_readout reward forfeit _ _ decoded bob]
  exact (LateOpeningRuntimeUtility.sourceUtility_intended reward forfeit bit label).2

end Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation
