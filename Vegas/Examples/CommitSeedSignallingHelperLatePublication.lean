/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFixedLateSuccess
import Vegas.Examples.CommitSeedSignallingHelperPublicationPrefix
import Vegas.Examples.CommitSeedSignallingHelperPublicationRecall
import Vegas.Examples.CommitSeedSignallingOriginalClearPrefix

/-! # An eligible proper helper declaration enters the actual publication suffix -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Any counted original Alice binding emitted at her eligible clock is
physically admitted by the actual next round at the selected late slot.
Bob's real original receipt makes this the second binding, so settlement
installs the publication suffix even when Alice's preparation is unopenable. -/
theorem helper_late_binding_publication_entry (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (position : execution.environmentRecall.length =
      lateIncludePosition alice (seedBits seed alice))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment (bindingEvent alice) candidate)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (players : Player → app.Policy) (next : app.Execution)
    (reached : next ∈ (app.round (family seed) players execution).support) :
    ∃ native,
      handle runtime execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.accepted (.inr (bindingEvent alice)) = some candidate ∧
      next.application.current.native = native ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.excluded = ∅ ∧
      ∀ recalled ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests recalled.beforeView.application.2 alice coordinate := by
  obtain ⟨native, nextState, _input, _authored, _tagged, found, _timely, command,
      handled, _completed, accepted, normalized, phaseHandled⟩ :=
    original_late_binding_admission seed remaining execution trace alice position request message
      emitted candidate call
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have early : execution.environmentRecall.length ≤ 10 := by
    rw [position]
    cases seedBits seed alice <;> decide
  have clear := original_prefix_before_expiry_clear seed ⟨remaining, none, execution⟩ raw original
    (by
      change execution.environmentRecall.length ≤ 20
      exact early.trans (by decide : 10 ≤ 20))
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).1
  have positive : 0 < remaining := by
    change execution.environmentRecall.length + remaining = 64 at accounted
    omega
  have sourceTrace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 1) + 1, none, execution⟩) := by
    rw [show remaining - 1 + 1 = remaining by omega]
    exact countedInRaw.trace initial horizon (family seed) trace
  obtain ⟨selected, chosen, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have selectedEq : selected = .«include» message.id := by
    rw [family_apply, command] at chosen
    exact (PMF.mem_support_pure_iff _ _).mp chosen
  subst selected
  obtain ⟨observed, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  simp only [ReactiveApplication.resume, ReactiveApplication.Command.actor?,
    PMF.mem_support_pure_iff] at resumed
  subst next
  have chosenInclude : (.«include» message.id : app.Command) ∈
      (family seed execution.environmentRecall (execution.observeEnvironment app)).support := by
    rw [family_apply, command]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have callAlice : message.payload.packet.call = .commitment aliceBinding candidate := by
    simpa only [bindingEvent, ite_true] using call
  obtain ⟨suffix, nativeEq, excluded⟩ := original_second_binding_publication_prefix (family seed)
    (remaining - 1) execution sourceTrace original clear bobAccepted message found candidate
      callAlice native handled nextState normalized phaseHandled chosenInclude observed moved
  refine ⟨native, handled, accepted, nativeEq, suffix, excluded, ?_⟩
  intro recalled recorded coordinate publication
  exact original_environment_no_prior_publication_request (family seed)
    ⟨remaining, none, execution⟩ raw original observed (.«include» message.id) moved alice recalled
      recorded coordinate publication

/-- The native late include at either eligible Alice slot installs the literal
successful binding result and the publication-only suffix. Earlier silent
Alice declarations remain in recall; none is replaced by a policy-consistency
assumption. The only Bob premise is his actual original accepting receipt. -/
theorem helper_proper_late_publication_entry (seed : Seeds) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - lateIncludePosition alice (seedBits seed alice), none, execution⟩))
    (position : execution.environmentRecall.length =
      lateIncludePosition alice (seedBits seed alice))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (serial : Nat) (entry : app.PlayerEntry) (retained : entry ∈ execution.recall alice)
    (declared : entry.action =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (timed : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (next : app.Execution)
    (included : next ∈ (execution.environmentStep app (.«include» message.id)).support) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
        PMF.pure (.«include» message.id) ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.native.accepted (.inr (bindingEvent alice)) =
        some (alice, .prepared serial) ∧
      next.application.current.native.config.outputs (bindingEvent alice) = some
        (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
          (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) ∧
      next.application.current.excluded = ∅ ∧
      ∀ recalled ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests recalled.beforeView.application.2 alice coordinate := by
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have early : execution.environmentRecall.length ≤ 20 := by
    rw [position]
    cases seedBits seed alice <;> decide
  have clear := original_prefix_before_expiry_clear seed
    ⟨horizon - lateIncludePosition alice (seedBits seed alice), none, execution⟩ raw original early
  obtain ⟨native, nextState, command, call, found, handled, accepted, output, normalized,
      phaseHandled, _receipt⟩ :=
    proper_late_inclusion seed alice (horizon - lateIncludePosition alice (seedBits seed alice))
      execution trace position request serial entry retained declared fresh message emitted timed
  have budget : horizon - lateIncludePosition alice (seedBits seed alice) =
      (horizon - lateIncludePosition alice (seedBits seed alice) - 1) + 1 := by
    cases seedBits seed alice <;> decide
  have rawMenuTrace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(horizon - lateIncludePosition alice (seedBits seed alice) - 1) + 1,
        none, execution⟩) := by
    rw [← budget]
    exact (PhaseCount.onePacketMenu_in_raw runtime leaks bounds).trace
      initial horizon (family seed) trace
  have callAlice : message.payload.packet.call =
      .commitment aliceBinding (alice, .prepared serial) := by
    simpa only [bindingEvent, ite_true] using call
  have actualHandled : handle runtime execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native := by
    rw [call]
    exact handled
  have chosen : (.«include» message.id : app.Command) ∈
      (family seed execution.environmentRecall (execution.observeEnvironment app)).support := by
    rw [command]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨suffix, nativeEq, excluded⟩ := original_second_binding_publication_prefix (family seed)
    (horizon - lateIncludePosition alice (seedBits seed alice) - 1) execution rawMenuTrace original
      clear bobAccepted message found (alice, .prepared serial) callAlice native actualHandled
        nextState normalized phaseHandled chosen next included
  refine ⟨command, suffix, ?_, ?_, excluded, ?_⟩
  · rw [nativeEq]
    exact accepted
  · rw [nativeEq]
    exact output
  · intro recalled recorded coordinate publication
    exact original_environment_no_prior_publication_request (family seed)
      ⟨horizon - lateIncludePosition alice (seedBits seed alice), none, execution⟩ raw original
        next (.«include» message.id) included alice recalled recorded coordinate publication

end Vegas.Examples.CommitSeedSignalling
