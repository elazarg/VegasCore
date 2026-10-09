/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeReadout
import Vegas.Examples.LateOpeningRuntimeObservation
import Vegas.Pending.ReactiveOpeningWindow
import Vegas.Pending.EventInitialObservation
import Vegas.Pending.ReactiveResponseObservation
import Interaction.ReactiveScheduleEvaluation
import Interaction.ReactiveRoundTrace

/-! # Genuine late-opening prefixes and Bob's first observation

These are initialized executions of the actual public scheduler. Alice remains
silent at her protected turn and sends one certified opening at either late
turn. Bob is silent at his intervening observation. The definitions retain
ordinary response recall, public commands and the actual private sampler.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeLatePrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeObservation

def initialPhysical (bit : Bool) (label : Fin 3) : app.State :=
  State.initial (graph := nativeGraph) (setup.eventInputs (sourceInitial bit label))

def initialExecution (bit : Bool) (label : Fin 3) : app.Execution :=
  ReactiveApplication.Execution.initial app (initialPhysical bit label)

def opening (bit : Bool) : app.Action :=
  LateOpeningRuntimeService.runtime.windowOpening leaks aliceEvent aliceCandidate ⟨.bool, bit⟩

def openingMessage (bit : Bool) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 0), ⟨.opening aliceEvent aliceCandidate ⟨.bool, bit⟩,
    some ⟨aliceCandidate, ⟨.bool, bit⟩⟩, some ⟨aliceEvent⟩⟩⟩

/-- Slot zero sends at the first late activation; slot one sends at the second.
Neither policy emits any other packet, including at the protected activation. -/
def latePlayers (bit : Bool) (slot : Fin 2) : Player → app.Policy :=
  fun who past _ => PMF.pure
    (if who = alice ∧ past.length = 1 + slot.val then opening bit else ⟨none⟩)

def recorded (execution : app.Execution) (command : app.Command)
    (physical : app.State) : app.Execution :=
  { execution with application := physical, environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] }

def protectedSilent (bit : Bool) (label : Fin 3) : app.Execution :=
  let start := initialExecution bit label
  (recorded start (.activate alice) start.application).respond app alice ⟨none⟩

def firstLateDecision (bit : Bool) (label : Fin 3) : app.Execution :=
  let silent := protectedSilent bit label
  let waited := recorded silent .wait silent.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  recorded ticked (.activate alice) ticked.application

def beforeBob (bit : Bool) (label : Fin 3) (slot : Fin 2) : app.Execution :=
  (firstLateDecision bit label).respond app alice
    (if slot.val = 0 then opening bit else ⟨none⟩)

private theorem leaks_empty (who : Player)
    (pending : List (Message Player (WitnessedPacket nativeGraph)))
    (empty : foreignPending who pending = ∅) : leaks who pending = PMF.pure ∅ := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro selected supported
  have subset := (leaks_supported who pending selected).mp supported
  rw [empty] at subset
  exact Finset.subset_empty.mp subset

theorem recorded_activation (execution : app.Execution) (who : Player)
    (empty : foreignPending who execution.network.pending = ∅) :
    execution.environmentStep app (.activate who) =
      PMF.pure (recorded execution (.activate who) execution.application) := by
  rw [ReactiveApplication.Execution.activation_samples]
  change (leaks who execution.network.pending).map _ = _
  rw [leaks_empty who _ empty, PMF.pure_map]
  simp only [ReactiveApplication.Execution.sampledActivation, MessageNetwork.learn_empty]
  rfl

theorem recorded_wait (execution : app.Execution) :
    execution.environmentStep app .wait =
      PMF.pure (recorded execution .wait execution.application) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

theorem recorded_clock (execution : app.Execution) :
    execution.environmentStep app (.application .advanceClock) =
      PMF.pure (recorded execution (.application .advanceClock)
        { execution.application with clock := execution.application.clock + 1 }) := by
  simp only [ReactiveApplication.Execution.environmentStep]
  change ((environmentStep LateOpeningRuntimeService.runtime execution.application
    .advanceClock).map _).map _ = _
  rw [show environmentStep LateOpeningRuntimeService.runtime execution.application .advanceClock =
    PMF.pure { execution.application with clock := execution.application.clock + 1 } from rfl,
    PMF.pure_map, PMF.pure_map]
  rfl

theorem fixed_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution next : app.Execution)
    (position : Nat) (command : app.Command)
    (cursor : execution.environmentRecall.length = position)
    (selected : stageChoice weight nonnegative position (execution.observeEnvironment app) =
      PMF.pure command)
    (moved : execution.environmentStep app command = PMF.pure next) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution =
      app.resume players (command.actor? app) next := by
  rw [ReactiveApplication.round, LateOpeningRuntimeService.scheduler, cursor, selected,
    PMF.pure_bind,
    ReactiveApplication.dispatch, moved, PMF.pure_bind]

/-- The protected silence and first late response are a true initialized
four-command run, before any Bob response or any discretionary inclusion. -/
theorem beforeBob_run (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot) 4
      (initialExecution bit label) = PMF.pure (beforeBob bit label slot) := by
  let e0 := initialExecution bit label
  let p0 := recorded e0 (.activate alice) e0.application
  let e1 := p0.respond app alice ⟨none⟩
  let e2 := recorded e1 .wait e1.application
  let e3 := recorded e2 (.application .advanceClock)
    { e2.application with clock := e2.application.clock + 1 }
  let p3 := recorded e3 (.activate alice) e3.application
  have s0 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e0 =
      PMF.pure e1 := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e0 p0 0 (.activate alice)
      rfl rfl (recorded_activation e0 alice (by rfl))]
    simp only [ReactiveApplication.resume, ReactiveApplication.invoke, latePlayers]
    change (PMF.pure (if alice = alice ∧ 0 = 1 + slot.val then opening bit else ⟨none⟩)).map
      (p0.respond app alice) = _
    rw [ite_eq_right (by omega), PMF.pure_map]
  have s1 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e1 =
      PMF.pure e2 := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e1 e2 1 .wait
      rfl rfl (recorded_wait e1)]
    rfl
  have s2 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e2 =
      PMF.pure e3 := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e2 e3 2
      (.application .advanceClock) rfl rfl (recorded_clock e2)]
    rfl
  have s3 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e3 =
      PMF.pure (beforeBob bit label slot) := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e3 p3 3 (.activate alice)
      rfl rfl (recorded_activation e3 alice (by rfl))]
    change (PMF.pure (if alice = alice ∧ 1 = 1 + slot.val then opening bit else ⟨none⟩)).map
      (p3.respond app alice) = _
    have test : 1 = 1 + slot.val ↔ slot.val = 0 := by omega
    simp only [true_and, test, PMF.pure_map]
    rfl
  rw [ReactiveApplication.runRounds, s0, PMF.pure_bind,
    ReactiveApplication.runRounds, s1, PMF.pure_bind,
    ReactiveApplication.runRounds, s2, PMF.pure_bind,
    ReactiveApplication.runRounds, s3, PMF.pure_bind,
    ReactiveApplication.runRounds]

/-- The owned initial candidate supplies a genuine certificate; the runtime's
readiness token carries no emission time. -/
theorem firstLate_opening_packet (bit : Bool) (label : Fin 3) :
    app.packet (firstLateDecision bit label).application alice []
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)) =
        (openingMessage bit).payload := by
  rw [LateOpeningRuntimeService.runtime.windowOpening_packet leaks alice aliceEvent aliceCandidate
    ⟨.bool, bit⟩ _ [] rfl (by rfl)]
  congr 1

theorem beforeBob_first_network (bit : Bool) (label : Fin 3) :
    (beforeBob bit label 0).network =
      (MessageNetwork.empty.submit alice (openingMessage bit).payload).2 := by
  change (MessageNetwork.empty.submit alice (app.packet
    (firstLateDecision bit label).application alice []
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)))).2 = _
  rw [firstLate_opening_packet]

theorem beforeBob_second_network (bit : Bool) (label : Fin 3) :
    (beforeBob bit label 1).network = MessageNetwork.empty := rfl

/-- Before publication, Bob's full native application view reveals neither
the committed bit nor the Alice-only label. -/
theorem initialBobView (bit otherBit : Bool) (label otherLabel : Fin 3) :
    (initialPhysical bit label).playerView bob =
      (initialPhysical otherBit otherLabel).playerView bob := by
  let first : nativeGraph.Inputs := setup.eventInputs (sourceInitial bit label)
  let second : nativeGraph.Inputs := setup.eventInputs (sourceInitial otherBit otherLabel)
  have observed : nativeGraph.playerObserve bob (Config.initial first) =
      nativeGraph.playerObserve bob (Config.initial second) := by
    refine nativeGraph.playerObserve_congr bob (Config.initial first) (Config.initial second)
      rfl ?_
    intro field visible
    cases field with
    | inl input =>
        change Fin 2 at input
        fin_cases input
        all_goals
          change alice = bob at visible
          exact False.elim ((show alice ≠ bob by decide) visible)
    | inr event => rfl
  have publics := State.initial_publicView_eq_of_observation bob first second observed
  have candidates := State.initial_candidates_eq_of_observation bob first second observed
  change PlayerView.mk bob (State.initial first).publicView
    (nativeGraph.playerObserve bob (Config.initial first))
    (fun slot => (State.initial first).candidates.lookup (bob, slot)) = _
  rw [publics, observed, candidates]
  rfl

theorem firstLate_BobView (bit otherBit : Bool) (label otherLabel : Fin 3) :
    (firstLateDecision bit label).application.playerView bob =
      (firstLateDecision otherBit otherLabel).application.playerView bob :=
  congrArg (fun view : EventGraphRuntime.PlayerView nativeGraph =>
    { view with publicView := { view.publicView with clock := 1 } })
      (initialBobView bit otherBit label otherLabel)

/-- Sending has not yet disclosed the packet to Bob. Both late timings give
the same actual pre-activation record before the sampler draws its subset. -/
theorem beforeBob_info (bit otherBit : Bool) (label otherLabel : Fin 3)
    (slot otherSlot : Fin 2) :
    ((beforeBob bit label slot).recall bob, (beforeBob bit label slot).observe app bob) =
      ((beforeBob otherBit otherLabel otherSlot).recall bob,
        (beforeBob otherBit otherLabel otherSlot).observe app bob) := by
  rw [beforeBob, beforeBob]
  rw [LateOpeningRuntimeService.runtime.reactive_response_other_input leaks _ alice bob
    (by decide), LateOpeningRuntimeService.runtime.reactive_response_other_input leaks _ alice bob
      (by decide)]
  exact congrArg (fun view : EventGraphRuntime.PlayerView nativeGraph =>
    (([] : List app.PlayerEntry),
      (⟨⟨[], []⟩, view, []⟩ : app.PlayerView)))
        (firstLate_BobView bit otherBit label otherLabel)

def bobObserved (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  ((beforeBob bit label slot).sampledActivation app bob
    (if seen then {(alice, 0)} else ∅)).respond app bob ⟨none⟩

/-- A first-late opening is disclosed or missed with the actual fair sampler.
The returned execution includes Bob's genuine remembered silent response. -/
theorem firstBob_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit 0)
      (beforeBob bit label 0) = mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (bobObserved bit label 0 true))
        (PMF.pure (bobObserved bit label 0 false)) := by
  have foreign : foreignPending bob (beforeBob bit label 0).network.pending = {(alice, 0)} := by
    rw [beforeBob_first_network]
    rfl
  rw [ReactiveApplication.round, LateOpeningRuntimeService.scheduler]
  change (PMF.pure (.activate bob : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.activation_samples, PMF.bind_map]
  change (leaks bob (beforeBob bit label 0).network.pending).bind _ = _
  rw [leaks_singleton bob _ (alice, 0) foreign]
  simp only [Function.comp_def, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.invoke, latePlayers,
    show bob ≠ alice by decide, false_and, ↓reduceIte, PMF.pure_map]
  rw [mix_bind, PMF.pure_bind, PMF.pure_bind]
  rfl

/-- Waiting for the second late turn leaves no packet at Bob's first sample. -/
theorem secondBob_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit 1)
      (beforeBob bit label 1) = PMF.pure (bobObserved bit label 1 false) := by
  rw [fixed_round weight nonnegative (latePlayers bit 1) (beforeBob bit label 1)
    (recorded (beforeBob bit label 1) (.activate bob) (beforeBob bit label 1).application)
      4 (.activate bob) rfl rfl
        (recorded_activation _ bob (by rw [beforeBob_second_network]; rfl))]
  simp only [ReactiveApplication.resume, ReactiveApplication.invoke, latePlayers,
    PMF.pure_map]
  simp only [bobObserved, Bool.false_eq_true, ↓reduceIte,
    ReactiveApplication.Execution.sampledActivation, MessageNetwork.learn_empty]
  rfl

def bobObservationRecord (bit : Bool) (label : Fin 3) (seen : Bool) : app.PlayerEntry :=
  ⟨⟨⟨if seen then [openingMessage bit] else [], []⟩,
    (firstLateDecision bit label).application.playerView bob, []⟩, ⟨none⟩, none⟩

theorem bobObserved_first_recall (bit : Bool) (label : Fin 3) (seen : Bool) :
    (bobObserved bit label 0 seen).recall bob = [bobObservationRecord bit label seen] := by
  have packet := beforeBob_first_network bit label
  change (beforeBob bit label 0).recall bob ++
    [⟨((beforeBob bit label 0).sampledActivation app bob
      (if seen then {(alice, 0)} else ∅)).observe app bob, ⟨none⟩, none⟩] = _
  have recalled : (beforeBob bit label 0).recall bob = [] := rfl
  rw [recalled, List.nil_append]
  have localView : (beforeBob bit label 0).application.playerView bob =
      (firstLateDecision bit label).application.playerView bob := rfl
  unfold ReactiveApplication.Execution.sampledActivation ReactiveApplication.Execution.observe
  change [ReactiveApplication.PlayerEntry.mk (app := app)
    (ReactiveApplication.PlayerView.mk (app := app)
      (((beforeBob bit label 0).network.learn bob
        (if seen then {(alice, 0)} else ∅)).observe bob)
      ((beforeBob bit label 0).application.playerView bob) []) ⟨none⟩ none] = _
  rw [localView, packet]
  cases seen <;> rfl

theorem bobObserved_second_recall (bit : Bool) (label : Fin 3) :
    (bobObserved bit label 1 false).recall bob = [bobObservationRecord bit label false] := by
  rfl

/-- The private label is absent from each complete remembered observation
record, including the application projection and the silent response itself. -/
theorem bobObservationRecord_label (bit : Bool) (label otherLabel : Fin 3) (seen : Bool) :
    bobObservationRecord bit label seen = bobObservationRecord bit otherLabel seen := by
  unfold bobObservationRecord
  rw [firstLate_BobView bit bit label otherLabel]

/-- The unseen record is identical for first-late and second-late sending.
This equality retains Bob's action, emitted output and full before-view. -/
theorem unseen_timing_recall (bit : Bool) (label otherLabel : Fin 3) :
    (bobObserved bit label 0 false).recall bob =
      (bobObserved bit otherLabel 1 false).recall bob := by
  rw [bobObserved_first_recall, bobObserved_second_recall,
    bobObservationRecord_label bit label otherLabel false]

theorem firstBob_recall_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 0) 5 (initialExecution bit label)).map
        (fun execution => execution.recall bob) =
        mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure [bobObservationRecord bit label true])
          (PMF.pure [bobObservationRecord bit label false]) := by
  rw [show 5 = 4 + 1 from rfl, ReactiveApplication.runRounds_add, beforeBob_run,
    PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  rw [firstBob_round, mix_map, PMF.pure_map, PMF.pure_map,
    bobObserved_first_recall, bobObserved_first_recall]

theorem firstBob_run (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 0) 5 (initialExecution bit label) =
        mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure (bobObserved bit label 0 true))
          (PMF.pure (bobObserved bit label 0 false)) := by
  rw [show 5 = 4 + 1 from rfl, ReactiveApplication.runRounds_add, beforeBob_run,
    PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  exact firstBob_round weight nonnegative bit label

theorem secondBob_run (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 1) 5 (initialExecution bit label) =
        PMF.pure (bobObserved bit label 1 false) := by
  rw [show 5 = 4 + 1 from rfl, ReactiveApplication.runRounds_add, beforeBob_run,
    PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  exact secondBob_round weight nonnegative bit label

/-- The genuine certified opening is available in the full bounded raw menu,
at every input. This does not restrict any competing malformed response. -/
theorem opening_in_raw_menu (bit : Bool) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    opening bit ∈ rawMenu.actions who past view := by
  change _ ∈ (ReactiveApplication.ResponseMenu.fromSubmissions
    (fun _ past view => bounds.submissions
      (ReactiveApplication.ResponseMenu.knownPackets past view))).actions who past view
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩) ∈
    bounds.submissions (ReactiveApplication.ResponseMenu.knownPackets past view)
  rw [MessageBounds.submissions_mem]
  exact ⟨⟨⟨trivial, bool_covered bit⟩, trivial⟩, ⟨trivial, bool_covered bit⟩⟩

theorem latePlayers_covered (bit : Bool) (slot : Fin 2) :
    ∀ who past view response, response ∈ (latePlayers bit slot who past view).support →
      response ∈ rawMenu.actions who past view := by
  intro who past view response supported
  have chosen := (PMF.mem_support_pure_iff _ _).mp supported
  subst response
  by_cases send : who = alice ∧ past.length = 1 + slot.val
  · rw [ite_eq_left send]
    exact opening_in_raw_menu bit who past view
  · rw [ite_eq_right send]
    change _ ∈ (ReactiveApplication.ResponseMenu.fromSubmissions
      (fun _ past view => bounds.submissions
        (ReactiveApplication.ResponseMenu.knownPackets past view))).actions who past view
    rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    trivial

theorem initialPhysical_supported (bit : Bool) (label : Fin 3) :
    initialPhysical bit label ∈ initial.support := by
  change _ ∈ (setup.initialLaw.map fun source =>
    State.initial (graph := nativeGraph) (setup.eventInputs source)).support
  rw [PMF.support_map]
  exact ⟨sourceInitial bit label, (initialLaw_support _).mpr ⟨bit, label, rfl⟩, rfl⟩

/-- Each observed/missed branch is an actual legal bounded raw history,
starting from a supported source parameter. -/
theorem bobObserved_first_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (seen : Bool) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, none, bobObserved bit label 0 seen⟩)) := by
  obtain ⟨trace⟩ := rawMenu.trace_initial initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (initialPhysical bit label)
      (initialPhysical_supported bit label)
  apply rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit 0)
      (latePlayers_covered bit 0) 21 5 (initialExecution bit label) _ trace
  rw [firstBob_run]
  cases seen
  · exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by simp)
  · exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by simp)

theorem bobObserved_second_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, none, bobObserved bit label 1 false⟩)) := by
  obtain ⟨trace⟩ := rawMenu.trace_initial initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (initialPhysical bit label)
      (initialPhysical_supported bit label)
  apply rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit 1)
      (latePlayers_covered bit 1) 21 5 (initialExecution bit label) _ trace
  rw [secondBob_run]
  simp

end Vegas.Examples.LateOpeningRuntimeLatePrefix
