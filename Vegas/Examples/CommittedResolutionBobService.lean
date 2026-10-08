/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionReadout
import Vegas.Examples.CommittedResolutionRecovery
import Vegas.Pending.ReactiveCanonicalResolution
import Vegas.Pending.ReactiveServiceSelection
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveMonitoring

/-! # A clean truthful Bob comparator after arbitrary RAW prefixes

The deterministic late-recovery controller gives Bob a protected final
activation. Its canonical TRUE response is accepted by the actual next round,
independently of all earlier Alice responses and of all subsequent policies.
The resulting packet is permitted at every record retaining its acceptance.
This is an operational continuation comparator, not an equilibrium theorem.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionBobService

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability
open CommittedResolutionService CommittedResolutionReadout

def bobPacket : WitnessedPacket nativeGraph :=
  ⟨.opening bobEvent bobCandidate ⟨.bool, true⟩,
    some ⟨bobCandidate, ⟨.bool, true⟩⟩, some ⟨bobEvent⟩⟩

def bobMessage (execution : app.Execution) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(bob, execution.network.nextSerial bob), bobPacket⟩

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initialLaw setup := by
  rw [PMF.map_comp]
  rfl

/-- Recovery retains Bob's protected activation at every legal RAW prefix. -/
theorem recovery_bob_phase (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    control.execution.environmentRecall.length = 11 ∧
      control.execution.application.clock = 2 ∧ control.execution.recall bob = [] ∧
      control.execution.application.config.cut.Ready bobEvent ∧
      control.execution.application.WithinDeadline (runtime setup) bobEvent :=
  bob_activation_phase control (app.trace_of_scheduler_support_subset (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler
      CommittedResolutionService.scheduler
      CommittedResolutionRecovery.scheduler_support_subset trace) active

/-- Canonical TRUE emits Bob's immutable certified opening and is accepted
when selected at his actual protected activation. -/
theorem canonical_bob_response (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    ∃ material : WitnessedSubmission nativeGraph,
      (runtime setup).canonicalServiceDecision leaks bob (control.execution.recall bob)
        (control.execution.observe app bob) bobEvent true = ⟨some material⟩ ∧
      app.submit control.execution.application bob material = control.execution.application ∧
      app.packet (app.submit control.execution.application bob material) bob
        (control.execution.network.known bob) material = bobPacket ∧
      ∃ next : EventGraphRuntime.State nativeGraph,
        app.handle (app.submit control.execution.application bob material)
          (bobMessage control.execution) = some next ∧
        next.config.store (.inr bobEvent) = some (.success true) := by
  obtain ⟨_cursor, _clock, _recalled, ready, timely⟩ := recovery_bob_phase control trace active
  have aligned : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph))) CommittedResolutionService.horizon
        CommittedResolutionRecovery.scheduler).Trace (some control) := by
    rwa [initial_law_eq]
  obtain ⟨input, supported, reachable⟩ := (runtime setup).reactive_history_graph_reachable
    leaks (setup.initialLaw.map setup.eventInputs) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler
      aligned
  have stored : bobBinding.get? control.execution.application.config.store =
      some (.success true) := by
    change some (control.execution.application.config.inputs bobInput) = _
    rw [reachable.inputs_eq, bob_input_true input supported]
  have resolved : EventCode.resolveOutput? bobBinding [] true
      control.execution.application.config.store = some (.success true) := by
    simp [EventCode.resolveOutput?, stored, GuardCheck.allAccepted?]
  have validated : EventCode.resolveOutput? bobBinding [] true
      (control.execution.observe app bob).application.observation.store =
        some (.success true) := by
    change EventCode.resolveOutput? bobBinding [] true
      (nativeGraph.playerStore bob control.execution.application.config.store) = _
    rwa [EventCode.resolveOutput?_playerStore]
  obtain ⟨associated, fixed⟩ := bob_binding_fixed CommittedResolutionRecovery.scheduler
    CommittedResolutionService.horizon control trace
  obtain ⟨material, decision, emitted⟩ :=
    (runtime setup).history_canonicalServiceDecision_resolution_validated leaks
      (setup.initialLaw.map setup.eventInputs) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler
      aligned bob bobEvent .bool bobBinding [] rfl rfl rfl bobCandidate true validated
      associated rfl
  rw [control.execution.application.publicView_tokenFor_of_ready _ bobEvent rfl ready] at emitted
  change app.packet (app.submit control.execution.application bob material) bob
    (control.execution.network.known bob) material = bobPacket at emitted
  have call : material.call.packet = .opening bobEvent bobCandidate ⟨.bool, true⟩ :=
    congrArg WitnessedPacket.call emitted
  have unchanged : app.submit control.execution.application bob material =
      control.execution.application := by
    rcases material with ⟨⟨packet, opening⟩, evidence⟩
    dsimp only at call
    subst packet
    cases opening <;> rfl
  let next := control.execution.application.complete bobEvent ready true (.success true)
  refine ⟨material, decision, unchanged, emitted, next, ?_, ?_⟩
  · rw [unchanged, reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
      (by rfl)]
    exact (runtime setup).handle_opening_eq control.execution.application _ bobEvent bobCandidate
      bob .bool bobBinding [] rfl rfl rfl ready timely rfl rfl associated true fixed stored
      (.success true) resolved
  · change (next.config.outputs bobEvent) = _
    simp [next, EventGraphRuntime.State.complete, Config.complete]

/-- An accepting receipt makes this guard-free truthful packet permanently
permitted, independently of the final clock and other submissions. -/
theorem bob_message_permitted (execution : app.Execution) (record : SettledRecord nativeGraph)
    (accepted : ((bobMessage execution).id, true) ∈ record.receipts) :
    record.permits (bobMessage execution) = true := by
  apply SettledRecord.permits_of_accepted record (bobMessage execution) bobEvent rfl accepted
  refine ⟨by simp [bobMessage, bobPacket, certifiedOpening], ?_⟩
  exact (record.view.openingGuardsAccepted_iff bob bobEvent .bool bobBinding []
    rfl rfl rfl bobCandidate ⟨.bool, true⟩ (some ⟨bobCandidate, ⟨.bool, true⟩⟩)).mpr
      ⟨true, rfl, rfl⟩

/-- The actual recovery scheduler immediately includes canonical Bob TRUE
with probability one after every legal RAW prefix. -/
theorem canonical_bob_round (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    ∃ material : WitnessedSubmission nativeGraph, ∃ next : app.Execution,
      (runtime setup).canonicalServiceDecision leaks bob (control.execution.recall bob)
        (control.execution.observe app bob) bobEvent true = ⟨some material⟩ ∧
      app.round CommittedResolutionRecovery.scheduler players
        (control.execution.respond app bob ⟨some material⟩) = PMF.pure next ∧
      next.application.config.store (.inr bobEvent) = some (.success true) ∧
      ((bobMessage control.execution).id, true) ∈ next.receipts ∧
      ((runtime setup).settledRecord leaks next).permits (bobMessage control.execution) = true := by
  obtain ⟨cursor, _clock, _recalled, _ready, _timely⟩ := recovery_bob_phase control trace active
  obtain ⟨material, decision, _unchanged, emitted, state, accepted, output⟩ :=
    canonical_bob_response control trace active
  let submitted := control.execution.respond app bob ⟨some material⟩
  let identifier := (bobMessage control.execution).id
  let included := submitted.includePending app identifier
  let next : app.Execution := { included with environmentRecall :=
    submitted.environmentRecall ++ [⟨submitted.observeEnvironment app, .include identifier⟩] }
  have serials := (app.messageIdentityInvariant CommittedResolutionRecovery.scheduler).history
    (initialLaw setup) CommittedResolutionService.horizon
      (by intro state _; exact ⟨MessageNetwork.SerialsBeforeNext.empty,
      MessageNetwork.UniqueIds.empty⟩) trace
  have call : material.call.packet.event? nativeGraph = some bobEvent := by
    have same := congrArg WitnessedPacket.call emitted
    change material.call.packet = _ at same
    rw [same]
    rfl
  have selection := (runtime setup).reactiveLatest_after_submit leaks bob bobEvent
    control.execution serials.1 material call
  have chosen : CommittedResolutionRecovery.scheduler submitted.environmentRecall
      (submitted.observeEnvironment app) = PMF.pure (.include identifier) := by
    have located : submitted.environmentRecall.length = 11 :=
      (app.respond_environmentRecall control.execution bob ⟨some material⟩) ▸ cursor
    simp only [CommittedResolutionRecovery.scheduler, located, show (11 : Nat) ≠ 5 by decide,
      ↓reduceIte, CommittedResolutionService.scheduler, stageChoice]
    exact congrArg PMF.pure selection
  have actual : app.handle submitted.application (bobMessage control.execution) = some state := by
    change app.handle (app.submit control.execution.application bob material) _ = _
    exact accepted
  have found : submitted.network.lookup identifier = some (bobMessage control.execution) := by
    change (control.execution.network.submit bob
      (app.packet (app.submit control.execution.application bob material) bob
        (control.execution.network.known bob) material)).2.lookup
          (bob, control.execution.network.nextSerial bob) = _
    rw [serials.1.lookup_submit, emitted]
    rfl
  have pending : included.application = state := by
    change (submitted.includePending app identifier).application = state
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (app.handle submitted.application (bobMessage control.execution)).getD _ = _
    rw [actual]
    rfl
  have receipt : (identifier, true) ∈ next.receipts := by
    change (identifier, true) ∈ (submitted.includePending app identifier).receipts
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (identifier, true) ∈ submitted.receipts ++
      [(identifier, (app.handle submitted.application (bobMessage control.execution)).isSome)]
    rw [actual]
    simp
  refine ⟨material, next, decision, ?_, ?_, receipt, ?_⟩
  · rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  · change included.application.config.store _ = _
    rw [pending]
    exact output
  · exact bob_message_permitted control.execution _ receipt

/-- A truthful successful publication and its accepting receipt persist under
every supported continuation, even with arbitrary future RAW policies and a
different observation-local scheduler. The accepted packet remains permitted. -/
theorem bob_accepted_suffix (players : Player → app.Policy) (scheduler : app.Scheduler)
    (count : Nat) (before final : app.Execution) (origin : app.Execution)
    (published : before.application.config.store (.inr bobEvent) = some (.success true))
    (accepted : ((bobMessage origin).id, true) ∈ before.receipts)
    (reached : final ∈ (app.runRounds scheduler players count before).support) :
    final.application.config.store (.inr bobEvent) = some (.success true) ∧
      ((bobMessage origin).id, true) ∈ final.receipts ∧
      ((runtime setup).settledRecord leaks final).permits (bobMessage origin) = true := by
  have output := (ReactiveApplication.Invariant.policyInvariant app
    ((runtime setup).reactiveStoreInvariant leaks (.inr bobEvent)
      (.success true)) players).runRounds scheduler count before final
      published reached
  have receipt := (app.receipt_policyInvariant players ((bobMessage origin).id, true)).runRounds
    scheduler count before final accepted reached
  exact ⟨output, receipt, bob_message_permitted origin _ receipt⟩

/-- Canonical Bob TRUE succeeds after every legal recovery prefix and retains
its truthful publication and permitted packet along every later RAW suffix. -/
theorem canonical_bob_continuation (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    ∃ material : WitnessedSubmission nativeGraph, ∃ next : app.Execution,
      (runtime setup).canonicalServiceDecision leaks bob (control.execution.recall bob)
        (control.execution.observe app bob) bobEvent true = ⟨some material⟩ ∧
      app.round CommittedResolutionRecovery.scheduler players
        (control.execution.respond app bob ⟨some material⟩) = PMF.pure next ∧
      ∀ (future : Player → app.Policy) (scheduler : app.Scheduler) (count : Nat)
        (final : app.Execution), final ∈ (app.runRounds scheduler future count next).support →
        final.application.config.store (.inr bobEvent) = some (.success true) ∧
          ((bobMessage control.execution).id, true) ∈ final.receipts ∧
          ((runtime setup).settledRecord leaks final).permits
            (bobMessage control.execution) = true := by
  obtain ⟨material, next, decision, moved, published, accepted, _permitted⟩ :=
    canonical_bob_round players control trace active
  exact ⟨material, next, decision, moved, fun future scheduler count final reached =>
    bob_accepted_suffix future scheduler count next final control.execution published accepted
      reached⟩

/-- Whether an arbitrary RAW Bob response is accepted is determined entirely
by its call syntax. Thus this success/failure class is the same at every hidden
history compatible with a Bob information state. Attached certificate requests
and ineffective private preparation do not change it. -/
theorem bob_raw_response_accepts_iff (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (material : WitnessedSubmission nativeGraph) :
    (∃ next : EventGraphRuntime.State nativeGraph,
      app.handle (app.submit control.execution.application bob material)
        ⟨(bob, control.execution.network.nextSerial bob),
          app.packet (app.submit control.execution.application bob material) bob
            (control.execution.network.known bob) material⟩ = some next) ↔
      material.call.packet = .opening bobEvent bobCandidate ⟨.bool, true⟩ := by
  have current : (app.packet (app.submit control.execution.application bob material) bob
      (control.execution.network.known bob) material).token =
        (app.submit control.execution.application bob material).publicView.tokenFor
          (app.packet (app.submit control.execution.application bob material) bob
            (control.execution.network.known bob) material).call := by
    rw [(runtime setup).reactiveApplication_packet_token leaks,
      (runtime setup).reactiveApplication_submit_publicView leaks]
    rfl
  rw [(runtime setup).reactiveApplication_handle_of_current_token leaks _ _ current]
  change (∃ next : EventGraphRuntime.State nativeGraph,
    (runtime setup).handle (app.submit control.execution.application bob material)
      ⟨(bob, control.execution.network.nextSerial bob), material.call.packet⟩ = some next) ↔ _
  rcases material with ⟨⟨packet, opening⟩, evidence⟩
  cases packet with
  | malformed raw => simp [handle]
  | commitment event candidate =>
      have rejected : (runtime setup).handle
          (app.submit control.execution.application bob ⟨⟨.commitment event candidate,
            opening⟩, evidence⟩)
          ⟨(bob, control.execution.network.nextSerial bob), .commitment event candidate⟩ =
            none := by
        fin_cases event <;> simp only [handle] <;> split_ifs <;> rfl
      simp [rejected]
  | opening event candidate raw =>
      have unchanged : app.submit control.execution.application bob
          ⟨⟨.opening event candidate raw, opening⟩, evidence⟩ =
            control.execution.application := by
        cases opening <;> rfl
      rw [unchanged]
      constructor
      · rintro ⟨next, accepted⟩
        obtain ⟨selected, named, owned⟩ := (runtime setup).handle_event_actor
          control.execution.application next
            ⟨(bob, control.execution.network.nextSerial bob), .opening event candidate raw⟩
            accepted
        have same : selected = event := Option.some.inj named.symm
        subst selected
        have eventEq : event = bobEvent := by
          fin_cases event
          · change none = some bob at owned
            cases owned
          · change some alice = some bob at owned
            norm_num [alice, bob] at owned
          · rfl
        subst event
        obtain ⟨rfl, rfl⟩ := accepted_bob_opening_true CommittedResolutionRecovery.scheduler
          CommittedResolutionService.horizon control trace next _ candidate raw accepted
        rfl
      · intro same
        cases same
        obtain ⟨honest, _decision, unchanged, _emitted, next, accepted, _published⟩ :=
          canonical_bob_response control trace active
        rw [unchanged] at accepted
        exact ⟨next, reactiveHandle_call accepted⟩

/-- Every scheduler command after Bob's activation is passive: inclusion,
clock advancement, expiry, or waiting. No player can signal again. -/
theorem recovery_after_bob_passive (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (later : 11 ≤ past.length) (command : app.Command)
    (selected : command ∈ (CommittedResolutionRecovery.scheduler past view).support) :
    command.actor? app = none := by
  have notLate : past.length ≠ 5 := by omega
  simp only [CommittedResolutionRecovery.scheduler, notLate, ↓reduceIte,
    CommittedResolutionService.scheduler] at selected
  generalize located : past.length = position at later selected
  by_cases inside : position < 16
  · interval_cases position <;>
      simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals
      subst command
      first
      | rfl
      | rcases (runtime setup).reactiveLatest_wait_or_owned leaks bobEvent bob view with
          idle | ⟨id, _owned, included⟩
        · rw [idle]; rfl
        · rw [included]; rfl
  · have idle : stageChoice position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    subst command
    rfl

private theorem recovery_round_after_bob (players : Player → app.Policy)
    (execution : app.Execution) (later : 11 ≤ execution.environmentRecall.length) :
    app.round CommittedResolutionRecovery.scheduler players execution =
      (CommittedResolutionRecovery.scheduler execution.environmentRecall
        (execution.observeEnvironment app)).bind (execution.environmentStep app) := by
  unfold ReactiveApplication.round ReactiveApplication.dispatch
  apply bind_congr_on_support
  intro command selected
  rw [recovery_after_bob_passive _ _ later command selected]
  change (execution.environmentStep app command).bind PMF.pure = _
  exact PMF.bind_pure _

/-- After Bob's one response, the complete physical suffix is independent of
every player's future policy. This accounts for whole-policy deviations. -/
theorem recovery_suffix_policy_independent (first second : Player → app.Policy)
    (count : Nat) (execution : app.Execution)
    (later : 11 ≤ execution.environmentRecall.length) :
    app.runRounds CommittedResolutionRecovery.scheduler first count execution =
      app.runRounds CommittedResolutionRecovery.scheduler second count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [ReactiveApplication.runRounds, ReactiveApplication.runRounds,
        recovery_round_after_bob first execution later,
        recovery_round_after_bob second execution later]
      apply bind_congr_on_support
      intro next reached
      apply ih
      have roundReached : next ∈
          (app.round CommittedResolutionRecovery.scheduler first execution).support := by
        rwa [recovery_round_after_bob first execution later]
      have cursor := app.round_environmentRecall_length CommittedResolutionRecovery.scheduler
        first execution next roundReached
      omega

/-- Passive recovery suffixes append no responses or packets, under arbitrary
future RAW policies. In particular, Bob's accepting response is his last one. -/
theorem recovery_suffix_preserves_traffic (players : Player → app.Policy) (count : Nat)
    (execution final : app.Execution) (later : 11 ≤ execution.environmentRecall.length)
    (reached : final ∈
      (app.runRounds CommittedResolutionRecovery.scheduler players count execution).support) :
    final.recall = execution.recall ∧ final.network.inputs = execution.network.inputs := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      obtain ⟨next, moved, continued⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have cursor := app.round_environmentRecall_length CommittedResolutionRecovery.scheduler
        players execution next moved
      have nextLate : 11 ≤ next.environmentRecall.length := by omega
      have retained := ih next nextLate continued
      rw [recovery_round_after_bob players execution later] at moved
      obtain ⟨command, _selected, environment⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      exact ⟨retained.1.trans (app.environmentStep_recall execution next command environment),
        retained.2.trans (app.environmentStep_inputs execution next command environment)⟩

end Vegas.Examples.CommittedResolutionBobService
