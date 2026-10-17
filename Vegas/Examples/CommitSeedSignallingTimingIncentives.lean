/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingIncentives
import Vegas.Examples.CommitSeedSignallingBindingPersistence
import Vegas.Game.PhaseCountServicePolicy
import Vegas.Pending.PhaseBindingMenuShape

/-! # Concrete counted timing deviations in the private-seed runtime -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem binding_payload_bool (owner : Player) (event : graph.EventId)
    (payload : simpleExpr.Ty) (binding : graph.outputLayout event = .binding owner payload) :
    payload = .bool := by
  classical
  fin_cases event
  · exact (EventField.binding.inj (binding_layouts.1.symm.trans binding)).2.symm
  · exact (EventField.binding.inj (binding_layouts.2.symm.trans binding)).2.symm
  · cases reveal_layouts.1.symm.trans binding
  · cases reveal_layouts.2.symm.trans binding

/-- A literal typed value, transported only along the static binding type. -/
def trueBindingLaw (owner : Player) (event : graph.EventId) (payload : simpleExpr.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (_ : List app.PlayerEntry) (_ : app.PlayerView) : PMF (simpleExpr.Val payload) := by
  have same := binding_payload_bool owner event payload binding
  subst payload
  exact PMF.pure true

/-- The original binding waits until the fixed late clock; every later
attempt is serviced immediately. Clocks are relative to event readiness. -/
def fixedLateRule (owner : Player) (coordinate : CommitAttemptEvent graph)
    (clocks : List Nat) : Bool :=
  if coordinate.attempt = originalAttempt then
    decide (clocks.getLastD 0 = if owner = alice then 2 else 4)
  else true

/-- The existing source-independent service policy supplies truthful openings,
fresh binding slots and count-correct evidence, with no encoder tremble. -/
def properPolicy
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) :
    app.Policy :=
  phaseCountServicePolicy setup .concurrentReveals runtime leaks bounds trueBindingLaw rule
    0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num) owner

open Classical in
/-- Override the first original callback with WAIT. The normalized service
constructor itself always sends at its first callback. -/
def fixedLatePolicy (owner : Player) : app.Policy := fun past view =>
  if view.application.2.attempt = originalAttempt ∧ view.application.2.native.clock = 0 then
    PMF.pure ⟨none⟩
  else properPolicy fixedLateRule owner past view

theorem properPolicy_counted
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (properPolicy rule owner past view).support) :
    response ∈ countedMenu.actions owner past view := by
  exact phaseCountServicePolicy_covered setup .concurrentReveals runtime leaks bounds
    trueBindingLaw rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    owner past view response supported

theorem fixedLatePolicy_counted (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (fixedLatePolicy owner past view).support) :
    response ∈ countedMenu.actions owner past view := by
  classical
  unfold fixedLatePolicy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds owner past view
  · exact properPolicy_counted fixedLateRule owner past view response supported

def properContinuation
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) :
    rawModel.BehavioralPolicy owner :=
  rawMenu.restrictPolicy initial horizon scheduler owner (properPolicy rule owner)

def fixedLateContinuation (owner : Player) : rawModel.BehavioralPolicy owner :=
  rawMenu.restrictPolicy initial horizon scheduler owner (fixedLatePolicy owner)

theorem decode_properContinuation
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) :
    app.decodePolicy (rawMenu.embedPolicy initial horizon scheduler owner
      (properContinuation rule owner)) = properPolicy rule owner := by
  apply rawMenu.decode_restrictPolicy_of_covered
  intro past view response supported
  exact PhaseCount.onePacketMenu_in_raw runtime leaks bounds owner past view
    (properPolicy_counted rule owner past view response supported)

theorem decode_fixedLateContinuation (owner : Player) :
    app.decodePolicy (rawMenu.embedPolicy initial horizon scheduler owner
      (fixedLateContinuation owner)) = fixedLatePolicy owner := by
  apply rawMenu.decode_restrictPolicy_of_covered
  intro past view response supported
  exact PhaseCount.onePacketMenu_in_raw runtime leaks bounds owner past view
    (fixedLatePolicy_counted owner past view response supported)

theorem fixedLatePolicy_aliceFirst :
    fixedLatePolicy alice (aliceFirst.recall alice) (aliceFirst.observe app alice) =
      PMF.pure ⟨none⟩ := by
  classical
  unfold fixedLatePolicy
  exact ite_eq_left ⟨initialState_attempt, initialState_clock⟩

theorem fixedLatePolicy_bobQuiet :
    fixedLatePolicy bob ((bobFirst ⟨none⟩).recall bob)
        ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩ := by
  classical
  unfold fixedLatePolicy
  exact ite_eq_left ⟨initialState_attempt, initialState_clock⟩

/-- A count-correct current response preserves just this sender's clean
record. Other authors' packets and earlier forbidden foreign traffic remain. -/
theorem ownPermitted_counted_respond (who : Player) (execution : app.Execution)
    (response : app.Action) (valid : OwnPermitted who execution)
    (allowed : response ∈ countedMenu.actions who (execution.recall who)
      (execution.observe app who)) : OwnPermitted who (execution.respond app who response) := by
  classical
  have permitted := (PhaseCount.mem_onePacketActions runtime leaks bounds who
    (execution.recall who) (execution.observe app who) response).mp allowed
  rcases permitted.2 with quiet | ⟨material, selected, verdict⟩
  · exact ownPermitted_respond who who execution response valid (fun _ => quiet)
  · cases response with
    | mk transmission =>
        change transmission = some material at selected
        subst transmission
        refine ⟨PhaseCount.countRecall_respond runtime leaks execution valid.1 who _, ?_⟩
        obtain ⟨inputs, fresh, retained⟩ :=
          PhaseCount.permits_respond runtime leaks execution valid.1 who material
        intro message present owner
        rw [inputs] at present
        rcases List.mem_append.mp present with old | current
        · rw [retained message old]
          exact valid.2 message old owner
        · rw [List.mem_singleton.mp current, fresh]
          exact verdict

theorem properPolicy_ownPermitted_invariant
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (who : Player)
    (players : Player → app.Policy) (selected : players who = properPolicy rule who) :
    app.PolicyInvariant players (OwnPermitted who) where
  respond execution actor response valid supported := by
    by_cases same : actor = who
    · subst actor
      rw [selected] at supported
      exact ownPermitted_counted_respond who execution response valid
        (properPolicy_counted rule who _ _ response supported)
    · exact ownPermitted_respond who actor execution response valid
        (fun equal => (same equal).elim)
  environment execution next command valid moved :=
    ownPermitted_environment who execution next command valid moved


/-- The fixed late deviation stays count-correct even when the other owner uses
an arbitrary raw continuation. This includes every protected retry callback. -/
theorem fixedLatePolicy_ownPermitted_invariant (who : Player)
    (players : Player → app.Policy) (selected : players who = fixedLatePolicy who) :
    app.PolicyInvariant players (OwnPermitted who) where
  respond execution actor response valid supported := by
    by_cases same : actor = who
    · subst actor
      rw [selected] at supported
      exact ownPermitted_counted_respond who execution response valid
        (fixedLatePolicy_counted who _ _ response supported)
    · exact ownPermitted_respond who actor execution response valid
        (fun equal => (same equal).elim)
  environment execution next command valid moved :=
    ownPermitted_environment who execution next command valid moved

/-- The whole native deviation preserves the sender's clean record on every
supported physical history, rather than only under the assessed baseline law. -/
theorem fixedLateContinuation_ownPermitted_run
    (profile : ∀ who, rawModel.BehavioralPolicy who) (who : Player)
    (history : rawProtocol.History) (valid :
      ReactiveApplication.executionInvariant (OwnPermitted who) history.state)
    (fuel : Nat) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralFrom
      (Profile.update (sig := rawModel.behavioralSignature)
        profile who (fixedLateContinuation who)) fuel history).support) :
    ReactiveApplication.executionInvariant (OwnPermitted who) final.state := by
  classical
  let updated := Profile.update (sig := rawModel.behavioralSignature)
    profile who (fixedLateContinuation who)
  let players := rawMenu.decodeProfile initial horizon scheduler updated
  have selected : players who = fixedLatePolicy who := by
    simpa [players, updated, ReactiveApplication.ResponseMenu.decodeProfile,
      Profile.update_same] using decode_fixedLateContinuation who
  have invariant := fixedLatePolicy_ownPermitted_invariant who players selected
  have projection := rawMenu.run_map_controlSteps initial horizon scheduler updated fuel history
  have stateSupported : final.state ∈
      ((rawModel.runBehavioralFrom updated fuel history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [projection] at stateSupported
  have propagate (count : Nat) (state : app.ProtocolState)
      (member : state ∈ ((fun law => law.bind
        (app.controlStep initial horizon scheduler players))^[count]
          (PMF.pure history.state)).support) :
      ReactiveApplication.executionInvariant (OwnPermitted who) state := by
    induction count generalizing state with
    | zero =>
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact valid
    | succ count ih =>
        rw [Function.iterate_succ_apply'] at member
        obtain ⟨before, prior, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
        exact invariant.controlStep initial horizon scheduler
          (fun state _ => ownPermitted_initial who state) before state (ih before prior) reached
  exact propagate fuel final.state stateSupported

/-- No hidden later charge is subtracted from the fixed late deviation's native
terminal utility. The identity holds on its original full-history runner. -/
theorem fixedLateContinuation_payoff_eq_base
    (profile : ∀ who, rawModel.BehavioralPolicy who) (who : Player)
    (history : rawProtocol.History) (valid :
      ReactiveApplication.executionInvariant (OwnPermitted who) history.state) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature)
        profile who (fixedLateContinuation who)) history) (rawPayoff who) =
      expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature)
          profile who (fixedLateContinuation who)) history)
        (fun final => basePayoff final.state who) := by
  classical
  rw [rawModel.runBehavioralTerminalFrom_eq_remaining canonicalCertificate _
    (rawMenu.bounded initial horizon scheduler)]
  apply expect_congr_on_support
  intro final supported
  have clean := fixedLateContinuation_ownPermitted_run profile who history valid _ final supported
  have zero := ownPermitted_charge_zero who final clean
  simp only [rawPayoff, netPayoff, TerminalAudit.utility, zero, zero_mul, sub_zero]

theorem initial_binding_request (owner : Player) :
    initialState.SeedRequest owner ⟨originalAttempt, bindingEvent owner⟩ := by
  classical
  have invariant := (PhaseRuntimeState.initial_invariant plan
    (encodeInputs (Env.empty (CellVal simpleExpr)))).1
  rw [← initialState_attempt]
  apply (initialState.requests_publicView invariant owner _).mp
  have available : ready owner (bindingEvent owner)
      (initialExecution.observeEnvironment app) = true := by
    fin_cases owner
    · simpa [bindingEvent] using initial_bindings_ready.1
    · simpa [bindingEvent] using initial_bindings_ready.2
  exact of_decide_eq_true available

theorem counted_aliceFirst_trace : Nonempty ((countedMenu.protocol initial horizon scheduler).Trace
    (some ⟨63, some alice, aliceFirst⟩)) := by
  obtain ⟨initialTrace⟩ := countedMenu.trace_initial initial horizon scheduler initialState
    (by rw [initial_eq_pure]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  apply countedMenu.trace_environment initial horizon scheduler 63 initialExecution aliceFirst
    (.activate alice) initialTrace
  · rw [scheduler_first]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem counted_bobQuiet_trace : Nonempty ((countedMenu.protocol initial horizon scheduler).Trace
    (some ⟨62, some bob, bobFirst ⟨none⟩⟩)) := by
  obtain ⟨first⟩ := counted_aliceFirst_trace
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler 63 aliceFirst alice
    ⟨none⟩ first (PhaseCount.silence_onePacket runtime leaks bounds alice _ _)
  apply countedMenu.trace_environment initial horizon scheduler 62 (aliceResponded ⟨none⟩)
    (bobFirst ⟨none⟩) (.activate bob) responded
  · rw [scheduler_after_alice]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- The actual first Bob menu contains only a fresh owned binding declaration;
private preparations are retained without a successful-value restriction. -/
theorem bobQuiet_counted_binding_shape (material : app.Submission)
    (counted : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob
      ((bobFirst ⟨none⟩).recall bob) ((bobFirst ⟨none⟩).observe app bob)) :
    ∃ serial preparation evidence,
      material = ⟨⟨.commitment bobBinding (bob, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      (bobFirst ⟨none⟩).application.current.native.candidates.lookup
        (bob, .prepared serial) = .fresh := by
  classical
  obtain ⟨trace⟩ := counted_bobQuiet_trace
  have request : (bobFirst ⟨none⟩).application.SeedRequest bob
      ⟨(bobFirst ⟨none⟩).application.attempt, bobBinding⟩ := by
    change initialState.SeedRequest bob ⟨initialState.attempt, bobBinding⟩
    rw [initialState_attempt]
    exact initial_binding_request bob
  exact PhaseCount.onePacket_binding_shape runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon scheduler 62 bob (bobFirst ⟨none⟩)
    trace bobBinding .bool binding_layouts.2 request material counted

/-- The raw game's supported first Bob transmissions have the original owned
binding address and a fresh slot. This retains unusable preparations verbatim. -/
theorem bobQuiet_supported_binding_shape
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (choice : rawModel.Choice bob bobQuietSite.1)
    (supported : choice ∈ (assessment.strategy bob bobQuietSite.1).support)
    (material : app.Submission) (selected : choice.1 = some ⟨some material⟩) :
    ∃ serial preparation evidence,
      material = ⟨⟨.commitment bobBinding (bob, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      (bobFirst ⟨none⟩).application.current.native.candidates.lookup
        (bob, .prepared serial) = .fresh := by
  exact bobQuiet_counted_binding_shape material
    (bobQuiet_supported_response_counted assessment equilibrium choice supported
      ⟨some material⟩ selected)

end Vegas.Examples.CommitSeedSignalling
