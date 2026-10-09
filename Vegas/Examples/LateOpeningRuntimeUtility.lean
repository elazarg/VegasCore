/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeReadout
import Vegas.Examples.LateOpeningRuntimeService
import Vegas.Game.RevealServicePayoffs
import Vegas.Game.SourceServiceAudit
import Vegas.Source.Forfeit

/-! # Source utilities and authentic charges for the initialized native game

The native base utility reads the actual compiled terminal store. Publication
failure costs the owner one source forfeit; successful publication has none.
The audit lemmas concern authentic sampled envelopes and the actual settled
record. They impose no condition on the time a permitted packet was emitted.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeUtility

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout

/-- Each player owns exactly one source publication instruction. -/
theorem alice_failed_reveals (terminal : State simpleExpr program.terminalCtx) :
    failedReveals program alice (publicOutcome program terminal) =
      if (terminal.get alicePublication).isSuccess then 0 else 1 := by
  have viewed : (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      ((sourcePublicEnv terminal).get (publicRef alicePublication)) =
        terminal.get alicePublication := by
    rw [sourcePublicEnv_get_publicRef]
    exact (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool).apply_symm_apply _
  cases result : terminal.get alicePublication <;>
    simp [failedReveals, revealCells, program, RevealCell.failed, publicOutcome,
      SourceProgram.terminalRef, List.filter, viewed, PublicationResult.isSuccess,
      alice, bob, result]

theorem bob_failed_reveals (terminal : State simpleExpr program.terminalCtx) :
    failedReveals program bob (publicOutcome program terminal) =
      if (terminal.get bobPublication).isSuccess then 0 else 1 := by
  have viewed : (IExpr.ResultTypes.valueEquiv (L := simpleExpr) (.range 0 5))
      ((sourcePublicEnv terminal).get (publicRef bobPublication)) =
        terminal.get bobPublication := by
    rw [sourcePublicEnv_get_publicRef]
    exact (IExpr.ResultTypes.valueEquiv (L := simpleExpr) (.range 0 5)).apply_symm_apply _
  cases result : terminal.get bobPublication <;>
    simp [failedReveals, revealCells, program, RevealCell.failed, publicOutcome,
      SourceProgram.terminalRef, List.filter, viewed, PublicationResult.isSuccess,
      alice, bob, result]

/-- The actual source failure policy, including the immutable private inputs. -/
def sourceUtility (reward forfeit : ℝ) (terminal : State simpleExpr program.terminalCtx)
    (who : Player) : ℝ :=
  forfeitUtility program forfeit (grossUtility reward)
    (setup.parameterOutcome parameter terminal) who

/-- The public two-late backend uses the unchanged compiler's typed readout. -/
def nativeBaseUtility (reward forfeit : ℝ) :
    LateOpeningRuntimeService.app.ProtocolState → Player → ℝ :=
  serviceBaseUtility setup .sequential LateOpeningRuntimeService.deadline
    LateOpeningRuntimeService.leaks (sourceUtility reward forfeit)

theorem nativeBaseUtility_of_readout (reward forfeit : ℝ)
    (state : LateOpeningRuntimeService.app.ProtocolState)
    (terminal : State simpleExpr program.terminalCtx)
    (decoded : serviceSourceReadout setup .sequential LateOpeningRuntimeService.deadline
      LateOpeningRuntimeService.leaks state = some terminal) (who : Player) :
    nativeBaseUtility reward forfeit state who = sourceUtility reward forfeit terminal who := by
  unfold nativeBaseUtility serviceBaseUtility
  rw [decoded]
  rfl

/-- Actual native initialization and graph completion provide a complete
typed readout; no guessed default payload replaces an expired instruction. -/
theorem nativeReadout_complete (horizon : Nat)
    (scheduler : LateOpeningRuntimeService.app.Scheduler)
    (control : LateOpeningRuntimeService.app.Control)
    (trace : (LateOpeningRuntimeService.app.protocol LateOpeningRuntimeService.initial
      horizon scheduler).Trace (some control))
    (completed : control.execution.application.config.cut.Terminal) :
    ∃ bit label aliceResult binding answer,
      serviceSourceReadout setup .sequential LateOpeningRuntimeService.deadline
        LateOpeningRuntimeService.leaks (some control) =
          some (terminalStateOf bit label aliceResult binding answer) := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime
    LateOpeningRuntimeService.leaks horizon scheduler control trace
  obtain ⟨aliceResult, binding, answer, decoded⟩ := terminal_decode_exists
    control.execution.application bit label valid completed
  refine ⟨bit, label, aliceResult, binding, answer, ?_⟩
  unfold serviceSourceReadout
  rw [Option.bind_some, ite_eq_left completed]
  exact decoded

/-- Joint successful publications determine the full initialized source
terminal state. The private answer binding is inferred from actual reachability. -/
theorem nativeReadout_success (control : LateOpeningRuntimeService.app.Control)
    (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) control.execution.application)
    (completed : control.execution.application.config.cut.Terminal)
    (publishedBit : Bool) (answer : Answer)
    (aliceStored : control.execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit))
    (bobStored : control.execution.application.config.store (.inr bobRevealEvent) =
      some (.success answer)) :
    serviceSourceReadout setup .sequential LateOpeningRuntimeService.deadline
      LateOpeningRuntimeService.leaks (some control) =
        some (finalState bit label true answer true) := by
  have sameBit := alice_success_from_initialized_bit _ bit label valid publishedBit aliceStored
  subst publishedBit
  have bound := bob_success_from_binding _ _ valid.reachable answer bobStored
  have decoded := decode_terminalStateOf control.execution.application bit label
    (.success bit) (.success answer) (.success answer) valid.reachable.inputs_eq
      aliceStored bound bobStored
  unfold serviceSourceReadout
  rw [Option.bind_some, ite_eq_left completed]
  exact decoded

theorem sourceUtility_alice (reward forfeit : ℝ)
    (terminal : State simpleExpr program.terminalCtx) :
    sourceUtility reward forfeit terminal alice =
      grossUtility reward (setup.parameterOutcome parameter terminal) alice -
        if (terminal.get alicePublication).isSuccess then 0 else forfeit := by
  unfold sourceUtility forfeitUtility
  change grossUtility reward (setup.parameterOutcome parameter terminal) alice -
    forfeit * failedReveals program alice (publicOutcome program terminal) = _
  rw [alice_failed_reveals]
  split <;> simp

theorem sourceUtility_bob (reward forfeit : ℝ)
    (terminal : State simpleExpr program.terminalCtx) :
    sourceUtility reward forfeit terminal bob =
      grossUtility reward (setup.parameterOutcome parameter terminal) bob -
        if (terminal.get bobPublication).isSuccess then 0 else forfeit := by
  unfold sourceUtility forfeitUtility
  change grossUtility reward (setup.parameterOutcome parameter terminal) bob -
    forfeit * failedReveals program bob (publicOutcome program terminal) = _
  rw [bob_failed_reveals]
  split <;> simp

/-- A single source publication gives the full native base payoff range,
without assuming clean responses or successful binding. -/
theorem sourceUtility_alice_bounds {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (terminal : State simpleExpr program.terminalCtx) :
    -forfeit ≤ sourceUtility reward forfeit terminal alice ∧
      sourceUtility reward forfeit terminal alice ≤ reward := by
  obtain ⟨lower, upper⟩ := alice_gross_bounds rewardNonnegative
    (setup.parameterOutcome parameter terminal)
  rw [sourceUtility_alice]
  split <;> constructor <;> linarith

theorem sourceUtility_bob_bounds {forfeit : ℝ} (forfeitNonnegative : 0 ≤ forfeit)
    (reward : ℝ) (terminal : State simpleExpr program.terminalCtx) :
    -forfeit ≤ sourceUtility reward forfeit terminal bob ∧
      sourceUtility reward forfeit terminal bob ≤ 1 := by
  obtain ⟨lower, upper⟩ := bob_gross_bounds reward (setup.parameterOutcome parameter terminal)
  rw [sourceUtility_bob]
  split <;> constructor <;> linarith

@[simp] theorem parameterOutcome_terminalStateOf (bit : Bool) (label : Fin 3)
    (aliceResult : PublicationResult Bool)
    (binding answer : PublicationResult Answer) :
    setup.parameterOutcome parameter (terminalStateOf bit label aliceResult binding answer) =
      ((bit, label), publicOutcome program
        (terminalStateOf bit label aliceResult binding answer)) :=
  by
    change (parameter (initialState program
      (terminalStateOf bit label aliceResult binding answer)), _) = _
    rw [show initialState program
      (terminalStateOf bit label aliceResult binding answer) = sourceInitial bit label from rfl,
    parameter_sourceInitial]
    rfl

theorem sourceUtility_success (reward forfeit : ℝ) (bit : Bool) (label : Fin 3)
    (answer : Answer) (who : Player) :
    sourceUtility reward forfeit (finalState bit label true answer true) who =
      grossUtility reward ((bit, label),
        publicOutcome program (finalState bit label true answer true)) who := by
  change sourceUtility reward forfeit
    (terminalStateOf bit label (.success bit) (.success answer) (.success answer)) who = _
  unfold sourceUtility forfeitUtility
  rw [parameterOutcome_terminalStateOf]
  change _ - forfeit * failedReveals program who
    (publicOutcome program (finalState bit label true answer true)) = _
  have players : who = alice ∨ who = bob := by
    change Fin 2 at who
    fin_cases who <;> simp [alice, bob]
  rcases players with rfl | rfl
  · rw [alice_failed_reveals]
    simp [terminalStateOf, finalState, PublicationResult.isSuccess]
  · rw [bob_failed_reveals]
    simp [terminalStateOf, finalState, PublicationResult.isSuccess]

theorem sourceUtility_intended (reward forfeit : ℝ) (bit : Bool) (label : Fin 3) :
    sourceUtility reward forfeit (finalState bit label true safe true) alice = reward / 2 ∧
    sourceUtility reward forfeit (finalState bit label true safe true) bob = 2 / 5 := by
  rw [sourceUtility_success, sourceUtility_success]
  exact intended_gross reward bit label

/-- Failed final publication has zero gross payoff and exactly one Bob forfeit,
even if the private answer binding failed or was malformed. -/
theorem sourceUtility_bob_failure (reward forfeit : ℝ) (bit : Bool) (label : Fin 3)
    (aliceResult : PublicationResult Bool) (binding : PublicationResult Answer) :
    sourceUtility reward forfeit (terminalStateOf bit label aliceResult binding .failure) bob =
      -forfeit := by
  rw [sourceUtility_bob, parameterOutcome_terminalStateOf]
  change (0 : ℝ) - forfeit = _
  ring

/-- A public failed Alice opening costs one forfeit even when Bob later succeeds. -/
theorem sourceUtility_alice_failure (reward forfeit : ℝ) (bit : Bool) (label : Fin 3)
    (binding : PublicationResult Answer) (answer : Answer) :
    sourceUtility reward forfeit
      (terminalStateOf bit label .failure binding (.success answer)) alice =
        (if (label.val = 0 ∧ answer.val = 5) ∨ (label.val = 1 ∧ answer.val = 4)
          then reward else 0) - forfeit := by
  rw [sourceUtility_alice, parameterOutcome_terminalStateOf]
  rfl

theorem sourceUtility_bob_after_alice_failure (reward forfeit : ℝ) (bit : Bool)
    (label : Fin 3) (binding : PublicationResult Answer) (answer : Answer) :
    sourceUtility reward forfeit
      (terminalStateOf bit label .failure binding (.success answer)) bob =
        if answer.val = (if bit then 5 else 4) then 1 else 0 := by
  rw [sourceUtility_bob, parameterOutcome_terminalStateOf]
  change (if answer.val = (if bit then 5 else 4) then (1 : ℝ) else 0) - 0 = _
  simp

/-- Alice owns no native binding event, so her publication failure cannot be
charged by the public binding-omission branch. -/
theorem alice_no_binding_omission (view : PublicView nativeGraph) :
    view.missedBindingBy alice = false := by
  classical
  apply decide_eq_false
  rintro ⟨event, owned, missed⟩
  change Fin 3 at event
  fin_cases event
  · have clear := view.missedBinding_of_not_binding aliceEvent (by
      intro owner payload same
      change (EventField.publication .bool : EventField Player simpleExpr) =
        .binding owner payload at same
      cases same)
    rw [clear] at missed
    cases missed
  · change (some bob : Option Player) = some alice at owned
    exact (show bob ≠ alice by decide) (Option.some.inj owned)
  · change (some bob : Option Player) = some alice at owned
    exact (show bob ≠ alice by decide) (Option.some.inj owned)

/-- Any authentic sample of permitted Alice envelopes has zero collected
charge. Other players' malformed traffic is unrestricted. -/
theorem alice_audit_charge_zero
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (control : LateOpeningRuntimeService.app.Control)
    (permitted : ∀ traffic ∈ LateOpeningRuntimeService.app.executionTraffic control.execution,
      traffic.envelope.sender = alice →
        (LateOpeningRuntimeService.runtime.settledRecord LateOpeningRuntimeService.leaks
          control.execution).permits traffic.envelope = true) :
    TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation LateOpeningRuntimeService.leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline
        LateOpeningRuntimeService.leaks sample) (some control) alice = 0 := by
  change TerminalAudit.charge
    (LateOpeningRuntimeService.runtime.serviceAuditObservation LateOpeningRuntimeService.leaks)
    (LateOpeningRuntimeService.runtime.serviceAudit LateOpeningRuntimeService.leaks fun record =>
      LateOpeningRuntimeService.app.sampledTrafficAudit
        (fun traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
        (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
        sample) (some control) alice = 0
  rw [LateOpeningRuntimeService.runtime.serviceAudit_charge, alice_no_binding_omission]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply LateOpeningRuntimeService.app.sampledTrafficAudit_sound
  · exact authentic _
  · exact permitted

/-- If Alice's only authored traffic consists of accepted certified openings,
her charge is zero even if she transmitted them outside the protected window.
The condition is about the actual envelopes and receipts, not their send times. -/
theorem alice_accepted_openings_audit_clean
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (control : LateOpeningRuntimeService.app.Control)
    (openings : ∀ traffic ∈ LateOpeningRuntimeService.app.executionTraffic control.execution,
      traffic.envelope.sender = alice → ∃ bit token,
        traffic.envelope.payload =
          ⟨.opening aliceEvent aliceCandidate ⟨.bool, bit⟩,
            some ⟨aliceCandidate, ⟨.bool, bit⟩⟩, token⟩ ∧
          (traffic.envelope.id, true) ∈ control.execution.receipts) :
    TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation LateOpeningRuntimeService.leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline
        LateOpeningRuntimeService.leaks sample) (some control) alice = 0 := by
  apply alice_audit_charge_zero sample authentic control
  intro traffic member owner
  obtain ⟨bit, token, content, accepted⟩ := openings traffic member owner
  have named : traffic.envelope =
      ⟨traffic.envelope.id, ⟨.opening aliceEvent aliceCandidate ⟨.bool, bit⟩,
        some ⟨aliceCandidate, ⟨.bool, bit⟩⟩, token⟩⟩ := by
    cases envelope : traffic.envelope
    simp only [envelope] at content ⊢
    congr 1
  rw [named]
  exact accepted_alice_opening_permitted _ _ bit token accepted

end Vegas.Examples.LateOpeningRuntimeUtility
