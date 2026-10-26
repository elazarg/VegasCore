/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.ProgramPayoffs
import Vegas.Game.RevealService
import Vegas.Source.SetupProtocolBehavioral
import Vegas.Pending.PhaseProposalOrigin

/-! # A source decision after an owner's failed publication

Value-only commitment admission still permits withholding a publication, followed
by another independent commitment of the same owner. The source program pays for
that later publication. The separately declared exit receipt is minus one.
A later same-owner phase requesting decision cannot retain an earlier public
failure. This distinguishes the decision interfaces; it does not assert that
every abstract Nash correspondence is impossible.
-/

noncomputable section

namespace Vegas.Examples.FailureContinuationScope

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

abbrev Player := Unit
abbrev owner : Player := ()

def context : SourceCtx Player simpleExpr := [(0, .commitment owner .bool)]

def guard : SourceGuard simpleExpr ((1, .publication .bool) :: context) owner 2 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun cell => nomatch cell

def continuation : SourceProgram Player simpleExpr ((1, .publication .bool) :: context) ∅ :=
  .commit 2 owner (by decide) guard <|
  .reveal 3 owner 2 (by decide) .here (by decide) <|
  .ret [(owner, .ite (.getResultD (.var 3 .here) (.constBool false))
    (.constInt 1) (.constInt 0))]

def program : SourceProgram Player simpleExpr context {0} :=
  .reveal 1 owner 0 (by decide) .here (by decide) continuation

def initial : State simpleExpr context := Env.cons (.success true) (Env.empty _)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := PMF.pure initial
  obligations := {0}
  program := program
  accounts := rfl
  exitTransfers := fun _ => -1

def profile (later : Bool) : BehavioralProfile program := fun _ =>
  ⟨fun _ _ => PMF.pure false,
    ⟨fun _ _ => PMF.pure (.success later), ⟨fun _ _ => PMF.pure true, PUnit.unit⟩⟩⟩

/-- The failure is a legal disclosure decision even under value-only admission. -/
theorem profile_admitted (later : Bool) (who : Player) :
    (profile later who).Admitted program (CommitmentInterface.values program) := by
  change (∀ (_ : owner = who) _ choice, choice ∈ (PMF.pure (.success later)).support →
      CommitmentAdmission.Admits .values choice) ∧ True
  refine ⟨?_, trivial⟩
  intro _ _ choice supported
  have same := (PMF.mem_support_pure_iff _ _).mp supported
  subst choice
  trivial

def final (later : Bool) : State simpleExpr program.terminalCtx :=
  Env.cons (.success later) <| Env.cons (.success later) <|
    Env.cons .failure initial

/-- The actual evaluator retains the first failure and the later success. -/
theorem run_profile (later : Bool) : setup.run (profile later) = PMF.pure (final later) := by
  change (PMF.pure initial).bind (SourceProgram.run program (profile later)) = _
  simp only [PMF.pure_bind, SourceProgram.run, runWith, program, continuation, profile,
    revealKernel, commitKernel, afterReveal, afterCommit]
  rfl

theorem terminal_results (later : Bool) :
    (final later).get (.there (.there .here)) = PublicationResult.failure ∧
      (final later).get .here = PublicationResult.success later := ⟨rfl, rfl⟩

/-- The retained `ret` instruction pays one precisely for the later true choice. -/
theorem terminal_transfer (later : Bool) :
    transferAmount (program.evaluatePayoffs (final later)) owner = if later then 1 else 0 := by
  cases later <;> rfl

/-- Joint source outcome and executable receipt, including after the failure. -/
theorem source_joint_law (later : Bool) :
    (setup.run (profile later)).map (fun terminal =>
      (terminal.get (.there (.there .here)), terminal.get .here,
        transferAmount (program.evaluatePayoffs terminal) owner)) =
      PMF.pure (PublicationResult.failure, PublicationResult.success later,
        if later then 1 else 0) := by
  rw [run_profile, PMF.pure_map]
  rw [terminal_transfer]
  rfl

abbrev source := setup.executionProtocol (CommitmentInterface.values program)

def entry : setup.ProtocolState :=
  some (SourceProgram.ProtocolState.entry program (setup.initialConfig initial))

def afterFailure : setup.ProtocolState :=
  some (Sum.inr (SourceProgram.ProtocolState.entry continuation
    (revealSuccessor 1 (.here : HasVar context 0 (.commitment owner .bool))
      (setup.initialConfig initial) false)))

private theorem draw_legal : source.Legal none (fun _ => none) := by
  exact ⟨fun impossible => impossible, fun _ impossible => impossible⟩

private theorem draw_supported :
    entry ∈ (source.step none ⟨fun _ => none, draw_legal⟩).support := by
  change entry ∈ ((PMF.pure initial).map _).support
  simp only [PMF.pure_map, PMF.mem_support_pure_iff]
  rfl

private theorem withholding_legal :
    source.Legal entry (fun _ => some (.reveal owner 0 false)) := by
  refine ⟨fun impossible => impossible, ?_⟩
  intro who
  change some owner = some who ∧ _
  refine ⟨by cases who; rfl, false, rfl⟩

private theorem withholding_supported : afterFailure ∈ (source.step entry
    ⟨fun _ => some (.reveal owner 0 false), withholding_legal⟩).support := by
  change afterFailure ∈ ((PMF.pure _).map some).support
  simp only [PMF.pure_map, PMF.mem_support_pure_iff]
  rfl

/-- The post-failure source position has an actual legal initialized history. -/
def failureTrace : source.Trace afterFailure :=
  .extend (.extend .start (fun _ => none) draw_legal draw_supported)
    (fun _ => some (.reveal owner 0 false)) withholding_legal withholding_supported

/-- At that reachable position either later Boolean commitment remains legal. -/
theorem later_commit_available (later : Bool) :
    (setup.informationModel (CommitmentInterface.values program)).menu owner
      (setup.protocolObserve owner afterFailure)
      (some (.commit owner 2 .bool (.success later))) := by
  exact ⟨rfl, .success later, trivial, rfl⟩

abbrev compiled := graph setup
abbrev firstEvent : compiled.EventId := ⟨0, by decide⟩
abbrev laterEvent : compiled.EventId := ⟨1, by decide⟩

/-- No actual phase history preserving the earlier public failure can expose
the later requesting callback of the same owner. The prior, scheduler, horizon,
leak rule and phase plan are arbitrary. -/
theorem phase_no_later_request_after_failure
    (runtime : EventGraphRuntime compiled)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket compiled))
    (plan : RuntimePhasePlan compiled) (inputs : PMF compiled.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (failed : current.execution.application.current.native.PublicFailure firstEvent)
    (attempt : CommitAttemptId) :
    ¬ current.execution.application.SeedRequest owner ⟨attempt, laterEvent⟩ := by
  intro request
  exact (PhaseProposal.requested_earlier_own_completed_not_failed runtime leaks plan
    (serviceGraph_revealRelaxedOrdered setup .sequential) inputs horizon scheduler current trace
    owner ⟨attempt, laterEvent⟩ request firstEvent rfl (by change 0 < 1; decide)).2 failed

/-- Preparing a later binding in advance cannot bypass permanent exclusion:
every such packet is rejected after the earlier failure on an actual history. -/
theorem phase_rejects_later_binding_after_failure
    (runtime : EventGraphRuntime compiled)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket compiled))
    (plan : RuntimePhasePlan compiled) (inputs : PMF compiled.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (failed : current.execution.application.current.native.PublicFailure firstEvent)
    (message : Message Player (CommitAttemptPacket compiled)) (candidate : Handle compiled)
    (named : message.payload.packet.call = .commitment laterEvent candidate) :
    current.execution.application.handle runtime message = none := by
  have excluded := (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    trace).active.covered firstEvent owner rfl failed
  have barred : current.execution.application.current.excludedCall
      message.payload.packet.call = true := by
    simp only [RecoveryState.excludedCall, named, Payload.event?, RecoveryState.excludedEvent]
    change decide (owner ∈ current.execution.application.current.excluded) = true
    exact decide_eq_true excluded
  simp only [PhaseRuntimeState.handle, barred, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

end Vegas.Examples.FailureContinuationScope
