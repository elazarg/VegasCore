/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPayoffs
import Vegas.Examples.CommitSeedBroadcastInitializedTrace
import Vegas.Examples.CommitSeedBroadcastRealization
import Vegas.Examples.CommitSeedBroadcastProperSurvival
import Vegas.Examples.CommitSeedBroadcastPublicationReceipts
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Exact initialized native payoff from actual exclusion and failure events -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  GameTheory.Enforcement

variable (clock : Nat)

/-- Completion and the zero count charge are derived from the genuine
initialized finite-menu run. No later action or successful delivery is assumed. -/
theorem initialized_counted_netPayoff_formula
    (profile : ∀ who, countedModel.BehavioralPolicy who) (final : app.Execution)
    (supported : final ∈ (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon
      initialExecution).support) (owner : Player) :
    netPayoff (app.finished final) owner =
      if owner ∈ final.application.current.excluded then -(3 / 2) else
        if ∃ other : Player, other ≠ owner ∧
          RecoveryState.publicationFailed final.application.current.native
            (revealEvent other) = true then 1 else 0 := by
  have covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (response : app.Action)
      (chosen : response ∈ (countedMenu.decodeProfile initial horizon scheduler profile
        who past view).support) : response ∈ countedMenu.actions who past view :=
    countedMenu.decode_embedPolicy_covered initial horizon scheduler who (profile who)
      past view response chosen
  obtain ⟨trace⟩ := countedMenu.trace_roundsFrom initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler profile) covered horizon le_rfl final
    (by simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
      initialExecution] using supported)
  have trace : countedProtocol.Trace (some ⟨0, none, final⟩) := by
    simpa only [Nat.sub_self] using trace
  have complete := scheduler_completesPlay ⟨0, none, final⟩
    (countedMenu.toRawTrace initial horizon scheduler trace) ⟨rfl, rfl⟩
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    scheduler evidenceService ⟨some ⟨0, none, final⟩, trace⟩ owner
  change TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, final⟩) owner = 0 at zero
  change basePayoff (some ⟨0, none, final⟩) owner -
    TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, final⟩) owner * deposit owner = _
  rw [zero, zero_mul, sub_zero]
  exact basePayoff_terminal_formula ⟨0, none, final⟩ complete owner

/-- A counted proper continuation attains the maximum reward whenever its
original binding is admitted and a foreign original binding misses. -/
theorem initialized_proper_foreign_miss_payoff
    (profile : ∀ who, countedModel.BehavioralPolicy who) (owner : Player)
    (selected : countedMenu.decodeProfile initial horizon scheduler profile owner =
      scheduledProperPolicy clock owner) (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon
        initialExecution).support)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final)
    (foreign : ∃ other : Player, other ≠ owner ∧
      ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate other) other final) :
    netPayoff (app.finished final) owner = 1 := by
  classical
  have active := initialized_scheduled_proper_original_binding_survives clock profile owner selected
    final reached accepted
  have complete := scheduler_completesPlay
  have covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (response : app.Action)
      (chosen : response ∈ (countedMenu.decodeProfile initial horizon scheduler profile
        who past view).support) : response ∈ countedMenu.actions who past view :=
    countedMenu.decode_embedPolicy_covered initial horizon scheduler who (profile who)
      past view response chosen
  obtain ⟨trace⟩ := countedMenu.trace_roundsFrom initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler profile) covered horizon le_rfl final
    (by simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
      initialExecution] using reached)
  have trace : countedProtocol.Trace (some ⟨0, none, final⟩) := by
    simpa only [Nat.sub_self] using trace
  have terminal := complete ⟨0, none, final⟩
    (countedMenu.toRawTrace initial horizon scheduler trace) ⟨rfl, rfl⟩
  obtain ⟨other, different, missing⟩ := foreign
  have failed := initialized_missing_original_binding_publication_failed
    (countedMenu.decodeProfile initial horizon scheduler profile) final reached terminal
      other missing
  rw [initialized_counted_netPayoff_formula profile final reached owner,
    ite_eq_right active, ite_eq_left ⟨other, different, failed⟩]

end Vegas.Examples.CommitSeedBroadcast
