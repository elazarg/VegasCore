/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseEventSourceView
import Vegas.EventGraph.ReadySemanticStability
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseReadiness

/-! # Semantic source information while a physical binding survives -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- The exact semantic decoder ignores the new physical scheduling transcript
when its visible source cells and original owned actions are unchanged. -/
private theorem phaseSourceView?_eq_of_semantics (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (before after : (phaseApplication runtime leaks).Execution)
    (stores : (serviceGraph setup mode).playerStore who
        after.application.current.native.config.store =
      (serviceGraph setup mode).playerStore who before.application.current.native.config.store)
    (history : (serviceGraph setup mode).ownCompletions who
        after.application.current.native.config.history =
      (serviceGraph setup mode).ownCompletions who
        before.application.current.native.config.history) :
    phaseSourceView? setup mode runtime leaks who event
      (after.observe (phaseApplication runtime leaks) who) =
    phaseSourceView? setup mode runtime leaks who event
      (before.observe (phaseApplication runtime leaks) who) := by
  unfold phaseSourceView?
  rw [dite_eq_left (show
    (after.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl),
    dite_eq_left (show
      (before.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
  change decodeEventView? setup.program _ _ who event
      ((serviceGraph setup mode).playerStore who after.application.current.native.config.store)
      (decodeCompletions setup.program
        (((serviceGraph setup mode).ownCompletions who
          after.application.current.native.config.history).map
            (setup.eventGraph.fromModeCompletion mode))) =
    decodeEventView? setup.program _ _ who event
      ((serviceGraph setup mode).playerStore who before.application.current.native.config.store)
      (decodeCompletions setup.program
        (((serviceGraph setup mode).ownCompletions who
          before.application.current.native.config.history).map
            (setup.eventGraph.fromModeCompletion mode)))
  rw [stores, history]

/-- Arbitrary actual responses and environment commands cannot change the
semantic source view of an owned binding that stays ready in the same attempt.
The full physical observation and its conditional likelihood remain separate. -/
theorem phaseSourceView?_runRounds (players : Player → (phaseApplication runtime leaks).Policy)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (count : Nat)
    (before after : (phaseApplication runtime leaks).Execution)
    {inputs : (serviceGraph setup mode).Inputs} (valid : before.application.Invariant inputs)
    (ordered : before.application.Ordered)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds scheduler players count
      before).support) (same : before.application.attempt = after.application.attempt)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (beforeReady : before.application.current.native.config.cut.Ready event)
    (afterReady : after.application.current.native.config.cut.Ready event)
    (acting : (serviceGraph setup mode).actor? event = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication) :
    phaseSourceView? setup mode runtime leaks who event
      (after.observe (phaseApplication runtime leaks) who) =
    phaseSourceView? setup mode runtime leaks who event
      (before.observe (phaseApplication runtime leaks) who) := by
  have afterValid :=
    ((phaseApplication_invariant runtime leaks inputs).policyInvariant
      (phaseApplication runtime leaks) players).runRounds
      scheduler count before after valid reached
  obtain ⟨stored, retained⟩ := phase_runRounds_semantic_extension runtime leaks players scheduler
    count before after ordered reached same
  obtain ⟨stores, history⟩ :=
    (serviceGraph_revealRelaxedOrdered setup mode).ready_semantics_eq_of_extension
      before.application.current.native.config
      after.application.current.native.config valid.active.reachable afterValid.active.reachable
      who event beforeReady afterReady acting notPublication stored retained
  exact phaseSourceView?_eq_of_semantics setup mode runtime leaks who event before after stores
    history

/-- At genuine initialized histories all required native and ordering facts
are derived from the real phased execution. Unsent waiting is included without
restricting the allowed private preparations or foreign hidden completions. -/
theorem phaseSourceView?_runRounds_of_history
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (initial.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (players : Player → (phaseApplication runtime leaks).Policy) (count : Nat)
    (after : (phaseApplication runtime leaks).Execution)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds scheduler players count
      control.execution).support)
    (same : control.execution.application.attempt = after.application.attempt)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (beforeReady : control.execution.application.current.native.config.cut.Ready event)
    (afterReady : after.application.current.native.config.cut.Ready event)
    (acting : (serviceGraph setup mode).actor? event = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication) :
    phaseSourceView? setup mode runtime leaks who event
      (after.observe (phaseApplication runtime leaks) who) =
    phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) := by
  have invariant : (phaseApplication runtime leaks).Invariant
      (fun state => ∃ inputs, state.Invariant inputs) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro state owner material ⟨inputs, valid⟩
      exact ⟨inputs, (phaseApplication_invariant runtime leaks inputs).submit state owner material
        valid⟩
    · rintro state message next ⟨inputs, valid⟩ accepted
      exact ⟨inputs, (phaseApplication_invariant runtime leaks inputs).handle state message next
        valid accepted⟩
    · rintro state command next ⟨inputs, valid⟩ supported
      exact ⟨inputs, (phaseApplication_invariant runtime leaks inputs).environment state command
        next valid supported⟩
  have valid := invariant.history (initial.map (PhaseRuntimeState.initial plan)) horizon scheduler
    (fun state supported => by
      obtain ⟨inputs, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact ⟨inputs, (PhaseRuntimeState.initial_invariant plan inputs).1⟩) trace
  obtain ⟨inputs, native⟩ := valid
  have ordered := (phaseApplication_seedOrder runtime leaks).history
    (initial.map (PhaseRuntimeState.initial plan)) horizon scheduler
    (fun state supported => by
      obtain ⟨inputs, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_ordered plan inputs) trace
  exact phaseSourceView?_runRounds setup mode runtime leaks players scheduler count
    control.execution after native ordered reached same who event beforeReady afterReady acting
      notPublication

end Vegas
