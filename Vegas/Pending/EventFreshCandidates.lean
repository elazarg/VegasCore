/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication
import Interaction.MessageApplicationLaws

/-! # Fresh candidates after arbitrary native prefixes

Every finite native execution leaves an unbounded supply of fresh, unused
prepared handles. This fact does not depend on prescribed policies, intact
event caches, or canonical candidate slots. It supplies material for a new
submission; it does not guarantee that the submission wins inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A finite prefix can occupy only finitely many prepared serials, even when
players, payloads, and the serial namespace are infinite. -/
def State.FreshCandidates (state : State graph) : Prop :=
  ∃ bound : Nat, ∀ who serial, bound ≤ serial →
    state.candidates.lookup (who, .prepared serial) = .fresh ∧
      state.HandleUnused (who, .prepared serial)

private def candidateBound (candidate : Handle graph) : Nat :=
  match candidate.2 with
  | .initial _ => 0
  | .prepared serial => serial + 1

omit [DecidableEq Player] in
private theorem prepared_ne_of_bound (candidate : Handle graph) (who : Player)
    (serial : Nat) (beyond : candidateBound candidate ≤ serial) :
    (who, .prepared serial) ≠ candidate := by
  rcases candidate with ⟨owner, slot⟩
  cases slot with
  | initial input => simp
  | prepared used =>
      intro same
      have equal := Slot.prepared.inj (congrArg Prod.snd same)
      simp only [candidateBound] at beyond
      omega

theorem State.initial_freshCandidates (inputs : graph.Inputs) :
    (State.initial inputs).FreshCandidates := by
  refine ⟨0, fun who serial _ => ⟨State.initial_candidate inputs who (.prepared serial), ?_⟩⟩
  intro field accepted
  obtain ⟨input, owner, payload, _, _, impossible⟩ :=
    State.initial_accepted_eq_some inputs field (who, .prepared serial) accepted
  cases congrArg Prod.snd impossible

theorem privateStep_freshCandidates (state : State graph) (who : Player)
    (command : PrivateCommand graph) (fresh : state.FreshCandidates) :
    (privateStep state who command).FreshCandidates := by
  obtain ⟨bound, available⟩ := fresh
  cases command with
  | prepare used raw =>
      refine ⟨max bound (used + 1), fun owner serial beyond => ?_⟩
      obtain ⟨candidate, unused⟩ := available owner serial (le_trans (le_max_left _ _) beyond)
      have different : (owner, .prepared serial) ≠ ((who, .prepared used) : Handle graph) :=
        prepared_ne_of_bound (who, .prepared used) owner serial
          (le_trans (le_max_right _ _) beyond)
      refine ⟨?_, unused⟩
      exact (state.candidates.lookup_prepare_other who (.prepared used) raw
        (owner, .prepared serial) different).trans candidate
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · cases remembered : state.remembered event <;>
          simpa only [privateStep, owned, ↓reduceDIte, remembered,
            State.FreshCandidates, State.HandleUnused] using ⟨bound, available⟩
      · simpa only [privateStep, owned, ↓reduceDIte] using ⟨bound, available⟩

theorem submitStep_freshCandidates (state : State graph) (who : Player)
    (packet : Payload graph) (fresh : state.FreshCandidates) :
    (submitStep state who packet).FreshCandidates := by
  obtain ⟨bound, available⟩ := fresh
  cases packet with
  | commitment event candidate =>
      by_cases owned : candidate.1 = who
      · refine ⟨max bound (candidateBound candidate), fun owner serial beyond => ?_⟩
        obtain ⟨prior, unused⟩ := available owner serial (le_trans (le_max_left _ _) beyond)
        have different := prepared_ne_of_bound candidate owner serial
          (le_trans (le_max_right _ _) beyond)
        refine ⟨?_, by simpa only [State.HandleUnused, submitStep_accepted] using unused⟩
        simp only [submitStep, owned, ↓reduceIte]
        exact (state.candidates.lookup_freeze_other candidate
          (owner, .prepared serial) different).trans prior
      · simpa only [submitStep, owned, ↓reduceIte, State.FreshCandidates,
          State.HandleUnused] using ⟨bound, available⟩
  | opening event candidate raw | withhold event | malformed raw =>
      exact ⟨bound, available⟩

theorem handle_freshCandidates (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (Payload graph))
    (fresh : before.FreshCandidates) (accepted : handle runtime before message = some after) :
    after.FreshCandidates := by
  obtain ⟨bound, available⟩ := fresh
  rcases message with ⟨id, packet⟩
  cases packet with
  | commitment event candidate =>
      obtain ⟨candidates, handles, _⟩ :=
        handle_commitment_tables runtime before after id event candidate accepted
      refine ⟨max bound (candidateBound candidate), fun owner serial beyond => ?_⟩
      obtain ⟨prior, unused⟩ := available owner serial (le_trans (le_max_left _ _) beyond)
      have different := prepared_ne_of_bound candidate owner serial
        (le_trans (le_max_right _ _) beyond)
      refine ⟨?_, ?_⟩
      · rw [candidates]
        exact (before.candidates.lookup_freeze_other candidate
          (owner, .prepared serial) different).trans prior
      · intro field retained
        by_cases current : field = .inr event
        · subst field
          rw [handles, Function.update_self] at retained
          exact different (Option.some.inj retained).symm
        · apply unused field
          simpa only [handles, Function.update_of_ne current] using retained
  | opening event candidate raw | withhold event =>
      have tables := handle_resolution_tables runtime before after _ (by intros; simp) accepted
      simpa only [State.FreshCandidates, State.HandleUnused, tables.1, tables.2]
        using ⟨bound, available⟩
  | malformed raw => simp [handle] at accepted

/-- Arbitrary finite native activity cannot exhaust fresh handles. In
particular, an occupied canonical slot does not exhaust material for a new submission. -/
theorem run_freshCandidates (runtime : EventGraphRuntime graph)
    (before after : runtime.application.State) (actions : List runtime.application.Action)
    (fresh : before.application.FreshCandidates)
    (reached : after ∈ (runtime.application.run actions before).support) :
    after.application.FreshCandidates := by
  apply runtime.application.run_application_invariant State.FreshCandidates
    privateStep_freshCandidates submitStep_freshCandidates
    (fun before message after fresh accepted =>
      handle_freshCandidates runtime before after message fresh accepted)
    _ before after actions fresh reached
  intro before command after fresh supported
  have tables := environmentStep_tables runtime before after command supported
  simpa only [State.FreshCandidates, State.HandleUnused, tables.1, tables.2] using fresh

omit [DecidableEq Player] in
/-- A requested lower bound can be avoided as well as every occupied or
accepted handle. Freshness and non-reuse are visible in the owner's catalogue
and the public accepted-handle table. -/
theorem State.FreshCandidates.exists_prepared {state : State graph}
    (fresh : state.FreshCandidates) (who : Player) (lower : Nat) :
    ∃ serial, lower ≤ serial ∧
      state.candidates.lookup (who, .prepared serial) = .fresh ∧
      state.HandleUnused (who, .prepared serial) := by
  obtain ⟨bound, available⟩ := fresh
  exact ⟨max lower bound, le_max_left _ _, available who _ (le_max_right _ _)⟩

end Vegas.EventGraphRuntime
