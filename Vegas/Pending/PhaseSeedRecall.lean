/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedScheduler
import Interaction.ReactiveTrafficState

/-! # Full local emission words reconstructed from actual player recall

The scheduler recovers emission clocks from successive public input prefixes.
The owner recovers the same word from its full retained callback recall, even
when previous attempt outputs have been voided by a reset.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def adjacent (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :=
  past.zip (past.tail.map (·.beforeView) ++ [view])

private theorem adjacent_snoc (past : List (app).EnvironmentEntry)
    (entry : (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    adjacent runtime leaks (past ++ [entry]) view =
      adjacent runtime leaks past entry.beforeView ++ [(entry, view)] := by
  induction past with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second later =>
          change (first, second.beforeView) ::
            adjacent runtime leaks ((second :: later) ++ [entry]) view =
              (first, second.beforeView) ::
                (adjacent runtime leaks (second :: later) entry.beforeView ++ [(entry, view)])
          exact congrArg ((first, second.beforeView) :: ·) ih

def callback (coordinate : CommitAttemptEvent graph) (owner : Player)
    (entry : (app).EnvironmentEntry) : Prop :=
  entry.command = .activate owner ∧
    PhaseRuntimeState.requests entry.beforeView.application owner coordinate

open Classical in
def word (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    List (Nat × List (Message Player (CommitAttemptPacket graph))) :=
  ((adjacent runtime leaks past view).filter fun pair =>
    callback runtime leaks coordinate owner pair.1).map fun pair =>
      (elapsed runtime leaks coordinate pair.1.beforeView,
        (pair.2.network.inputs.drop pair.1.beforeView.network.inputs.length).filter
          (ownPacket coordinate owner))

open Classical in
private theorem word_snoc (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (view : (app).EnvironmentView) :
    word runtime leaks coordinate owner (past ++ [entry]) view =
      word runtime leaks coordinate owner past entry.beforeView ++
        if callback runtime leaks coordinate owner entry then
          [(elapsed runtime leaks coordinate entry.beforeView,
            (view.network.inputs.drop entry.beforeView.network.inputs.length).filter
              (ownPacket coordinate owner))] else [] := by
  simp only [word, adjacent_snoc, List.filter_append, List.map_append, List.filter_cons,
    List.filter_nil]
  by_cases active : callback runtime leaks coordinate owner entry <;> simp [active]

open Classical in
/-- The owner uses only its own callback input and emitted envelope. -/
def ownerWord (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).PlayerEntry) :
    List (Nat × List (Message Player (CommitAttemptPacket graph))) :=
  (past.filter fun entry =>
    PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate).map fun entry =>
      (entry.beforeView.application.2.native.clock -
          (entry.beforeView.application.2.native.activatedAt coordinate.event).getD
            entry.beforeView.application.2.native.clock,
        entry.emitted.toList.filter (ownPacket coordinate owner))

def WordRecall (execution : (app).Execution) : Prop :=
  ∀ owner coordinate, word runtime leaks coordinate owner execution.environmentRecall
    (execution.observeEnvironment app) = ownerWord runtime leaks coordinate owner
      (execution.recall owner)

@[simp]
theorem initial_wordRecall (state : PhaseRuntimeState graph) :
    WordRecall runtime leaks (ReactiveApplication.Execution.initial app state) := by
  intro owner coordinate
  rfl

/-- The complete local query is the clocked word, together with current elapsed time. -/
theorem localInput_word (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    localInput runtime leaks coordinate owner past view =
      { elapsed := elapsed runtime leaks coordinate view
        activationClocks := (word runtime leaks coordinate owner past view).map Prod.fst
        emissions := (word runtime leaks coordinate owner past view).flatMap fun entry =>
          entry.2.map (Prod.mk entry.1) } := by
  simp only [localInput, word, adjacent, callback, List.map_map, List.flatMap_map,
    Function.comp_def]
  have canonical (proposition : Prop) (decision : Decidable proposition) :
      @decide proposition decision =
        @decide proposition (Classical.propDecidable proposition) :=
    decide_eq_decide.mpr Iff.rfl
  simp_rw [canonical]

open Classical in
/-- Every actual scheduler round preserves the owner's reconstruction of the
full local word; foreign commands and reset normalization add no own callback. -/
theorem dispatch_wordRecall (players : Player → (app).Policy) (command : (app).Command)
    (execution next : (app).Execution) (valid : WordRecall runtime leaks execution)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    WordRecall runtime leaks next := by
  obtain ⟨middle, observed, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recallEq := (app).environmentStep_recall execution middle command observed
  have envRecallEq := (app).dispatch_environmentRecall players command execution next reached
  intro owner coordinate
  rw [envRecallEq, word_snoc]
  cases command with
  | activate acting =>
      change next ∈ ((app).invoke players acting middle).support at resumed
      obtain ⟨action, supported, rfl⟩ := PMF.support_map .. ▸ resumed
      obtain ⟨after, moved, middleEq⟩ := PMF.support_map .. ▸ observed
      obtain ⟨selected, selectedSupport, afterEq⟩ := PMF.support_map .. ▸ moved
      subst after
      subst middle
      by_cases same : owner = acting
      · subst acting
        rw [valid owner coordinate]
        rcases action with ⟨transmission⟩
        cases transmission with
        | none =>
            by_cases ready : PhaseRuntimeState.requests execution.application.publicView
                owner coordinate <;>
              simp [ReactiveApplication.Execution.respond, ownerWord, callback, ready,
                ReactiveApplication.Execution.observe,
                ReactiveApplication.Execution.observeEnvironment, phaseApplication,
                PhaseRuntimeState.playerView, MessageNetwork.learn, MessageNetwork.publicView,
                elapsed]
        | some submission =>
            by_cases ready : PhaseRuntimeState.requests execution.application.publicView
                owner coordinate <;>
              simp [ReactiveApplication.Execution.respond, ownerWord, callback, ready,
                ReactiveApplication.Execution.observe,
                ReactiveApplication.Execution.observeEnvironment, phaseApplication,
                PhaseRuntimeState.playerView, MessageNetwork.learn, MessageNetwork.publicView,
                MessageNetwork.submit, elapsed]
      · have notActivated :
            (ReactiveApplication.Command.activate acting : (app).Command) ≠ .activate owner := by
          intro commands
          cases commands
          exact same rfl
        simp only [ite_eq_right (show ¬ callback runtime leaks coordinate owner
          ⟨execution.observeEnvironment app, .activate acting⟩ from
            fun activated => notActivated activated.1), List.append_nil]
        simpa only [ReactiveApplication.Execution.respond, ite_eq_right same] using
          valid owner coordinate
  | wait =>
      change next ∈ (PMF.pure middle).support at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      simp only [ite_eq_right (show ¬ callback runtime leaks coordinate owner
        ⟨execution.observeEnvironment app, .wait⟩ from fun activated => by
          cases activated.1), List.append_nil]
      rw [recallEq]
      exact valid owner coordinate
  | «include» identifier =>
      change next ∈ (PMF.pure middle).support at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      simp only [ite_eq_right (show ¬ callback runtime leaks coordinate owner
        ⟨execution.observeEnvironment app, .include identifier⟩ from fun activated => by
          cases activated.1), List.append_nil]
      rw [recallEq]
      exact valid owner coordinate
  | application native =>
      change next ∈ (PMF.pure middle).support at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      simp only [ite_eq_right (show ¬ callback runtime leaks coordinate owner
        ⟨execution.observeEnvironment app, .application native⟩ from fun activated => by
          cases activated.1), List.append_nil]
      rw [recallEq]
      exact valid owner coordinate

/-- The equality is over genuine full executions and all original attempt IDs,
including the voided own choices retained after a retry. -/
theorem runRounds_wordRecall (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (execution next : (app).Execution) (valid : WordRecall runtime leaks execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    WordRecall runtime leaks next := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | succ count ih =>
      obtain ⟨middle, roundReached, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, chosen, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ roundReached)
      exact ih middle
        (dispatch_wordRecall runtime leaks players command execution middle valid moved) future

end Vegas.EventGraphRuntime.PhaseSeedScheduler
