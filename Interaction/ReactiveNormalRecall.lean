/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseNormalization

/-! # Projecting private response aliases out of recall

Normalization leaves every transmitted packet and application effect intact.
The acting player nevertheless remembers its raw response. This projection
normalizes the remembered responses at their original observations and keeps
all observations and emissions. It supplies the history map needed to compare
the finite raw and normalized games; it is not an equilibrium theorem.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Math.Probability

variable {Principal : Type} {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization)

theorem action_eq_of_outputs (who : Principal) (first second : List app.PlayerEntry)
    (view : app.PlayerView) (same : app.outputs first = app.outputs second)
    (response : app.Action) :
    normal.action who first view response = normal.action who second view response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      have known : ResponseMenu.knownPackets (app := app) first view =
          ResponseMenu.knownPackets (app := app) second view := by
        simp only [ResponseMenu.knownPackets, same]
      cases transmission with
      | submit submission => simp only [action, known]
      | replay id =>
          have replay : ReplayKnown (app := app) first view id ↔
              ReplayKnown (app := app) second view id := by
            unfold ReplayKnown
            rw [known]
          by_cases available : ReplayKnown (app := app) first view id
          · simp only [action, available, replay.mp available, ↓reduceIte]
          · have absent := mt replay.mpr available
            simp only [action, available, absent, ↓reduceIte]

def recall (who : Principal) (past : List app.PlayerEntry) : List app.PlayerEntry :=
  past.foldl (fun normalized entry => normalized ++
    [{ entry with action := normal.action who normalized entry.beforeView entry.action }]) []

@[simp] theorem recall_nil (who : Principal) : normal.recall who [] = [] := rfl

theorem recall_append (who : Principal) (past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    normal.recall who (past ++ [entry]) = normal.recall who past ++
      [{ entry with
          action := normal.action who (normal.recall who past)
            entry.beforeView entry.action }] := by
  simp only [recall, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem recall_outputs (who : Principal) (past : List app.PlayerEntry) :
    app.outputs (normal.recall who past) = app.outputs past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [recall_append]
      cases emitted : entry.emitted <;>
      simpa only [ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, emitted, Option.toList] using
          congrArg (· ++ entry.emitted.toList) ih

@[simp] theorem action_recall (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action) :
    normal.action who (normal.recall who past) view response =
      normal.action who past view response :=
  normal.action_eq_of_outputs who _ _ view (normal.recall_outputs who past) response

theorem recall_append_action (who : Principal) (past : List app.PlayerEntry)
    (entry : app.PlayerEntry) :
    normal.recall who (past ++ [entry]) = normal.recall who past ++
      [{ entry with action := normal.action who past entry.beforeView entry.action }] := by
  rw [recall_append, action_recall]

@[simp] theorem recall_idempotent (who : Principal) (past : List app.PlayerEntry) :
    normal.recall who (normal.recall who past) = normal.recall who past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      simp only [recall_append_action, ih, action_recall, action_idempotent]

def execution (original : app.Execution) : app.Execution :=
  { original with recall := fun who => normal.recall who (original.recall who) }

@[simp] theorem execution_observe
    (original : app.Execution) (who : Principal) :
    (normal.execution original).observe app who = original.observe app who := rfl

@[simp] theorem execution_observeEnvironment (original : app.Execution) :
    (normal.execution original).observeEnvironment app = original.observeEnvironment app := rfl

@[simp] theorem execution_idempotent (original : app.Execution) :
    normal.execution (normal.execution original) = normal.execution original := by
  simp only [execution, recall_idempotent]

variable [DecidableEq Principal]

theorem execution_inputRecall (original : app.Execution) (valid : original.InputRecall app) :
    (normal.execution original).InputRecall app := by
  intro who
  change _ = app.outputs (normal.recall who (original.recall who))
  rw [recall_outputs]
  exact valid who

omit [DecidableEq Principal] in
theorem execution_initial (state : app.State) :
    normal.execution (.initial app state) = .initial app state := rfl

theorem execution_environmentStep (original : app.Execution) (command : app.Command) :
    (original.environmentStep app command).map normal.execution =
      (normal.execution original).environmentStep app command := by
  cases command with
  | wait => simp only [Execution.environmentStep, FinDist.map_pure]; rfl
  | activate who =>
      simp only [Execution.environmentStep, FinDist.map_comp]
      rfl
  | application command =>
      simp only [Execution.environmentStep, FinDist.map_comp]
      rfl
  | «include» id =>
      simp only [execution, Execution.environmentStep, FinDist.map_pure,
        Execution.includePending, MessageNetwork.includePending]
      cases original.network.lookup id <;> rfl

/-- A raw response and its normalized response generate exactly corresponding
recall entries; the emitted packet is retained even for a rejected call. -/
theorem execution_respond (original : app.Execution) (who : Principal) (response : app.Action)
    (valid : original.InputRecall app) :
    normal.execution (original.respond app who response) =
      (normal.execution original).respond app who
        (normal.action who (original.recall who) (original.observe app who) response) := by
  have known : ResponseMenu.knownPackets (app := app)
      (original.recall who) (original.observe app who) =
      original.network.known who := (app.known_from_recall original who valid).symm
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [action, Execution.respond, execution, Execution.observe]
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, recall_append_action, action]
      · simp only [same, ↓reduceIte]
  | some transmission =>
      cases transmission with
      | submit submission =>
          have submitted := normal.submit original.application who
            (original.network.known who) submission
          have packet := normal.packet (app.submit original.application who submission) who
            (app.observePlayer original.application who) (original.network.known who) submission
          simp only [action]
          rw [known]
          change normal.execution (original.respond app who ⟨some (.submit submission)⟩) =
            (normal.execution original).respond app who
              ⟨some (.submit (normal.normalize who (app.observePlayer original.application who)
                (original.network.known who) submission))⟩
          simp only [Execution.respond, execution, submitted, packet]
          congr 1
          funext observer
          by_cases same : observer = who
          · subst observer
            simp only [↓reduceIte, recall_append_action, action, known]
            rfl
          · simp only [same, ↓reduceIte]
      | replay id =>
          by_cases available : ReplayKnown (app := app)
              (original.recall who) (original.observe app who) id
          · simp only [action]
            rw [ite_eq_left available]
            simp only [Execution.respond, execution]
            congr 1
            funext observer
            by_cases same : observer = who
            · subst observer
              simp only [↓reduceIte, recall_append_action, action, available]
              rfl
            · simp only [same, ↓reduceIte]
          · have absent : (original.network.known who).find?
                  (fun envelope => envelope.id = id) = none := by
              apply List.find?_eq_none.mpr
              intro message member identified
              exact available ((replayKnown_iff original who valid id).mpr
                ⟨message, member, of_decide_eq_true identified⟩)
            simp only [action]
            rw [ite_eq_right available]
            simp only [Execution.respond, execution, MessageNetwork.replay, absent]
            congr 1
            funext observer
            by_cases same : observer = who
            · subst observer
              simp only [↓reduceIte, recall_append_action, action, available]
              rfl
            · simp only [same, ↓reduceIte]

end Interaction.ReactiveApplication.SubmissionNormalization
