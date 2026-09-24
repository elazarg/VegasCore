/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveNormalRecall
import Interaction.ReactiveImplementationContinuation

/-! # Simulating private response names inside a strategy

A deviating strategy may condition later behavior on its earlier raw response
names. Those names can instead be retained as private implementation state.
Observed views and emitted packets are reconstructed from normal recall.
The memory introduced here belongs to the proof strategy, not the protocol.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization)

def restoreActions (past : List app.PlayerEntry) (actions : List app.Action) :
    List app.PlayerEntry :=
  List.zipWith (fun entry action => { entry with action := action }) past actions

private theorem normalized_length (who : Principal) (past : List app.PlayerEntry) :
    (normal.recall who past).length = past.length := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      simp only [normal.recall_append_action, List.length_append, List.length_singleton, ih]

theorem restoreActions_recall (who : Principal) (past : List app.PlayerEntry) :
    restoreActions (normal.recall who past) (past.map PlayerEntry.action) = past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [normal.recall_append_action, List.map_append]
      unfold restoreActions at *
      rw [List.zipWith_append
        (by simpa only [List.length_map] using normal.normalized_length who past)]
      simp only [List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left, ih]

open Classical in
/-- The fallback makes this an information-local total strategy even at inputs
incompatible with its private memory. It has no effect on the simulated run. -/
def aliasImplementation (who : Principal) (reference : List app.PlayerEntry)
    (policy : app.Policy) : app.Implementation (List app.Action) where
  initial := FinDist.pure (reference.map PlayerEntry.action)
  respond names input :=
    let restored := restoreActions input.1 names
    let past := if names.length = input.1.length ∧ normal.recall who restored = input.1
      then restored else input.1
    (policy past input.2).map fun response =>
      (normal.action who past input.2 response,
        if input.1.length < names.length then names else names ++ [response])

theorem aliasImplementation_respond (who : Principal) (reference past : List app.PlayerEntry)
    (policy : app.Policy) (view : app.PlayerView) :
    (normal.aliasImplementation who reference policy).respond
        (past.map PlayerEntry.action) (normal.recall who past, view) =
      (policy past view).map fun response =>
        (normal.action who past view response, past.map PlayerEntry.action ++ [response]) := by
  simp only [aliasImplementation, restoreActions_recall, List.length_map,
    normal.normalized_length, and_self, ↓reduceIte, Nat.lt_irrefl]

/-- The reference recall is a fixed initial condition for this continuation
deviation. Conditioning earlier observations does not resample its names. -/
theorem aliasImplementation_posterior_prefix (who : Principal)
    (reference past : List app.PlayerEntry) (policy : app.Policy)
    (short : past.length ≤ reference.length) :
    (normal.aliasImplementation who reference policy).posterior past =
      FinDist.pure (reference.map PlayerEntry.action) := by
  classical
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier : past.length ≤ reference.length := by
        simp only [List.length_append, List.length_singleton] at short
        omega
      have shorter : past.length < (reference.map PlayerEntry.action).length := by
        simp only [List.length_append, List.length_singleton, List.length_map] at *
        omega
      rw [Implementation.posterior_snoc, ih earlier, FinDist.pure_bind]
      apply FinDist.eq_pure_of_support_subset_singleton
      intro names member
      obtain ⟨response, supported, rfl⟩ := FinDist.support_map .. ▸ member
      have original : response ∈ ((normal.aliasImplementation who reference policy).respond
          (reference.map PlayerEntry.action) (past, entry.beforeView)).support := by
        unfold FinDist.condOnFibre at supported
        split at supported
        · exact (FinDist.support_condOn _ _ _ supported).2
        · exact supported
      simp only [aliasImplementation, shorter, ↓reduceIte, FinDist.support_map] at original
      obtain ⟨chosen, _, rfl⟩ := original
      rfl

theorem aliasImplementation_posterior_reference (who : Principal)
    (reference : List app.PlayerEntry) (policy : app.Policy) :
    (normal.aliasImplementation who reference policy).posterior (normal.recall who reference) =
      FinDist.pure (reference.map PlayerEntry.action) :=
  normal.aliasImplementation_posterior_prefix who reference _ policy
    (normal.normalized_length who reference).le

variable [DecidableEq Principal]

private theorem respond_action_names (execution : app.Execution) (who : Principal)
    (response : app.Action) :
    ((execution.respond app who response).recall who).map PlayerEntry.action =
      (execution.recall who).map PlayerEntry.action ++ [response] := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ↓reduceIte, List.map_append]; rfl
  | some transmission =>
      cases transmission <;> simp only [Execution.respond, ↓reduceIte, List.map_append] <;> rfl

/-- Opponents use their normalized recall; the focal player can use any raw
policy, including one that remembers its private response names. -/
theorem aliasImplementation_resume (who : Principal) (reference : List app.PlayerEntry)
    (policy : app.Policy) (players : Principal → app.Policy)
    (fixed : ∀ other past view response, response ∈ (players other past view).support →
      normal.action other past view response = response)
    (actor : Option Principal) (execution : app.Execution) (valid : execution.InputRecall app) :
    (normal.aliasImplementation who reference policy).resume who players actor
        (normal.execution execution) ((execution.recall who).map PlayerEntry.action) =
      (app.resume (Function.update
        (fun other past view => players other (normal.recall other past) view) who policy)
          actor execution).map (fun next =>
            (normal.execution next, (next.recall who).map PlayerEntry.action)) := by
  cases actor with
  | none => simp only [Implementation.resume, ReactiveApplication.resume, FinDist.map_pure]
  | some owner =>
      by_cases same : owner = who
      · subst owner
        simp only [Implementation.resume, ↓reduceIte, execution_observe,
          ReactiveApplication.resume, invoke, Function.update_self]
        change ((normal.aliasImplementation who reference policy).respond _
          (normal.recall who (execution.recall who), execution.observe app who)).map _ = _
        rw [normal.aliasImplementation_respond, FinDist.map_comp, FinDist.map_comp]
        apply FinDist.map_congr_of_eq_on_support
        intro response _
        simp only [Function.comp_apply]
        rw [← normal.execution_respond execution who response valid,
          respond_action_names]
      · simp only [Implementation.resume, same, ↓reduceIte, execution_observe,
          ReactiveApplication.resume, invoke, Function.update_of_ne same, FinDist.map_comp]
        change (players owner (normal.recall owner (execution.recall owner))
          (execution.observe app owner)).map _ = _
        apply FinDist.map_congr_of_eq_on_support
        intro response supported
        have unchanged : normal.action owner (execution.recall owner)
            (execution.observe app owner) response = response := by
          rw [← normal.action_recall]
          exact fixed owner _ _ response supported
        simp only [Function.comp_apply]
        have projected := normal.execution_respond execution owner response valid
        rw [unchanged] at projected
        rw [← projected]
        rw [app.respond_recall_other execution owner who (Ne.symm same) response]

theorem aliasImplementation_round (who : Principal) (reference : List app.PlayerEntry)
    (policy : app.Policy) (players : Principal → app.Policy)
    (fixed : ∀ other past view response, response ∈ (players other past view).support →
      normal.action other past view response = response)
    (scheduler : app.Scheduler) (execution : app.Execution) (valid : execution.InputRecall app) :
    (normal.aliasImplementation who reference policy).round who players scheduler
        (normal.execution execution) ((execution.recall who).map PlayerEntry.action) =
      (app.round scheduler (Function.update
        (fun other past view => players other (normal.recall other past) view) who policy)
          execution).map (fun next =>
            (normal.execution next, (next.recall who).map PlayerEntry.action)) := by
  simp only [Implementation.round, ReactiveApplication.round, dispatch, FinDist.map_bind]
  change (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind _ = _
  apply FinDist.bind_congr
  intro command _
  rw [← normal.execution_environmentStep, FinDist.bind_map]
  apply FinDist.bind_congr
  intro next reached
  rw [← app.environmentStep_recall execution next command reached]
  exact normal.aliasImplementation_resume who reference policy players fixed _ next
    (app.environment_inputRecall execution next command valid reached)

private theorem round_inputRecall (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (execution next : app.Execution) (valid : execution.InputRecall app)
    (reached : next ∈ (app.round scheduler players execution).support) :
    next.InputRecall app := by
  obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨middle, stepped, resumed⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
  have middleValid := app.environment_inputRecall execution middle command valid stepped
  cases actor : command.actor? app with
  | none =>
      simp only [ReactiveApplication.resume, actor] at resumed
      cases FinDist.mem_support_pure.mp resumed
      exact middleValid
  | some owner =>
      simp only [ReactiveApplication.resume, actor, invoke] at resumed
      obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ resumed
      exact app.respond_inputRecall middle owner response middleValid

/-- Exact simulation of an arbitrary raw deviation by private implementation
memory, from any valid execution and against normalized opponents. -/
theorem aliasImplementation_run (who : Principal) (reference : List app.PlayerEntry)
    (policy : app.Policy) (players : Principal → app.Policy)
    (fixed : ∀ other past view response, response ∈ (players other past view).support →
      normal.action other past view response = response)
    (scheduler : app.Scheduler) (count : Nat)
    (execution : app.Execution) (valid : execution.InputRecall app) :
    (normal.aliasImplementation who reference policy).run who players scheduler count
        (normal.execution execution) ((execution.recall who).map PlayerEntry.action) =
      (app.runRounds scheduler (Function.update
        (fun other past view => players other (normal.recall other past) view) who policy)
          count execution).map normal.execution := by
  induction count generalizing execution with
  | zero => simp only [Implementation.run, runRounds, FinDist.map_pure]
  | succ count ih =>
      rw [Implementation.run, normal.aliasImplementation_round who reference policy players
        fixed scheduler execution valid, FinDist.bind_map, runRounds, FinDist.map_bind]
      apply FinDist.bind_congr
      intro next reached
      exact ih next (round_inputRecall _ scheduler execution next valid reached)

/-- The external execution law of a deviation is available to a behavioral
strategy in the normalized game. The initial raw own recall is fixed at the
continuation being compared; no hidden environment state enters the policy. -/
theorem aliasImplementation_behavioral_run (who : Principal) (policy : app.Policy)
    (players : Principal → app.Policy)
    (fixed : ∀ other past view response, response ∈ (players other past view).support →
      normal.action other past view response = response)
    (scheduler : app.Scheduler) (count : Nat)
    (execution : app.Execution) (valid : execution.InputRecall app) :
    app.runRounds scheduler (Function.update players who
        (normal.aliasImplementation who (execution.recall who) policy).policy)
        count (normal.execution execution) =
      (app.runRounds scheduler (Function.update
        (fun other past view => players other (normal.recall other past) view) who policy)
          count execution).map normal.execution := by
  rw [← Implementation.realize]
  change ((normal.aliasImplementation who (execution.recall who) policy).posterior
    (normal.recall who (execution.recall who))).bind _ = _
  rw [normal.aliasImplementation_posterior_reference, FinDist.pure_bind]
  exact normal.aliasImplementation_run who _ policy players fixed scheduler count execution valid

/-- The same deviation simulation starts at a decision information set, after
activation and before its response, and preserves the final external state. -/
theorem aliasImplementation_behavioral_continuation (who : Principal) (policy : app.Policy)
    (players : Principal → app.Policy)
    (fixed : ∀ other past view response, response ∈ (players other past view).support →
      normal.action other past view response = response)
    (scheduler : app.Scheduler) (count : Nat) (actor : Option Principal)
    (execution : app.Execution) (valid : execution.InputRecall app) :
    (app.resume (Function.update players who
        (normal.aliasImplementation who (execution.recall who) policy).policy)
        actor (normal.execution execution)).bind
      (app.runRounds scheduler (Function.update players who
        (normal.aliasImplementation who (execution.recall who) policy).policy) count) =
      ((app.resume (Function.update
        (fun other past view => players other (normal.recall other past) view) who policy)
          actor execution).bind (app.runRounds scheduler (Function.update
            (fun other past view => players other (normal.recall other past) view) who policy)
              count)).map normal.execution := by
  rw [← Implementation.realize_continuation]
  change ((normal.aliasImplementation who (execution.recall who) policy).posterior
    (normal.recall who (execution.recall who))).bind _ = _
  rw [normal.aliasImplementation_posterior_reference, FinDist.pure_bind,
    normal.aliasImplementation_resume who _ policy players fixed actor execution valid,
    FinDist.bind_map, FinDist.map_bind]
  apply FinDist.bind_congr
  intro next reached
  apply normal.aliasImplementation_run who _ policy players fixed scheduler count next
  cases actor with
  | none =>
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | some owner =>
      obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact app.respond_inputRecall execution owner response valid

end Interaction.ReactiveApplication.SubmissionNormalization
