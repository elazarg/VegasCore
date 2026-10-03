/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrame
import Vegas.Pending.ReactiveRiskMenu
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveObservation

/-! # Actual public activation records in response recall

The public before-view of every response is the public view at its actual
activation. One pending activation has no response yet. This derives the
risk records needed by private binding repair from actual raw histories.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private def publicActivations (who : Player)
    (past : List (runtime.reactiveApplication leaks).EnvironmentEntry) :
    List (Player × PublicView graph) :=
  past.filterMap fun entry => match entry.command with
    | .activate actor => if actor = who then some (who, entry.beforeView.application) else none
    | _ => none

private def responsePublicViews
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) :
    List (Player × PublicView graph) :=
  past.map fun entry => (entry.beforeView.application.who, entry.beforeView.application.publicView)

private def activationRecall (state : (runtime.reactiveApplication leaks).ProtocolState) : Prop :=
  match state with
  | none => True
  | some control => ∀ who,
      publicActivations runtime leaks who control.execution.environmentRecall =
        responsePublicViews runtime leaks (control.execution.recall who) ++
          if control.actor = some who then [(who, control.execution.application.publicView)] else []

private theorem activationRecall_transition
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before after : (runtime.reactiveApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (valid : activationRecall runtime leaks before)
    (reached : after ∈ ((runtime.reactiveApplication leaks).transition initial horizon scheduler
      before joint).support) : activationRecall runtime leaks after := by
  let app := runtime.reactiveApplication leaks
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      intro who
      rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some actor =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          intro who
          have old := valid who
          by_cases same : who = actor
          · subst who
            simpa only [activationRecall, ReactiveApplication.Execution.respond,
              responsePublicViews, List.map_append, List.map_cons, List.map_nil,
              ↓reduceIte, Option.some.injEq, reduceCtorEq, List.append_nil,
              ReactiveApplication.Execution.observe,
              EventGraphRuntime.reactiveApplication] using old
          · simpa only [activationRecall, ReactiveApplication.Execution.respond,
              same, Ne.symm same, ↓reduceIte, Option.some.injEq, reduceCtorEq,
              List.append_nil] using old
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
              have recallsEq := app.environmentStep_recall execution next command moved
              have envRecall : next.environmentRecall = execution.environmentRecall ++
                  [⟨execution.observeEnvironment app, command⟩] := by
                obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ moved
                rfl
              intro who
              have old := valid who
              simp only [reduceCtorEq, ↓reduceIte, List.append_nil] at old
              change publicActivations runtime leaks who next.environmentRecall = _
              rw [envRecall, recallsEq]
              cases command with
              | activate actor =>
                  obtain ⟨updated, sampled, rfl⟩ := PMF.support_map .. ▸ moved
                  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ sampled
                  simp only [publicActivations] at old
                  simp only [publicActivations, List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, old, ReactiveApplication.Command.actor?]
                  by_cases same : actor = who
                  · subst actor
                    simp only [↓reduceIte]
                    rfl
                  · simp only [same, ↓reduceIte, Option.some.injEq]
              | wait =>
                  simpa only [publicActivations, List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, old, ReactiveApplication.Command.actor?,
                    reduceCtorEq, ↓reduceIte, List.append_nil]
              | «include» id =>
                  simpa only [publicActivations, List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, old, ReactiveApplication.Command.actor?,
                    reduceCtorEq, ↓reduceIte, List.append_nil]
              | application command =>
                  simpa only [publicActivations, List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, old, ReactiveApplication.Command.actor?,
                    reduceCtorEq, ↓reduceIte, List.append_nil]

private theorem activationRecall_history
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    ∀ {state}
      (_trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
        state), activationRecall runtime leaks state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      activationRecall_transition runtime leaks initial horizon scheduler _ _ joint
        (activationRecall_history initial horizon scheduler prior) reached

/-- At a completed scheduler boundary every actual activation has a response
in the named player's recall at that same public application view. This holds
for every legal RAW history, without any response-menu or policy restriction. -/
theorem activations_answered_history
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (execution : (runtime.reactiveApplication leaks).Execution) (remaining : Nat)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩)) :
    ∀ entry ∈ execution.environmentRecall, ∀ who, entry.command = .activate who →
      ∃ answer ∈ execution.recall who,
        answer.beforeView.application.publicView = entry.beforeView.application := by
  intro entry member who activated
  have actual := activationRecall_history runtime leaks initial horizon scheduler trace who
  change publicActivations runtime leaks who execution.environmentRecall =
    responsePublicViews runtime leaks (execution.recall who) ++
      (if (none : Option Player) = some who then _ else []) at actual
  simp only [reduceCtorEq, ↓reduceIte, List.append_nil] at actual
  have present : (who, entry.beforeView.application) ∈
      publicActivations runtime leaks who execution.environmentRecall := by
    apply List.mem_filterMap.mpr
    refine ⟨entry, member, ?_⟩
    simp only [activated, ↓reduceIte]
  rw [actual] at present
  obtain ⟨answer, recalled, same⟩ := List.mem_map.mp present
  exact ⟨answer, recalled, congrArg Prod.snd same⟩

private theorem responsePublicViews_history
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player) :
    responsePublicViews runtime leaks (control.execution.recall who) =
      (publicActivations runtime leaks who control.execution.environmentRecall).take
        (control.execution.recall who).length := by
  have actual := activationRecall_history runtime leaks initial horizon scheduler trace who
  have observed := congrArg (List.take (control.execution.recall who).length) actual
  simpa only [List.take_append, responsePublicViews, List.length_map,
    ← List.map_take, List.take_length,
    Nat.sub_self, List.take_zero, List.append_nil] using observed.symm

private theorem submissionRiskRecords_eq_zip
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) :
    past.map (runtime.submissionRiskRecord leaks) =
      List.zipWith (fun observed named => (observed.1, observed.2, named))
        (responsePublicViews runtime leaks past) (runtime.submissionRecall leaks past) := by
  induction past with
  | nil => rfl
  | cons entry past ih =>
      simpa only [responsePublicViews, submissionRiskRecord, submissionRecall, List.map_cons,
        List.zipWith_cons_cons] using congrArg (runtime.submissionRiskRecord leaks entry :: ·) ih

/-- The actual public scheduler recall and event-name recall determine the
same risk records on both sides of a binding repair. Every before-view comes
from its real activation, including at an input whose response is pending. -/
theorem BindingMemory.Frame.submissionRiskRecords
    {initial : PMF (runtime.reactiveApplication leaks).State} {horizon : Nat}
    {scheduler : (runtime.reactiveApplication leaks).Scheduler}
    {memory : BindingMemory runtime leaks} {owner : Player}
    {original repaired : (runtime.reactiveApplication leaks).Control}
    (frame : BindingMemory.Frame runtime leaks memory owner original.execution repaired.execution)
    (leftTrace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some original))
    (rightTrace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some repaired)) :
    (original.execution.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.execution.recall owner).map (runtime.submissionRiskRecord leaks) := by
  have lengths := congrArg List.length frame.submissions
  simp only [submissionRecall, List.length_map] at lengths
  have views : responsePublicViews runtime leaks (original.execution.recall owner) =
      responsePublicViews runtime leaks (repaired.execution.recall owner) := by
    rw [responsePublicViews_history runtime leaks initial horizon scheduler original leftTrace,
      responsePublicViews_history runtime leaks initial horizon scheduler repaired rightTrace,
      frame.service, lengths]
  rw [submissionRiskRecords_eq_zip, submissionRiskRecords_eq_zip, views, frame.submissions]

private theorem riskRecord_response_step
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) :
    ((execution.respond (runtime.reactiveApplication leaks) who response).recall who).map
        (runtime.submissionRiskRecord leaks) =
      (execution.recall who).map (runtime.submissionRiskRecord leaks) ++
        [(who, execution.application.publicView, runtime.submittedEvent? leaks response)] := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
        List.map_cons, List.map_nil, submissionRiskRecord, ReactiveApplication.Execution.observe,
        reactiveApplication]
  | some material =>
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
        List.map_cons, List.map_nil, submissionRiskRecord, ReactiveApplication.Execution.observe,
        reactiveApplication]

/-- Actual paired owner responses preserve the complete risk record whenever
repair preserves the submitted event. Hidden binding material is irrelevant. -/
theorem BindingMemory.Frame.submissionRiskRecords_respond
    {memory : BindingMemory runtime leaks} {owner : Player}
    {original repaired : (runtime.reactiveApplication leaks).Execution}
    (frame : BindingMemory.Frame runtime leaks memory owner original repaired)
    (same : (original.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.recall owner).map (runtime.submissionRiskRecord leaks))
    (leftResponse rightResponse : (runtime.reactiveApplication leaks).Action)
    (named : runtime.submittedEvent? leaks leftResponse =
      runtime.submittedEvent? leaks rightResponse) :
    ((original.respond (runtime.reactiveApplication leaks) owner leftResponse).recall owner).map
        (runtime.submissionRiskRecord leaks) =
      ((repaired.respond (runtime.reactiveApplication leaks) owner rightResponse).recall owner).map
        (runtime.submissionRiskRecord leaks) := by
  rw [riskRecord_response_step, riskRecord_response_step, same, frame.publicView, named]

end Vegas.EventGraphRuntime
