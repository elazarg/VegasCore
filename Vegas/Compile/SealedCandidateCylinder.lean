/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReplay
import Vegas.Compile.SealedCandidateValues

/-! # Exact assignment cylinders for candidate-host replay

For fixed native responses, a replay prefix is determined exactly by the
non-focal reference proposals it prepared. Pending packets, competing focal candidates,
unopenable acceptances, and post-timeout execution are retained. The assignment
law may be correlated. These are probability laws for assigned-value replay;
original state-dependent legal kernels require a separate source likelihood law.
-/

noncomputable section

namespace Vegas.EventGraph.SealedShape

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedShape G ty) (nullValue : L.Val ty) (window : Nat) (focal : Player)

/-- Changing only unprepared non-focal reference coordinates preserves a supported trace,
with the same arbitrary randomized focal and environment policies. -/
theorem tracePolicies_candidateValues_transfer
    (deviator : (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment : MessageApplication.EnvironmentPolicy
      (supported.resolvingRuntime nullValue window).candidateApplication)
    (left right : Fin G.nodeCount → L.Val ty)
    (release :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution → Bool)
    (schedule : List (@Invocation Player))
    (initial : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (trace : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
        (supported.candidateValuePlayers nullValue window left focal deviator)
        environment schedule initial |>.map (PolicyTrace.prefixThrough release)).support)
    (hagrees : ∀ who (node : Fin G.nodeCount) (value : L.Val ty), who ≠ focal →
      (.privateCommand who ⟨(node.val, value)⟩ :
        (supported.resolvingRuntime nullValue window).candidateApplication.Action) ∈
          trace.last.nativeTrace → left node = right node) :
    trace ∈ ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
      (supported.candidateValuePlayers nullValue window right focal deviator)
        environment schedule initial |>.map (PolicyTrace.prefixThrough release)).support := by
  let runtime := supported.resolvingRuntime nullValue window
  apply MessageApplication.tracePolicies_prefix_support_transfer _ _ _ environment release schedule
    initial trace htrace
  intro who history view command hcommand hrecord
  by_cases hwho : who = focal
  · subst who
    simpa only [candidateValuePlayers, Profile.update_same] using hcommand
  · rw [candidateValuePlayers, Profile.update_of_ne _ _ hwho] at hcommand ⊢
    have hright := supported.selected_proposals_congr left right who view.application.timeouts
      (runtime.eventHistory (runtime.registeredPlayerHistory history))
      (runtime.eventView (runtime.registeredPlayerView view)) _ command hcommand
      (fun node heq => hagrees who node (left node) hwho (hrecord _ (by rw [heq]; rfl)))
    change runtime.candidatePlayerPolicy
      (supported.resolvingProposalPolicy nullValue window who (supported.assignedProposals right
        who))
        history view = FinDist.pure command at hright
    rw [hright, FinDist.mem_support_pure]

variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))
variable (release :
  (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution → Bool)

/-- A stopped replay's last snapshot is supported by an actual invocation prefix. -/
theorem candidateReplay_prefix_run_support (values : Fin G.nodeCount → L.Val ty) :
    ∃ front, (supported.candidateReplay nullValue window values focal deviator environment schedule
      |>.prefixThrough release).last ∈
        ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
          (supported.candidateValuePlayers nullValue window values focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) front
          (PolicyExecution.initial _ (State.initial _
            (supported.resolvingRuntime nullValue window).candidateInitial))).support := by
  have hfull : supported.candidateReplay nullValue window values focal
      deviator environment schedule ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
        (supported.candidateValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)))
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support := by
    rw [candidateReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, _, _, hprefix, _⟩ := MessageApplication.tracePolicies_firstRelease_split
    _ _ _ release schedule _ _ hfull
  exact ⟨front, by simpa only [PolicyTrace.prefixThrough_last] using hprefix⟩

/-- Replay records the assigned reference preparation and retains its opening.
This is valid even when the selected prefix contains timeout transitions. -/
theorem candidateReplay_registration_lookup (values : Fin G.nodeCount → L.Val ty)
    (who : Player) (hwho : who ≠ focal) (node : Fin G.nodeCount) (value : L.Val ty)
    (hrecord : (.privateCommand who ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).candidateApplication.Action) ∈
        (supported.candidateReplay nullValue window values focal deviator environment schedule
          |>.prefixThrough release).last.nativeTrace) :
    value = values node ∧
      (supported.candidateReplay nullValue window values focal deviator environment schedule
        |>.prefixThrough release).last.native.application.service.lookup (who, node.val) =
          .openable (values node) ∧ ∃ guard, (G.nodeRow node).sem = .commit who guard := by
  obtain ⟨front, hprefix⟩ := supported.candidateReplay_prefix_run_support nullValue window focal
    deviator environment schedule release values
  exact ⟨(supported.runPolicies_candidateValues_registration nullValue window values focal
    _ _ front _ hprefix who hwho node value hrecord).1,
    supported.runPolicies_candidateValues_registration_lookup nullValue window values focal
      _ _ front _ hprefix who hwho node value hrecord⟩

/-- The complete prefix agrees exactly when the assignments agree on the
non-focal preparations recorded by the left run. Focal commands add no draw factors. -/
theorem candidateReplay_prefix_eq_iff (left right : Fin G.nodeCount → L.Val ty) :
    (supported.candidateReplay nullValue window left focal
      deviator environment schedule).prefixThrough release =
      (supported.candidateReplay nullValue window right focal
        deviator environment schedule).prefixThrough release ↔
      ∀ who (node : Fin G.nodeCount) (value : L.Val ty), who ≠ focal →
        (.privateCommand who ⟨(node.val, value)⟩ :
          (supported.resolvingRuntime nullValue window).candidateApplication.Action) ∈
            (supported.candidateReplay nullValue window left focal
              deviator environment schedule |>.prefixThrough release).last.nativeTrace →
                left node = right node := by
  constructor
  · intro heq who node value hwho hrecord
    have hl := (supported.candidateReplay_registration_lookup nullValue window focal deviator
      environment schedule release left who hwho node value hrecord).1
    have hr := (supported.candidateReplay_registration_lookup nullValue window focal deviator
      environment schedule release right who hwho node value (heq ▸ hrecord)).1
    exact hl.symm.trans hr
  · intro hagrees
    have hleft : (supported.candidateReplay nullValue window left focal
        deviator environment schedule).prefixThrough release ∈
        ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
          (supported.candidateValuePlayers nullValue window left focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) schedule
          (PolicyExecution.initial _ (State.initial _
            (supported.resolvingRuntime nullValue window).candidateInitial)) |>.map
              (PolicyTrace.prefixThrough release)).support := by
      rw [candidateReplay_law, FinDist.map_pure, FinDist.mem_support_pure]
    have hright := supported.tracePolicies_candidateValues_transfer nullValue window focal
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) left right release schedule
      _ _ hleft hagrees
    rwa [candidateReplay_law, FinDist.map_pure, FinDist.mem_support_pure] at hright

/-- Equivalently, only the openable non-focal graph slots in the prefix's
catalog constrain the assignment. Extra focal candidates and unopenable
acceptances are retained by replay but add no source draw constraints. -/
theorem candidateReplay_prefix_eq_iff_lookup (left right : Fin G.nodeCount → L.Val ty) :
    (supported.candidateReplay nullValue window left focal
      deviator environment schedule).prefixThrough release =
      (supported.candidateReplay nullValue window right focal
        deviator environment schedule).prefixThrough release ↔
      ∀ who (node : Fin G.nodeCount) guard,
        (G.nodeRow node).sem = .commit who guard → who ≠ focal → ∀ value,
        (supported.candidateReplay nullValue window left focal deviator environment schedule
          |>.prefixThrough release).last.native.application.service.lookup (who, node.val) =
            .openable value → right node = value := by
  rw [supported.candidateReplay_prefix_eq_iff nullValue window focal deviator environment
    schedule release left right]
  constructor
  · intro h who node _guard _hsem hwho value hlookup
    obtain ⟨front, hprefix⟩ := supported.candidateReplay_prefix_run_support nullValue window focal
      deviator environment schedule release left
    have hrecord := SealedResolution.runPolicies_candidate_openable_origin
      (supported.resolvingRuntime nullValue window) _ _ front _ hprefix who node.val value hlookup
    have hvalue := (supported.candidateReplay_registration_lookup nullValue window focal deviator
      environment schedule release left who hwho node value hrecord).1
    exact (h who node value hwho hrecord).symm.trans hvalue.symm
  · intro h who node value hwho hrecord
    obtain ⟨_hvalue, hlookup, guard, hsem⟩ := supported.candidateReplay_registration_lookup
      nullValue window focal deviator environment schedule release left who hwho node value hrecord
    exact (h who node guard hsem hwho (left node) hlookup).symm

/-- For any correlated assignment law, the probability of a complete replay
prefix is exactly the mass of its non-focal preparation cylinder. This statement
does not assume independent source draws or normal completion. -/
theorem candidateReplay_cylinder_probability
    (assignments : FinDist (Fin G.nodeCount → L.Val ty)) (reference : Fin G.nodeCount → L.Val ty) :
    (assignments.map (fun values =>
      (supported.candidateReplay nullValue window values focal
        deviator environment schedule).prefixThrough release)).prob
          (supported.candidateReplay nullValue window reference focal
            deviator environment schedule |>.prefixThrough release) =
      assignments.probOf {values | ∀ who (node : Fin G.nodeCount) (value : L.Val ty),
        who ≠ focal →
          (.privateCommand who ⟨(node.val, value)⟩ :
            (supported.resolvingRuntime nullValue window).candidateApplication.Action) ∈
              (supported.candidateReplay nullValue window reference focal
                deviator environment schedule |>.prefixThrough release).last.nativeTrace →
                  reference node = values node} := by
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  congr 1
  ext values
  exact eq_comm.trans (supported.candidateReplay_prefix_eq_iff nullValue window focal
    deviator environment schedule release reference values)

end Vegas.EventGraph.SealedShape

/-- info: 'Vegas.EventGraph.SealedShape.candidateReplay_cylinder_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.candidateReplay_cylinder_probability
