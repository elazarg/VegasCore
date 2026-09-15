/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReplay
import Interaction.SealedResolutionProvenance

/-! # Exact assignment cylinders for resolving native execution

For fixed native responses, equality of stopped replays is equivalent to
agreement on the non-focal reference coordinates recorded by one replay.
Every finite invocation prefix is an instance. The trace records private
commands for analysis; its complete contents are not exposed to players.

These facts include post-timeout execution. They characterize value-substituted
replay, not yet the law obtained from the original state-dependent source
kernels. A source/native coupling must connect those legal kernels to the
assignment distribution used in the cylinder probability theorem.
-/

noncomputable section

namespace Vegas.EventGraph.SealedShape

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedShape G ty) (nullValue : L.Val ty) (window : Nat)

section Support

variable (focal : Player)
variable (deviator : (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
variable (environment :
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)

/-- Changing only unregistered non-focal reference coordinates preserves the supported
stopped trace, with the same arbitrary randomized deviator and environment. -/
theorem tracePolicies_resolvingValues_transfer (left right : Fin G.nodeCount → L.Val ty)
    (release : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
      Bool)
    (schedule : List (@Invocation Player))
    (initial : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (supported.resolvingValuePlayers nullValue window left focal deviator)
        environment schedule initial |>.map (PolicyTrace.prefixThrough release)).support)
    (hagrees : ∀ owner (node : Fin G.nodeCount) (value : L.Val ty), owner ≠ focal →
      (.privateCommand owner ⟨(node.val, value)⟩ :
        (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
          trace.last.nativeTrace → left node = right node) :
    trace ∈ ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
      (supported.resolvingValuePlayers nullValue window right focal deviator)
        environment schedule initial |>.map (PolicyTrace.prefixThrough release)).support := by
  apply MessageApplication.tracePolicies_prefix_support_transfer _ _ _ environment release schedule
    initial trace htrace
  intro owner history view command hcommand hrecord
  by_cases howner : owner = focal
  · subst owner
    simpa only [resolvingValuePlayers, GameTheory.Profile.update_same] using hcommand
  · rw [resolvingValuePlayers, GameTheory.Profile.update_of_ne _ _ howner] at hcommand ⊢
    have hright := supported.selected_proposals_congr left right owner view.application.timeouts
      ((supported.resolvingRuntime nullValue window).eventHistory history)
      ((supported.resolvingRuntime nullValue window).eventView view)
      _ command hcommand (fun node heq =>
        hagrees owner node (left node) howner (hrecord _ (by rw [heq]; rfl)))
    change supported.resolvingProposalPolicy nullValue window owner (supported.assignedProposals
      right owner)
      history view = FinDist.pure command at hright
    rw [hright, FinDist.mem_support_pure]

/-- Every non-focal reference registration in a resolving run carries its
assigned node value, including registrations made after an earlier public default. -/
theorem runPolicies_resolvingValues_registration (values : Fin G.nodeCount → L.Val ty)
    (schedule : List (@Invocation Player))
    (final : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hfinal : final ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
        (supported.resolvingValuePlayers nullValue window values focal deviator)
        environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty) (howner : owner ≠ focal)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        final.nativeTrace) :
    value = values node ∧ ∃ guard, (G.nodeRow node).sem = .commit owner guard := by
  have hproperty :=
    (supported.resolvingRuntime nullValue window).messageApplication.runPolicies_action_property
      (fun action => ∀ who (index : Fin G.nodeCount) (registered : L.Val ty), who ≠ focal →
        action = .privateCommand who ⟨(index.val, registered)⟩ →
          registered = values index ∧ ∃ guard, (G.nodeRow index).sem = .commit who guard)
      (supported.resolvingValuePlayers nullValue window values focal deviator) environment
      (by
        intro actor history view command hcommand action ha who index registered hwho heq
        rw [heq] at ha
        cases command with
        | privateCommand request =>
            simp only [PlayerCommand.toAction, Option.some.injEq,
              MessageInterface.Action.privateCommand.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            rw [resolvingValuePlayers, GameTheory.Profile.update_of_ne _ _ hwho] at hcommand
            obtain ⟨actual, hindex, hvalue, guard, hsem⟩ :=
              supported.selected_proposals_registration values actor view.application.timeouts
                ((supported.resolvingRuntime nullValue window).eventHistory history)
                ((supported.resolvingRuntime nullValue window).eventView view)
                _ index.val registered hcommand
            have hactual : actual = index := Fin.ext hindex.symm
            exact ⟨by simpa only [hactual] using hvalue,
              guard, by simpa only [hactual] using hsem⟩
        | submit payload | replay id | wait =>
            simp only [PlayerCommand.toAction, Option.some.injEq] at ha
            cases ha)
      (by
        intro history view command _ action ha who index registered _ heq
        rw [heq] at ha
        cases command <;>
          simp only [EnvironmentPolicyCommand.toAction, Option.some.injEq] at ha <;> cases ha)
      schedule _ final (by simp only [PolicyExecution.initial, List.not_mem_nil,
        false_implies, implies_true]) hfinal
  exact hproperty _ htrace owner node value howner rfl

/-- The continuing private service retains exactly the assigned value at
each occupied non-focal reference slot. This conclusion concerns the service itself,
not merely the values appearing in emitted commands. -/
theorem runPolicies_resolvingValues_lookup (values : Fin G.nodeCount → L.Val ty)
    (schedule : List (@Invocation Player))
    (final : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hfinal : final ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
        (supported.resolvingValuePlayers nullValue window values focal deviator)
        environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty) (howner : owner ≠ focal)
    (hlookup : final.native.application.service.lookup (owner, node.val) = some value) :
    value = values node := by
  exact (supported.runPolicies_resolvingValues_registration nullValue window focal
    deviator environment values schedule final hfinal owner node value howner
    ((supported.resolvingRuntime nullValue window).runPolicies_lookup_origin
      _ _ schedule final hfinal owner node.val value hlookup)).1

end Support

variable (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.View →
  (supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))
variable (release :
  (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution → Bool)

/-- A checkpoint selected within the pre-resolution trace has actual policy
execution on both sides: from initialization to it, and from it to the common
timeout snapshot. The policies and assigned values are unchanged throughout. -/
theorem resolvingReplay_prefix_support (values : Fin G.nodeCount → L.Val ty) :
    let trace := (supported.resolvingReplay nullValue window values focal deviator environment
      schedule).prefixThrough (fun execution :
        (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∃ before after,
      trace.firstRelease release ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
          (supported.resolvingValuePlayers nullValue window values focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) before
          (PolicyExecution.initial _
            (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support ∧
      supported.resolvingStop nullValue window values focal deviator environment schedule ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
          (supported.resolvingValuePlayers nullValue window values focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) after
          (trace.firstRelease release)).support := by
  intro trace
  have hfull : supported.resolvingReplay nullValue window values focal
      deviator environment schedule ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (supported.resolvingValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)))
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support := by
    rw [resolvingReplay_law, FinDist.mem_support_pure]
  exact MessageApplication.tracePolicies_prefixThrough_firstRelease_split _ _ _
    (fun execution : (supported.resolvingRuntime
        nullValue window).messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty) release schedule _ _ hfull

/-- Every occupied non-focal reference slot at the common timeout snapshot retains its
assigned graph value, even when the snapshot already contains public defaults. -/
theorem resolvingStop_honest_lookup (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty) (howner : owner ≠ focal)
    (hlookup : (supported.resolvingStop nullValue window values focal
      deviator environment schedule).native.application.service.lookup (owner, node.val) =
        some value) : value = values node := by
  have hfull : supported.resolvingReplay nullValue window values focal
      deviator environment schedule ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (supported.resolvingValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)))
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support := by
    rw [resolvingReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, _, _, hprefix, _⟩ :=
    MessageApplication.tracePolicies_firstRelease_split _ _ _
      (fun execution :
          (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution =>
        !execution.native.application.visible.timeouts.isEmpty) schedule _ _ hfull
  exact supported.runPolicies_resolvingValues_lookup nullValue window focal
    (fun history view => FinDist.pure (deviator history view))
    (fun history view => FinDist.pure (environment history view)) values front _ hprefix
    owner node value howner hlookup

/-- Every stopped replay snapshot is supported by an actual invocation prefix
of the same runner, with no replacement transition at the cutoff. -/
theorem resolvingReplay_prefix_run_support (values : Fin G.nodeCount → L.Val ty) :
    ∃ front suffix, schedule = front ++ suffix ∧
      (supported.resolvingReplay nullValue window values focal
        deviator environment schedule |>.prefixThrough release).last ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
          (supported.resolvingValuePlayers nullValue window values focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) front
          (PolicyExecution.initial _
            (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support := by
  have hfull : supported.resolvingReplay nullValue window values focal
      deviator environment schedule ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (supported.resolvingValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)))
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support := by
    rw [resolvingReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, suffix, hschedule, hprefix, _⟩ :=
    MessageApplication.tracePolicies_firstRelease_split _ _ _ release schedule _ _ hfull
  exact ⟨front, suffix, hschedule, by
    simpa only [PolicyTrace.prefixThrough_last] using hprefix⟩

theorem resolvingReplay_registration (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty) (howner : owner ≠ focal)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        (supported.resolvingReplay nullValue window values focal
          deviator environment schedule |>.prefixThrough release).last.nativeTrace) :
    value = values node := by
  obtain ⟨front, _, _, hprefix⟩ := supported.resolvingReplay_prefix_run_support
    nullValue window focal deviator environment schedule release values
  exact (supported.runPolicies_resolvingValues_registration nullValue window focal
    (fun history view => FinDist.pure (deviator history view))
    (fun history view => FinDist.pure (environment history view)) values front _ hprefix
    owner node value howner htrace).1

/-- Recorded non-focal reference registrations occupy precisely their graph-owned slots
with the assigned values, even if the prefix includes timeout transitions. -/
theorem resolvingReplay_registration_lookup (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty) (howner : owner ≠ focal)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        (supported.resolvingReplay nullValue window values focal
          deviator environment schedule |>.prefixThrough release).last.nativeTrace) :
    (supported.resolvingReplay nullValue window values focal
      deviator environment schedule |>.prefixThrough release).last.native.application.service.lookup
        (owner, node.val) = some (values node) ∧
      ∃ guard, (G.nodeRow node).sem = .commit owner guard := by
  obtain ⟨front, _, _, hprefix⟩ := supported.resolvingReplay_prefix_run_support
    nullValue window focal deviator environment schedule release values
  obtain ⟨stored, hstored⟩ :=
    (supported.resolvingRuntime nullValue window).runPolicies_registration_occupied
      _ _ front _ hprefix owner node.val value htrace
  have hvalue := supported.runPolicies_resolvingValues_lookup nullValue window focal
    (fun history view => FinDist.pure (deviator history view))
    (fun history view => FinDist.pure (environment history view)) values front _ hprefix
    owner node stored howner hstored
  have hregistered := supported.runPolicies_resolvingValues_registration nullValue window focal
    (fun history view => FinDist.pure (deviator history view))
    (fun history view => FinDist.pure (environment history view)) values front _ hprefix
    owner node value howner htrace
  exact ⟨hvalue ▸ hstored, hregistered.2⟩

theorem resolvingReplay_lookup_origin (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (slot : Nat) (value : L.Val ty)
    (hlookup : (supported.resolvingReplay nullValue window values focal
      deviator environment schedule |>.prefixThrough release).last.native.application.service.lookup
        (owner, slot) = some value) :
    (.privateCommand owner ⟨(slot, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        (supported.resolvingReplay nullValue window values focal
          deviator environment schedule |>.prefixThrough release).last.nativeTrace := by
  obtain ⟨front, _, _, hprefix⟩ := supported.resolvingReplay_prefix_run_support
    nullValue window focal deviator environment schedule release values
  exact (supported.resolvingRuntime nullValue window).runPolicies_lookup_origin
    _ _ front _ hprefix owner slot value hlookup

/-- Exact replay equivalence, retaining every local history, pool snapshot,
clock transition, and receipt. Agreement is needed only at the non-focal values
registered by the left replay, not at every potential graph decision. -/
theorem resolvingReplay_prefix_eq_iff (left right : Fin G.nodeCount → L.Val ty) :
    (supported.resolvingReplay nullValue window left focal
      deviator environment schedule).prefixThrough release =
      (supported.resolvingReplay nullValue window right focal
        deviator environment schedule).prefixThrough release ↔
      ∀ owner (node : Fin G.nodeCount) (value : L.Val ty), owner ≠ focal →
        (.privateCommand owner ⟨(node.val, value)⟩ :
          (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
            (supported.resolvingReplay nullValue window left focal
              deviator environment schedule |>.prefixThrough release).last.nativeTrace →
                left node = right node := by
  constructor
  · intro heq owner node value howner htrace
    have hl := supported.resolvingReplay_registration nullValue window focal deviator environment
      schedule release left owner node value howner htrace
    have hr := supported.resolvingReplay_registration nullValue window focal deviator environment
      schedule release right owner node value howner (heq ▸ htrace)
    exact hl.symm.trans hr
  · intro hagrees
    have hleft : (supported.resolvingReplay nullValue window left focal
        deviator environment schedule).prefixThrough release ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
          (supported.resolvingValuePlayers nullValue window left focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) schedule
          (PolicyExecution.initial _
            (State.initial _ (supported.resolvingRuntime nullValue window).initial)) |>.map
              (PolicyTrace.prefixThrough release)).support := by
      rw [resolvingReplay_law, FinDist.map_pure, FinDist.mem_support_pure]
    have hright := supported.tracePolicies_resolvingValues_transfer nullValue window focal
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) left right release schedule _ _
      hleft hagrees
    rwa [resolvingReplay_law, FinDist.map_pure, FinDist.mem_support_pure] at hright

/-- A stopped replay is determined exactly by its occupied non-focal graph
slots. Out-of-program and focal registrations add no assignment constraints. -/
theorem resolvingReplay_prefix_eq_iff_lookup (left right : Fin G.nodeCount → L.Val ty) :
    (supported.resolvingReplay nullValue window left focal
      deviator environment schedule).prefixThrough release =
      (supported.resolvingReplay nullValue window right focal
        deviator environment schedule).prefixThrough release ↔
      ∀ owner (node : Fin G.nodeCount) guard,
        (G.nodeRow node).sem = .commit owner guard → owner ≠ focal → ∀ value,
        (supported.resolvingReplay nullValue window left focal deviator environment schedule
          |>.prefixThrough release).last.native.application.service.lookup
          (owner, node.val) = some value → right node = value := by
  rw [supported.resolvingReplay_prefix_eq_iff nullValue window focal deviator environment
    schedule release left right]
  constructor
  · intro h owner node _ _ howner value hlookup
    have htrace := supported.resolvingReplay_lookup_origin nullValue window focal deviator
      environment schedule release left owner node.val value hlookup
    have hvalue := supported.resolvingReplay_registration nullValue window focal deviator
      environment schedule release left owner node value howner htrace
    exact (h owner node value howner htrace).symm.trans hvalue.symm
  · intro h owner node value howner htrace
    obtain ⟨hlookup, guard, hsem⟩ := supported.resolvingReplay_registration_lookup
      nullValue window focal deviator environment schedule release left owner node value
        howner htrace
    exact (h owner node guard hsem howner (left node) hlookup).symm

/-- For any joint assignment law, the mass of a stopped replay is the mass
of its non-focal registration cylinder. No independence of assignment coordinates
is assumed. A later source coupling may supply a correlated assignment law. -/
theorem resolvingReplay_cylinder_probability (assignments : FinDist (Fin G.nodeCount → L.Val ty))
    (reference : Fin G.nodeCount → L.Val ty) :
    (assignments.map (fun values =>
      (supported.resolvingReplay nullValue window values focal
        deviator environment schedule).prefixThrough release)).prob
        (supported.resolvingReplay nullValue window reference focal
          deviator environment schedule |>.prefixThrough release) =
      assignments.probOf {values | ∀ owner (node : Fin G.nodeCount) (value : L.Val ty),
        owner ≠ focal →
          (.privateCommand owner ⟨(node.val, value)⟩ :
            (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
              (supported.resolvingReplay nullValue window reference focal
                deviator environment schedule |>.prefixThrough release).last.nativeTrace →
                  reference node = values node} := by
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  congr 1
  ext values
  exact eq_comm.trans (supported.resolvingReplay_prefix_eq_iff nullValue window focal
    deviator environment schedule release reference values)

end Vegas.EventGraph.SealedShape

/-- info: 'Vegas.EventGraph.SealedShape.resolvingReplay_prefix_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.resolvingReplay_prefix_eq_iff

/-- info: 'Vegas.EventGraph.SealedShape.resolvingReplay_cylinder_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.resolvingReplay_cylinder_probability
