/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReplay
import Interaction.SealedResolutionProvenance

/-! # All-assigned sealed-resolution replay cylinders

Every principal uses the resolving policy with its source commitment values
fixed by one graph assignment.  The resulting deterministic trace supports a
focal-free cylinder characterization for honest source execution.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Resolve every player's source choices from the same graph assignment. -/
def resolvingAssignedPlayers (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (values : Fin G.nodeCount → L.Val ty) :
    Player → (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy :=
  fun who => supported.resolvingPolicy nullValue window who (supported.valuePolicy values who)

variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)

private theorem resolvingAssignedReplay_exists
    (values : Fin G.nodeCount → L.Val ty)
    (environment :
      List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
    (schedule : List (@Invocation Player)) :
    ∃ trace, (supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
      (supported.resolvingAssignedPlayers nullValue window values)
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _
        (supported.resolvingRuntime nullValue window).initial)) = FinDist.pure trace := by
  apply MessageApplication.tracePolicies_pure _ _ _ ?_
    (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩)
  intro who history view
  exact supported.resolvingPolicy_valuePolicy_pure nullValue window values who history view

/-- The unique full trace of an all-assigned resolving execution with one
fixed environment response. -/
def resolvingAssignedReplay
    (values : Fin G.nodeCount → L.Val ty)
    (environment :
      List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
    (schedule : List (@Invocation Player)) :
    (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace :=
  Classical.choose
    (supported.resolvingAssignedReplay_exists nullValue window values environment schedule)

/-- The all-assigned player and fixed-environment law is a point mass at its
replay trace. -/
theorem resolvingAssignedReplay_law
    (values : Fin G.nodeCount → L.Val ty)
    (environment :
      List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
    (schedule : List (@Invocation Player)) :
    (supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
      (supported.resolvingAssignedPlayers nullValue window values)
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _
        (supported.resolvingRuntime nullValue window).initial)) =
      FinDist.pure
        (supported.resolvingAssignedReplay nullValue window values environment schedule) :=
  Classical.choose_spec
    (supported.resolvingAssignedReplay_exists nullValue window values environment schedule)

private theorem tracePolicies_resolvingAssigned_transfer
    (left right : Fin G.nodeCount → L.Val ty)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (release :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution → Bool)
    (schedule : List (@Invocation Player))
    (initial : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (supported.resolvingAssignedPlayers nullValue window left)
        environment schedule initial |>.map (PolicyTrace.prefixThrough release)).support)
    (hagrees : ∀ owner (node : Fin G.nodeCount) (value : L.Val ty),
      (.privateCommand owner ⟨(node.val, value)⟩ :
        (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
          trace.last.nativeTrace → left node = right node) :
    trace ∈ ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
      (supported.resolvingAssignedPlayers nullValue window right)
      environment schedule initial |>.map (PolicyTrace.prefixThrough release)).support := by
  apply MessageApplication.tracePolicies_prefix_support_transfer _ _ _ environment release schedule
    initial trace htrace
  intro owner history view command hcommand hrecord
  change command ∈
    (supported.resolvingPolicy nullValue window owner (supported.valuePolicy left owner)
      history view).support at hcommand
  have hright := supported.selected_valuePolicy_congr left right owner view.application.timeouts
    ((supported.resolvingRuntime nullValue window).eventHistory history)
    ((supported.resolvingRuntime nullValue window).eventView view)
    _ command hcommand (fun node heq =>
      hagrees owner node (left node) (hrecord _ (by rw [heq]; rfl)))
  change supported.resolvingPolicy nullValue window owner (supported.valuePolicy right owner)
    history view = FinDist.pure command at hright
  change command ∈
    (supported.resolvingPolicy nullValue window owner (supported.valuePolicy right owner)
      history view).support
  rw [hright, FinDist.mem_support_pure]

/-- Every private registration in an all-assigned supported run carries its
assigned value and belongs to a real commitment node. -/
theorem runPolicies_resolvingAssigned_registration
    (values : Fin G.nodeCount → L.Val ty)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (final : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hfinal : final ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
        (supported.resolvingAssignedPlayers nullValue window values)
        environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        final.nativeTrace) :
    value = values node ∧ ∃ guard, (G.nodeRow node).sem = .commit owner guard := by
  have hproperty :=
    (supported.resolvingRuntime nullValue window).messageApplication.runPolicies_action_property
      (fun action => ∀ who (index : Fin G.nodeCount) (registered : L.Val ty),
        action = .privateCommand who ⟨(index.val, registered)⟩ →
          registered = values index ∧ ∃ guard, (G.nodeRow index).sem = .commit who guard)
      (supported.resolvingAssignedPlayers nullValue window values) environment
      (by
        intro actor history view command hcommand action ha who index registered heq
        rw [heq] at ha
        cases command with
        | privateCommand request =>
            simp only [PlayerCommand.toAction, Option.some.injEq,
              MessageInterface.Action.privateCommand.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            change .privateCommand ⟨(index.val, registered)⟩ ∈
              (supported.resolvingPolicy nullValue window actor
                (supported.valuePolicy values actor) history view).support at hcommand
            obtain ⟨actual, hindex, hvalue, guard, hsem⟩ :=
              supported.selected_valuePolicy_registration values actor view.application.timeouts
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
        intro history view command _ action ha who index registered heq
        rw [heq] at ha
        cases command <;>
          simp only [EnvironmentPolicyCommand.toAction, Option.some.injEq] at ha <;> cases ha)
      schedule _ final (by simp only [PolicyExecution.initial, List.not_mem_nil,
        false_implies, implies_true]) hfinal
  exact hproperty _ htrace owner node value rfl

/-- An occupied source-indexed service slot in an all-assigned supported run
contains exactly its assignment value and has the claimed commitment owner. -/
theorem runPolicies_resolvingAssigned_lookup
    (values : Fin G.nodeCount → L.Val ty)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (final : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hfinal : final ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
        (supported.resolvingAssignedPlayers nullValue window values)
        environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty)
    (hlookup : final.native.application.service.lookup (owner, node.val) = some value) :
    value = values node ∧ ∃ guard, (G.nodeRow node).sem = .commit owner guard := by
  exact supported.runPolicies_resolvingAssigned_registration nullValue window values environment
    schedule final hfinal owner node value
      ((supported.resolvingRuntime nullValue window).runPolicies_lookup_origin
        _ _ schedule final hfinal owner node.val value hlookup)

variable (environment :
  List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))
variable (release :
  (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution → Bool)

/-- The selected snapshot of an all-assigned replay is supported by an actual
prefix of the same native runner. -/
theorem resolvingAssignedReplay_prefix_run_support
    (values : Fin G.nodeCount → L.Val ty) :
    ∃ front suffix, schedule = front ++ suffix ∧
      (supported.resolvingAssignedReplay nullValue window values environment schedule
        |>.prefixThrough release).last ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
          (supported.resolvingAssignedPlayers nullValue window values)
          (fun history view => FinDist.pure (environment history view)) front
          (PolicyExecution.initial _
            (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support := by
  have hfull : supported.resolvingAssignedReplay nullValue window values environment schedule ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (supported.resolvingAssignedPlayers nullValue window values)
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support := by
    rw [resolvingAssignedReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, suffix, hschedule, hprefix, _⟩ :=
    MessageApplication.tracePolicies_firstRelease_split _ _ _ release schedule _ _ hfull
  exact ⟨front, suffix, hschedule, by
    simpa only [PolicyTrace.prefixThrough_last] using hprefix⟩

theorem resolvingAssignedReplay_registration
    (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        (supported.resolvingAssignedReplay nullValue window values environment schedule
          |>.prefixThrough release).last.nativeTrace) :
    value = values node ∧ ∃ guard, (G.nodeRow node).sem = .commit owner guard := by
  obtain ⟨front, _, _, hprefix⟩ := supported.resolvingAssignedReplay_prefix_run_support
    nullValue window environment schedule release values
  exact supported.runPolicies_resolvingAssigned_registration nullValue window values
    (fun history view => FinDist.pure (environment history view)) front _ hprefix
    owner node value htrace

theorem resolvingAssignedReplay_registration_lookup
    (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        (supported.resolvingAssignedReplay nullValue window values environment schedule
          |>.prefixThrough release).last.nativeTrace) :
    (supported.resolvingAssignedReplay nullValue window values environment schedule
      |>.prefixThrough release).last.native.application.service.lookup (owner, node.val) =
        some (values node) ∧
      ∃ guard, (G.nodeRow node).sem = .commit owner guard := by
  obtain ⟨front, _, _, hprefix⟩ := supported.resolvingAssignedReplay_prefix_run_support
    nullValue window environment schedule release values
  obtain ⟨stored, hstored⟩ :=
    (supported.resolvingRuntime nullValue window).runPolicies_registration_occupied
      _ _ front _ hprefix owner node.val value htrace
  have hvalue := supported.runPolicies_resolvingAssigned_lookup nullValue window values
    (fun history view => FinDist.pure (environment history view)) front _ hprefix
    owner node stored hstored
  exact ⟨hvalue.1 ▸ hstored, hvalue.2⟩

theorem resolvingAssignedReplay_lookup_origin
    (values : Fin G.nodeCount → L.Val ty)
    (owner : Player) (slot : Nat) (value : L.Val ty)
    (hlookup : (supported.resolvingAssignedReplay nullValue window values environment schedule
      |>.prefixThrough release).last.native.application.service.lookup (owner, slot) =
        some value) :
    (.privateCommand owner ⟨(slot, value)⟩ :
      (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
        (supported.resolvingAssignedReplay nullValue window values environment schedule
          |>.prefixThrough release).last.nativeTrace := by
  obtain ⟨front, _, _, hprefix⟩ := supported.resolvingAssignedReplay_prefix_run_support
    nullValue window environment schedule release values
  exact (supported.resolvingRuntime nullValue window).runPolicies_lookup_origin
    _ _ front _ hprefix owner slot value hlookup

/-- Equality of stopped all-assigned replays is equivalent to agreement on
the assignment coordinates registered by the left replay. -/
theorem resolvingAssignedReplay_prefix_eq_iff
    (left right : Fin G.nodeCount → L.Val ty) :
    (supported.resolvingAssignedReplay nullValue window left environment schedule
      |>.prefixThrough release) =
      (supported.resolvingAssignedReplay nullValue window right environment schedule
        |>.prefixThrough release) ↔
      ∀ owner (node : Fin G.nodeCount) (value : L.Val ty),
        (.privateCommand owner ⟨(node.val, value)⟩ :
          (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
            (supported.resolvingAssignedReplay nullValue window left environment schedule
              |>.prefixThrough release).last.nativeTrace → left node = right node := by
  constructor
  · intro heq owner node value htrace
    have hleft := supported.resolvingAssignedReplay_registration nullValue window environment
      schedule release left owner node value htrace
    have hright := supported.resolvingAssignedReplay_registration nullValue window environment
      schedule release right owner node value (heq ▸ htrace)
    exact hleft.1.symm.trans hright.1
  · intro hagrees
    have hleft :
        (supported.resolvingAssignedReplay nullValue window left environment schedule
          |>.prefixThrough release) ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
          (supported.resolvingAssignedPlayers nullValue window left)
          (fun history view => FinDist.pure (environment history view)) schedule
          (PolicyExecution.initial _
            (State.initial _ (supported.resolvingRuntime nullValue window).initial)) |>.map
              (PolicyTrace.prefixThrough release)).support := by
      rw [resolvingAssignedReplay_law, FinDist.map_pure, FinDist.mem_support_pure]
    have hright := supported.tracePolicies_resolvingAssigned_transfer nullValue window left right
      (fun history view => FinDist.pure (environment history view)) release schedule _ _ hleft
      hagrees
    rwa [resolvingAssignedReplay_law, FinDist.map_pure, FinDist.mem_support_pure] at hright

/-- Two stopped all-assigned replays are identical exactly when the right
assignment agrees with every real commitment slot occupied by the left replay. -/
theorem resolvingAssignedReplay_prefix_eq_iff_lookup
    (left right : Fin G.nodeCount → L.Val ty) :
    (supported.resolvingAssignedReplay nullValue window left environment schedule
      |>.prefixThrough release) =
      (supported.resolvingAssignedReplay nullValue window right environment schedule
        |>.prefixThrough release) ↔
      ∀ owner (node : Fin G.nodeCount) guard,
        (G.nodeRow node).sem = .commit owner guard → ∀ value,
        (supported.resolvingAssignedReplay nullValue window left environment schedule
          |>.prefixThrough release).last.native.application.service.lookup
            (owner, node.val) = some value → right node = value := by
  rw [supported.resolvingAssignedReplay_prefix_eq_iff nullValue window environment schedule
    release left right]
  constructor
  · intro hagrees owner node guard hsem value hlookup
    have htrace := supported.resolvingAssignedReplay_lookup_origin nullValue window environment
      schedule release left owner node.val value hlookup
    have hvalue := supported.resolvingAssignedReplay_registration nullValue window environment
      schedule release left owner node value htrace
    exact (hagrees owner node value htrace).symm.trans hvalue.1.symm
  · intro hagrees owner node value htrace
    obtain ⟨hlookup, guard, hsem⟩ :=
      supported.resolvingAssignedReplay_registration_lookup nullValue window environment schedule
        release left owner node value htrace
    exact (hagrees owner node guard hsem (left node) hlookup).symm

/-- The mass of an all-assigned stopped replay is the mass of its complete
occupied-commitment cylinder under any joint assignment law. -/
theorem resolvingAssignedReplay_cylinder_probability
    (assignments : FinDist (Fin G.nodeCount → L.Val ty))
    (reference : Fin G.nodeCount → L.Val ty) :
    (assignments.map (fun values =>
      (supported.resolvingAssignedReplay nullValue window values environment schedule
        |>.prefixThrough release))).prob
        (supported.resolvingAssignedReplay nullValue window reference environment schedule
          |>.prefixThrough release) =
      assignments.probOf {values | ∀ owner (node : Fin G.nodeCount) guard,
        (G.nodeRow node).sem = .commit owner guard → ∀ value,
        (supported.resolvingAssignedReplay nullValue window reference environment schedule
          |>.prefixThrough release).last.native.application.service.lookup
            (owner, node.val) = some value → values node = value} := by
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  congr 1
  ext values
  exact eq_comm.trans (supported.resolvingAssignedReplay_prefix_eq_iff_lookup nullValue window
    environment schedule release reference values)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.resolvingAssignedReplay_prefix_eq_iff_lookup'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.resolvingAssignedReplay_prefix_eq_iff_lookup
