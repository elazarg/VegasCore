/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicy
import Interaction.MessageApplicationPolicyLaws
import Interaction.MessageApplicationPolicyTrace

/-! # Assigned-proposal execution of the compiled sealed command generator

An assigned proposal kernel fixes a raw value at each graph commitment without
changing the shared registration, submission, or opening code. It is the
deterministic reference execution used by causal backtranslation; the actual
shared runner still supplies every history, pending packet, delivery, inclusion,
and receipt. A separate assigned commit policy is available only when the
fragment certificate proves those values legal graph choices.

These raw replay laws concern the registered and candidate hosts before optional
opening validation. Allowing rejecting guards in `SealedShape` does not by itself
establish their probability or strategy laws for a guarded host.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Assigned legal graph choices require a certificate that every value passes. -/
def assignedCommitPolicy (supported : SealedFragment G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player) : CommitPolicy G who :=
  fun node guard hsem reads =>
    FinDist.pure ⟨cast (congrArg L.Val (supported.commitType node who guard hsem).symm)
      (values node), supported.commitGuard node who guard hsem _ reads⟩

end Vegas.EventGraph.SealedFragment

namespace Vegas.EventGraph.SealedShape

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Fix raw native preparations, including values that fail a graph guard.
No graph legality proof is asserted and no invalid value is replaced. -/
def assignedProposals (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player) : ProposalPolicy G who :=
  fun node guard hsem _ =>
    FinDist.pure (cast (congrArg L.Val (supported.commitType node who guard hsem).symm)
      (values node))

/-- The only assignment coordinate read by an invocation is its fresh private
registration, if any. Cached submissions, openings, and waits ignore the rest
of the assignment. The statement uses the shared compiled command generator. -/
theorem selected_proposals_congr (supported : SealedShape G ty)
    (left right : Fin G.nodeCount → L.Val ty) (who : Player) (completed : List Nat)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hcommand : command ∈
      ((G.nodeOrder.findSome? (supported.nodeCommand? who completed
        (supported.assignedProposals left who) history view store)).getD (FinDist.pure
          .wait)).support)
    (hagrees : ∀ node : Fin G.nodeCount,
      command = .privateCommand ⟨(node.val, left node)⟩ → left node = right node) :
    (G.nodeOrder.findSome? (supported.nodeCommand? who completed
      (supported.assignedProposals right who) history view store)).getD (FinDist.pure .wait) =
      FinDist.pure command := by
  cases command with
  | privateCommand request =>
      obtain ⟨node, guard, hsem, reads, _, _, _, hkernel⟩ :=
        supported.selected_registration_kernel who completed (supported.assignedProposals left who)
          history view store request.down.1 request.down.2 hcommand
      rw [hkernel (supported.assignedProposals left who)] at hcommand
      simp only [assignedProposals, FinDist.map_pure, cast_cast, cast_eq,
        FinDist.mem_support_pure] at hcommand
      have heq := hagrees node hcommand
      rw [hkernel (supported.assignedProposals right who)]
      simp only [assignedProposals, FinDist.map_pure, cast_cast, cast_eq, ← heq]
      exact congrArg FinDist.pure hcommand.symm
  | submit payload | replay id | wait =>
      exact supported.selected_nonregistration_law who completed
        (supported.assignedProposals left who) (supported.assignedProposals right who) history
          view store
        _ hcommand (fun _ h => by cases h)

/-- Reference players use assigned proposal values; the focal principal retains
its arbitrary native policy, including all pending-message observations. -/
def valuePlayers (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy) :
    Player → (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy :=
  GameTheory.Profile.update
    (sig := MessageApplication.policySignature Player
      (supported.compile.messageApplication (Value := L.Val ty)))
    (fun who => supported.proposalPlayerPolicy who (supported.assignedProposals values who)) focal
      deviator

/-- Every non-focal reference registration carries precisely the assigned
value of its graph node. No other assignment coordinate is encoded there. -/
theorem selected_proposals_registration (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player) (completed : List Nat)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L)
    (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      ((G.nodeOrder.findSome? (supported.nodeCommand? who completed
        (supported.assignedProposals values who) history view store)).getD
          (FinDist.pure .wait)).support) :
    ∃ node : Fin G.nodeCount, slot = node.val ∧ value = values node ∧
      ∃ guard, (G.nodeRow node).sem = .commit who guard := by
  obtain ⟨node, guard, hsem, reads, hslot, _, _, hkernel⟩ :=
    supported.selected_registration_kernel who completed (supported.assignedProposals values who)
      history view store slot value hcommand
  rw [hkernel (supported.assignedProposals values who)] at hcommand
  simp only [assignedProposals, FinDist.map_pure, cast_cast, cast_eq,
    FinDist.mem_support_pure, MessageInterface.PlayerCommand.privateCommand.injEq] at hcommand
  exact ⟨node, hslot, (Prod.mk.inj (congrArg ULift.down hcommand)).2, guard, hsem⟩

/-- Changing only unused non-focal assignment coordinates preserves an entire
supported native execution, including private histories and the pending pool.
The deviator and environment can be randomized and adaptive. -/
theorem runPolicies_valuePlayers_transfer (supported : SealedShape G ty)
    (left right : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment : (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (initial final : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hfinal : final ∈ ((supported.compile.messageApplication (Value := L.Val ty)).runPolicies
      (supported.valuePlayers left focal deviator) environment schedule initial).support)
    (hagrees : ∀ owner (node : Fin G.nodeCount) (value : L.Val ty), owner ≠ focal →
      (.privateCommand owner ⟨(node.val, value)⟩ :
        (supported.compile.messageApplication (Value := L.Val ty)).Action) ∈ final.nativeTrace →
        left node = right node) :
    final ∈ ((supported.compile.messageApplication (Value := L.Val ty)).runPolicies
      (supported.valuePlayers right focal deviator) environment schedule initial).support := by
  let app := supported.compile.messageApplication (Value := L.Val ty)
  rw [← app.tracePolicies_last, FinDist.support_map] at hfinal ⊢
  obtain ⟨trace, htrace, rfl⟩ := hfinal
  refine ⟨trace, app.tracePolicies_support_transfer _ _ environment schedule initial trace
    htrace ?_, rfl⟩
  intro owner history view command hcommand hrecord
  by_cases howner : owner = focal
  · subst owner
    simpa only [valuePlayers, GameTheory.Profile.update_same] using hcommand
  · rw [valuePlayers, GameTheory.Profile.update_of_ne _ _ howner] at hcommand ⊢
    have hright := supported.selected_proposals_congr left right owner []
      history view _ command hcommand (fun node heq =>
        hagrees owner node (left node) howner (hrecord _ (by rw [heq]; rfl)))
    rw [SealedShape.proposalPlayerPolicy, hright, FinDist.mem_support_pure]

/-- Non-focal reference registrations in the actual native trace identify their
assigned graph values, even when the deviator and environment are randomized. -/
theorem runPolicies_valuePlayers_registration (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment : (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (final : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hfinal : final ∈ ((supported.compile.messageApplication (Value := L.Val ty)).runPolicies
      (supported.valuePlayers values focal deviator) environment schedule
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩))).support)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty) (howner : owner ≠ focal)
    (htrace : (.privateCommand owner ⟨(node.val, value)⟩ :
      (supported.compile.messageApplication (Value := L.Val ty)).Action) ∈ final.nativeTrace) :
    value = values node := by
  have hproperty :=
    (supported.compile.messageApplication (Value := L.Val ty)).runPolicies_action_property
      (fun action => ∀ who (index : Fin G.nodeCount) (registered : L.Val ty), who ≠ focal →
        action = .privateCommand who ⟨(index.val, registered)⟩ → registered = values index)
      (supported.valuePlayers values focal deviator) environment
      (by
        intro actor history view command hcommand action ha who index registered hwho heq
        rw [heq] at ha
        cases command with
        | privateCommand request =>
            simp only [MessageApplication.PlayerCommand.toAction, Option.some.injEq,
              MessageInterface.Action.privateCommand.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            rw [valuePlayers, GameTheory.Profile.update_of_ne _ _ hwho] at hcommand
            obtain ⟨actual, hindex, hvalue, _⟩ :=
              supported.selected_proposals_registration values actor [] history view
                _ index.val registered hcommand
            have hactual : actual = index := Fin.ext hindex.symm
            simpa only [hactual] using hvalue
        | submit payload | replay id | wait =>
            simp only [MessageApplication.PlayerCommand.toAction,
              Option.some.injEq] at ha
            cases ha)
      (by
        intro history view command _ action ha who index registered _ heq
        rw [heq] at ha
        cases command <;>
          simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
            Option.some.injEq] at ha <;> cases ha)
      schedule _ final (by simp only [MessageApplication.PolicyExecution.initial, List.not_mem_nil,
        false_implies, implies_true]) hfinal
  exact hproperty _ htrace owner node value howner rfl

private theorem replay_exists (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).View →
        (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (environment :
      List (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentObservation →
        (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicyCommand)
    (schedule : List (@MessageApplication.Invocation Player)) :
    ∃ final, (supported.compile.messageApplication (Value := L.Val ty)).runPolicies
      (supported.valuePlayers values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩)) =
      FinDist.pure final := by
  let app := supported.compile.messageApplication (Value := L.Val ty)
  have hplayers : ∀ who history view, ∃ command,
      supported.valuePlayers values focal
        (fun history view => FinDist.pure (deviator history view)) who history view =
          FinDist.pure command := by
    intro who history view
    by_cases hwho : who = focal
    · subst who
      exact ⟨deviator history view, by
        simp only [valuePlayers, GameTheory.Profile.update_same]⟩
    · obtain ⟨command, hcommand⟩ :=
        (supported.proposalPlayerPolicy who (supported.assignedProposals values who)
          history view).support_nonempty
      refine ⟨command, ?_⟩
      rw [valuePlayers, GameTheory.Profile.update_of_ne _ _ hwho]
      exact supported.selected_proposals_congr values values who [] history view
        _ command hcommand (fun _ _ => rfl)
  obtain ⟨trace, htrace⟩ := app.tracePolicies_pure
    (supported.valuePlayers values focal (fun history view => FinDist.pure (deviator history view)))
    (fun history view => FinDist.pure (environment history view)) hplayers
    (fun _ _ => ⟨_, rfl⟩) (fun _ command => nomatch command.down) schedule
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩))
  refine ⟨trace.last, ?_⟩
  rw [← app.tracePolicies_last, htrace, FinDist.map_pure]

/-- Deterministic value substitution evaluated by the shared native runner.
This selects its unique outcome; it does not implement a second machine. -/
def replay (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).View →
        (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (environment :
      List (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentObservation →
        (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicyCommand)
    (schedule : List (@MessageApplication.Invocation Player)) :
    (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution :=
  Classical.choose (supported.replay_exists values focal deviator environment schedule)

theorem replay_law (supported : SealedShape G ty)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).View →
        (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (environment :
      List (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentObservation →
        (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicyCommand)
    (schedule : List (@MessageApplication.Invocation Player)) :
    (supported.compile.messageApplication (Value := L.Val ty)).runPolicies
      (supported.valuePlayers values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩)) =
      FinDist.pure (supported.replay values focal deviator environment schedule) :=
  Classical.choose_spec (supported.replay_exists values focal deviator environment schedule)

/-- A whole native replay depends only on non-focal values actually registered
in that replay. Arbitrary deterministic deviations and adaptive service
commands are preserved, with the entire final native execution record. -/
theorem replay_congr (supported : SealedShape G ty)
    (left right : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).View →
        (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (environment :
      List (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentObservation →
        (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicyCommand)
    (schedule : List (@MessageApplication.Invocation Player))
    (hagrees : ∀ owner (node : Fin G.nodeCount) (value : L.Val ty), owner ≠ focal →
      (.privateCommand owner ⟨(node.val, value)⟩ :
        (supported.compile.messageApplication (Value := L.Val ty)).Action) ∈
        (supported.replay left focal deviator environment schedule).nativeTrace →
      left node = right node) :
    supported.replay left focal deviator environment schedule =
      supported.replay right focal deviator environment schedule := by
  have hleft : supported.replay left focal deviator environment schedule ∈
      ((supported.compile.messageApplication (Value := L.Val ty)).runPolicies
        (supported.valuePlayers left focal
          (fun history view => FinDist.pure (deviator history view)))
        (fun history view => FinDist.pure (environment history view)) schedule
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩))).support := by
    rw [supported.replay_law, FinDist.mem_support_pure]
  have hright := supported.runPolicies_valuePlayers_transfer left right focal
    (fun history view => FinDist.pure (deviator history view))
    (fun history view => FinDist.pure (environment history view)) schedule _ _ hleft hagrees
  rwa [supported.replay_law, FinDist.mem_support_pure] at hright

/-- Exact cylinder characterization for the assigned-proposal native runner.
Equality of entire executions is equivalent to equality at the non-focal
registration coordinates recorded by one execution. Every invocation prefix
is an instance, by choosing that prefix as the schedule. -/
theorem replay_eq_iff (supported : SealedShape G ty)
    (left right : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).View →
        (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (environment :
      List (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentEntry →
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentObservation →
        (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicyCommand)
    (schedule : List (@MessageApplication.Invocation Player)) :
    supported.replay left focal deviator environment schedule =
        supported.replay right focal deviator environment schedule ↔
      ∀ owner (node : Fin G.nodeCount) (value : L.Val ty), owner ≠ focal →
        (.privateCommand owner ⟨(node.val, value)⟩ :
          (supported.compile.messageApplication (Value := L.Val ty)).Action) ∈
            (supported.replay left focal deviator environment schedule).nativeTrace →
        left node = right node := by
  constructor
  · intro heq owner node value howner htrace
    have hleft := supported.runPolicies_valuePlayers_registration left focal
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) schedule
      (supported.replay left focal deviator environment schedule)
      (by rw [supported.replay_law, FinDist.mem_support_pure]) owner node value howner htrace
    have hright := supported.runPolicies_valuePlayers_registration right focal
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) schedule
      (supported.replay right focal deviator environment schedule)
      (by rw [supported.replay_law, FinDist.mem_support_pure]) owner node value howner
      (heq ▸ htrace)
    exact hleft.symm.trans hright
  · exact supported.replay_congr left right focal deviator environment schedule

end Vegas.EventGraph.SealedShape

/-- info: 'Vegas.EventGraph.SealedShape.replay_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.replay_eq_iff

namespace Vegas.EventGraph.SealedFragment

/-- Legal assigned graph policies implement the same raw reference proposals. -/
@[simp] theorem assignedCommitPolicy_proposals {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} {ty : L.Ty} (supported : SealedFragment G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player) :
    (supported.assignedCommitPolicy values who).proposals =
      supported.assignedProposals values who := by
  funext node guard hsem reads
  simp only [CommitPolicy.proposals, assignedCommitPolicy, SealedShape.assignedProposals,
    GameTheory.Math.Probability.FinDist.map_pure]

end Vegas.EventGraph.SealedFragment
