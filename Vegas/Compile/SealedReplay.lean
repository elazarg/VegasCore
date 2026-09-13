/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicy
import Interaction.MessageApplicationPolicyLaws

/-! # Value-substituted execution of the compiled sealed policy

The value policy fixes a value at each graph commitment without changing the
native policy's registration, submission, or opening code. It is the deterministic
evaluation used by the causal source backtranslation: the actual shared runner
still supplies every history, pending packet, delivery, inclusion, and receipt.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Substitute the supplied node value for a source kernel's fresh draw. -/
def valuePolicy (supported : SealedFragment G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player) : CommitPolicy G who :=
  fun node guard hsem reads =>
    FinDist.pure ⟨cast (congrArg L.Val (supported.commitType node who guard hsem).symm)
      (values node), supported.commitGuard node who guard hsem _ reads⟩

private theorem commitCommand_valuePolicy_congr (supported : SealedFragment G ty)
    (left right : Fin G.nodeCount → L.Val ty) (who : Player)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (store : Store L)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hcommand : command ∈
      (supported.commitCommand who (supported.valuePolicy left who)
        node guard hsem history store).support)
    (hagrees : command = .privateCommand ⟨(node.val, left node)⟩ → left node = right node) :
    supported.commitCommand who (supported.valuePolicy right who)
      node guard hsem history store = FinDist.pure command := by
  unfold commitCommand at hcommand ⊢
  split at hcommand
  · exact congrArg FinDist.pure (FinDist.mem_support_pure.mp hcommand).symm
  · split at hcommand
    · exact congrArg FinDist.pure (FinDist.mem_support_pure.mp hcommand).symm
    · simp only [valuePolicy, FinDist.map_pure, cast_cast, cast_eq] at hcommand ⊢
      have heq := FinDist.mem_support_pure.mp hcommand
      rw [← hagrees heq]
      exact congrArg FinDist.pure heq.symm

private theorem nodeCommand?_valuePolicy_congr (supported : SealedFragment G ty)
    (left right : Fin G.nodeCount → L.Val ty) (who : Player)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who [] (supported.valuePolicy left who)
      history view (supported.playerStore who history view) node = some law)
    (hcommand : command ∈ law.support)
    (hagrees : ∀ index : Fin G.nodeCount,
      command = .privateCommand ⟨(index.val, left index)⟩ → left index = right index) :
    supported.nodeCommand? who [] (supported.valuePolicy right who) history view
      (supported.playerStore who history view) node =
      some (FinDist.pure command) := by
  simp only [nodeCommand?, List.contains_nil, Bool.false_eq_true, ite_false,
    SealedRule.discharge_nil, SealedProgram.discharge_nil] at hselected ⊢
  split at hselected
  · rename_i hready
    rw [if_pos hready]
    split at hselected
    · rename_i owner guard hsem
      split at hselected
      · rename_i howner
        rw [dif_pos howner]
        rw [← Option.some.inj hselected] at hcommand
        rw [supported.commitCommand_valuePolicy_congr left right who node guard
          (howner ▸ hsem) history (supported.playerStore who history view)
          command hcommand (hagrees node)]
      · rename_i howner
        contradiction
    · rename_i source hsem
      cases hhandle : supported.compile.openingHandle? view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          simp only [hhandle, Option.map_some] at hselected ⊢
          split at hselected <;> rename_i hcache
          all_goals
            rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hcommand
            cases hcommand
            rfl
    · contradiction
  · contradiction

/-- The only assignment coordinate read by an invocation is its fresh private
registration, if any. Cached submissions, openings, and waits ignore the rest
of the assignment. The statement uses the actual compiled policy. -/
theorem playerPolicy_valuePolicy_congr (supported : SealedFragment G ty)
    (left right : Fin G.nodeCount → L.Val ty) (who : Player)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hcommand : command ∈
      (supported.playerPolicy who (supported.valuePolicy left who) history view).support)
    (hagrees : ∀ node : Fin G.nodeCount,
      command = .privateCommand ⟨(node.val, left node)⟩ → left node = right node) :
    supported.playerPolicy who (supported.valuePolicy right who) history view =
      FinDist.pure command := by
  unfold playerPolicy at hcommand ⊢
  cases hselected : G.nodeOrder.findSome?
      (supported.nodeCommand? who [] (supported.valuePolicy left who) history view
        (supported.playerStore who history view)) with
  | none =>
      simp only [hselected, Option.getD_none, FinDist.mem_support_pure] at hcommand
      have hnone : G.nodeOrder.findSome?
          (supported.nodeCommand? who [] (supported.valuePolicy right who) history view
            (supported.playerStore who history view)) = none := by
        apply List.findSome?_eq_none_iff.mpr
        intro node hnode
        exact (supported.nodeCommand?_none_iff who [] _ _ history history view _ _ node).mp
          (List.findSome?_eq_none_iff.mp hselected node hnode)
      simp only [hnone, Option.getD_none, hcommand]
  | some law =>
      simp only [hselected, Option.getD_some] at hcommand
      obtain ⟨front, node, rest, hnodes, hnode, hfront⟩ :=
        List.findSome?_eq_some_iff.mp hselected
      have hright : G.nodeOrder.findSome?
          (supported.nodeCommand? who [] (supported.valuePolicy right who) history view
            (supported.playerStore who history view)) =
          some (FinDist.pure command) := by
        apply List.findSome?_eq_some_iff.mpr
        refine ⟨front, node, rest, hnodes, ?_, ?_⟩
        · exact supported.nodeCommand?_valuePolicy_congr left right who history view
            node law command hnode hcommand hagrees
        · intro prior hprior
          exact (supported.nodeCommand?_none_iff who [] _ _ history history view _ _ prior).mp
            (hfront prior hprior)
      simp only [hright, Option.getD_some]

/-- Honest players use assigned source values; the focal principal retains
its arbitrary native policy, including all pending-message observations. -/
def valuePlayers (supported : SealedFragment G ty)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy) :
    Player → (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy :=
  GameTheory.Profile.update
    (sig := MessageApplication.policySignature Player
      (supported.compile.messageApplication (Value := L.Val ty)))
    (fun who => supported.playerPolicy who (supported.valuePolicy values who)) focal deviator

private theorem nodeCommand?_valuePolicy_registration (supported : SealedFragment G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (slot : Nat) (value : L.Val ty)
    (hselected : supported.nodeCommand? who [] (supported.valuePolicy values who)
      history view (supported.playerStore who history view) node = some law)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈ law.support) :
    slot = node.val ∧ value = values node := by
  simp only [nodeCommand?, List.contains_nil, Bool.false_eq_true, ite_false,
    SealedRule.discharge_nil, SealedProgram.discharge_nil] at hselected
  split at hselected
  · split at hselected
    · split at hselected
      · rw [← Option.some.inj hselected] at hcommand
        unfold commitCommand at hcommand
        split at hcommand
        · simp only [FinDist.mem_support_pure] at hcommand
          cases hcommand
        · split at hcommand
          · simp only [FinDist.mem_support_pure] at hcommand
            cases hcommand
          · simp only [valuePolicy, FinDist.map_pure, cast_cast, cast_eq,
              FinDist.mem_support_pure, MessageInterface.PlayerCommand.privateCommand.injEq]
              at hcommand
            exact Prod.mk.inj (congrArg ULift.down hcommand)
      · contradiction
    · cases hhandle : supported.compile.openingHandle? view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          simp only [hhandle, Option.map_some] at hselected
          split at hselected <;>
            rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hcommand <;>
            cases hcommand
    · contradiction
  · contradiction

/-- Every honest private registration carries precisely the substituted
value of its source node. No other assignment coordinate is encoded there. -/
theorem playerPolicy_valuePolicy_registration (supported : SealedFragment G ty)
    (values : Fin G.nodeCount → L.Val ty) (who : Player)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      (supported.playerPolicy who (supported.valuePolicy values who) history view).support) :
    ∃ node : Fin G.nodeCount, slot = node.val ∧ value = values node := by
  unfold playerPolicy at hcommand
  cases hselected : G.nodeOrder.findSome?
      (supported.nodeCommand? who [] (supported.valuePolicy values who) history view
        (supported.playerStore who history view)) with
  | none =>
      simp only [hselected, Option.getD_none, FinDist.mem_support_pure] at hcommand
      cases hcommand
  | some law =>
      simp only [hselected, Option.getD_some] at hcommand
      obtain ⟨node, _, hnode⟩ := List.exists_of_findSome?_eq_some hselected
      exact ⟨node, supported.nodeCommand?_valuePolicy_registration values who history view
        node law slot value hnode hcommand⟩

private theorem privateCommand_mem_trace (supported : SealedFragment G ty)
    (owner : Player) (slot : Nat) (value : L.Val ty)
    (initial next : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hnext : next ∈ ((supported.compile.messageApplication (Value := L.Val ty)).playerStep
      owner initial (.privateCommand ⟨(slot, value)⟩)).support) :
    .privateCommand owner ⟨(slot, value)⟩ ∈ next.nativeTrace := by
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at hnext
  subst next
  simp

/-- Changing only unused honest assignment coordinates preserves an entire
supported native execution, including private histories and the pending pool.
The deviator and environment can be randomized and adaptive. -/
theorem runPolicies_valuePlayers_transfer (supported : SealedFragment G ty)
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
  induction schedule generalizing initial with
  | nil => exact hfinal
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
        at hfinal ⊢
      obtain ⟨middle, hmiddle, hfinal⟩ := hfinal
      obtain ⟨suffix, htrace, _⟩ :=
        (supported.compile.messageApplication (Value := L.Val ty)).runPolicies_native_support
          (supported.valuePlayers left focal deviator) environment rest middle final hfinal
      have hprefix : ∀ action, action ∈ middle.nativeTrace → action ∈ final.nativeTrace := by
        intro action haction
        rw [htrace]
        exact List.mem_append_left _ haction
      refine ⟨middle, ?_, ih middle hfinal⟩
      cases invocation with
      | environment => exact hmiddle
      | player owner =>
          by_cases howner : owner = focal
          · subst owner
            simpa only [MessageApplication.invoke, valuePlayers, GameTheory.Profile.update_same]
              using hmiddle
          · simp only [MessageApplication.invoke, valuePlayers,
              GameTheory.Profile.update_of_ne _ _ howner,
              FinDist.support_bind, Set.mem_iUnion] at hmiddle ⊢
            obtain ⟨command, hcommand, hstep⟩ := hmiddle
            have hright := supported.playerPolicy_valuePolicy_congr left right owner
              (initial.principalHistory owner)
              (MessageApplication.State.observe _ initial.native owner) command hcommand
              (fun node heq => by
                subst command
                exact hagrees owner node (left node) howner
                  (hprefix _ (supported.privateCommand_mem_trace owner node.val (left node)
                    initial middle hstep)))
            refine ⟨command, ?_, hstep⟩
            rw [hright, FinDist.mem_support_pure]

/-- Honest registrations in the actual native trace identify their assigned
source values, even when the deviator and environment are randomized. -/
theorem runPolicies_valuePlayers_registration (supported : SealedFragment G ty)
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
            obtain ⟨actual, hindex, hvalue⟩ :=
              supported.playerPolicy_valuePolicy_registration values actor history view
                index.val registered hcommand
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

private theorem runPolicies_pure (supported : SealedFragment G ty)
    (players : Player → (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment : (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (hplayers : ∀ who history view, ∃ command, players who history view = FinDist.pure command)
    (henvironment : ∀ history view, ∃ command, environment history view = FinDist.pure command)
    (schedule : List (@MessageApplication.Invocation Player))
    (initial : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution) :
    ∃ final, (supported.compile.messageApplication (Value := L.Val ty)).runPolicies
      players environment schedule initial = FinDist.pure final := by
  induction schedule generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons invocation rest ih =>
      have hinvoke : ∃ middle,
          (supported.compile.messageApplication (Value := L.Val ty)).invoke
            players environment initial invocation = FinDist.pure middle := by
        cases invocation with
        | player who =>
            obtain ⟨command, hcommand⟩ := hplayers who (initial.principalHistory who)
              (MessageApplication.State.observe _ initial.native who)
            simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind]
            cases command <;>
              simp only [MessageApplication.playerStep, MessageApplication.advance,
                MessageApplication.PlayerCommand.toAction, MessageApplication.step,
                FinDist.pure_bind] <;> exact ⟨_, rfl⟩
        | environment =>
            obtain ⟨command, hcommand⟩ := henvironment initial.environmentHistory
              (MessageApplication.State.environmentView _ initial.native)
            simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind]
            cases command with
            | application command => exact nomatch command.down
            | deliver observer id | «include» id | wait =>
                simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
                  MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
                  FinDist.pure_bind]
                exact ⟨_, rfl⟩
      obtain ⟨middle, hmiddle⟩ := hinvoke
      obtain ⟨final, hfinal⟩ := ih middle
      refine ⟨final, ?_⟩
      simp only [MessageApplication.runPolicies, hmiddle, FinDist.pure_bind, hfinal]

private theorem replay_exists (supported : SealedFragment G ty)
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
  apply supported.runPolicies_pure _ _ ?_ (fun _ _ => ⟨_, rfl⟩)
  intro who history view
  by_cases hwho : who = focal
  · subst who
    exact ⟨deviator history view, by
      simp only [valuePlayers, GameTheory.Profile.update_same]⟩
  · obtain ⟨command, hcommand⟩ :=
      (supported.playerPolicy who (supported.valuePolicy values who) history view).support_nonempty
    refine ⟨command, ?_⟩
    rw [valuePlayers, GameTheory.Profile.update_of_ne _ _ hwho]
    exact supported.playerPolicy_valuePolicy_congr values values who history view command hcommand
      (fun _ _ => rfl)

/-- Deterministic value substitution evaluated by the shared native runner.
This selects its unique outcome; it does not implement a second machine. -/
def replay (supported : SealedFragment G ty)
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

theorem replay_law (supported : SealedFragment G ty)
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

/-- A whole native replay depends only on honest values actually registered
in that replay. Arbitrary deterministic deviations and adaptive service
commands are preserved, with the entire final native execution record. -/
theorem replay_congr (supported : SealedFragment G ty)
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

/-- Exact cylinder characterization for the value-substituted native runner.
Equality of entire executions is equivalent to equality at the honest
registration coordinates recorded by one execution. Every invocation prefix
is an instance, by choosing that prefix as the schedule. -/
theorem replay_eq_iff (supported : SealedFragment G ty)
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

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.replay_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.replay_eq_iff
