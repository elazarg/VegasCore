/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactivePendingMenus
import Vegas.Pending.ReactiveStateInvariant

/-! # Continuation incentives in the reactive pending-menu example -/

noncomputable section

namespace VegasTests.ReactivePendingMenus

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction
open Vegas Vegas.EventGraphRuntime

def result (state : app.ProtocolState) : Option (PublicationResult Int) :=
  state.bind fun control => control.execution.application.config.outputs 1

def run (policy : app.Policy) : FinDist arena.History :=
  model.runSingleMoverBehavioralFrom (app.singleMover (FinDist.pure initialState) 7 scheduler)
    (fun _ => app.encodePolicy policy) 15 (secondHistory first second)

theorem run_state (policy : app.Policy) : (run policy).map ExecutionProtocol.History.state =
    (app.runRounds scheduler (fun _ => policy) 5 contested).map app.finished := by
  rw [run, app.run_map_state]
  change (fun law : FinDist app.ProtocolState => law.bind
    (app.controlStep (FinDist.pure initialState) 7 scheduler (fun _ => policy)))^[15]
      (FinDist.pure (some ⟨5, none, contested⟩)) = _
  simpa only [ReactiveApplication.finish, ReactiveApplication.resume, FinDist.pure_bind] using
    app.iterate_eq_finish (FinDist.pure initialState) 7 scheduler (fun _ => policy)
      15 (some ⟨5, none, contested⟩) (by change 2 * 5 + 0 ≤ 15; omega)

theorem first_round (policy : app.Policy) :
    app.round scheduler (fun _ => policy) contested =
      (policy ((activated contested).recall ()) ((activated contested).observe app ())).map
        afterAction := by
  change (FinDist.pure (.activate () : app.Command)).bind _ = _
  simp only [FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
    FinDist.map_pure, MessageNetwork.learn_empty, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.invoke]
  rfl

private theorem afterAction_environment (action : app.Action) :
    (afterAction action).environmentRecall = (activated contested).environmentRecall :=
  app.respond_environmentRecall (activated contested) () action

theorem inclusion_round (policy : app.Policy) (action : app.Action) :
    app.round scheduler (fun _ => policy) (afterAction action) =
      FinDist.pure (included action) := by
  have choice : scheduler (afterAction action).environmentRecall
      ((afterAction action).observeEnvironment app) =
        FinDist.pure (.include ((), selected action)) := by
    rw [afterAction_environment]
    rfl
  simp only [ReactiveApplication.round, choice, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem first_two_rounds (policy : app.Policy) :
    app.runRounds scheduler (fun _ => policy) 2 contested =
      (policy ((activated contested).recall ()) ((activated contested).observe app ())).map
        included := by
  rw [ReactiveApplication.runRounds, first_round, FinDist.bind_map]
  change (policy ((activated contested).recall ()) ((activated contested).observe app ())).bind
    (fun action => (app.round scheduler (fun _ => policy) (afterAction action)).bind _) = _
  simp only [inclusion_round, FinDist.pure_bind, ReactiveApplication.runRounds]
  exact (FinDist.map_eq_bind _ _).symm

private theorem contested_invariant : contested.application.Invariant input := by
  have invariant := (runtime.reactiveStateInvariant leaks input).history
    (FinDist.pure initialState) 7 scheduler (fun state supported => by
      cases FinDist.mem_support_pure.mp supported
      exact (State.initial_invariant input).copy rfl rfl rfl)
    (secondHistory first second).trace
  exact invariant

private theorem included_invariant (action : app.Action) :
    (included action).application.Invariant input :=
  (runtime.reactiveStateInvariant leaks input).includePending
    (afterAction action) ((), selected action)
    ((runtime.reactiveStateInvariant leaks input).respond
      (activated contested) () action contested_invariant)

/-- Once either old binding is included, no later raw behavior can publish
zero. This bound includes arbitrary randomized continuation policies. -/
theorem residual_utility_sum_le (policy : app.Policy) (action : app.Action) (count : Nat)
    (final : app.Execution)
    (reached : final ∈
      (app.runRounds scheduler (fun _ => policy) count (included action)).support) :
    PendingMenus.publicUtility true (final.application.config.outputs 1) +
      PendingMenus.publicUtility false (final.application.config.outputs 1) ≤ 3 := by
  have invariant := (ReactiveApplication.Invariant.policyInvariant app
    (runtime.reactiveStateInvariant leaks input) (fun _ => policy)).runRounds
      scheduler count (included action) final
      (included_invariant action) reached
  have stored := (ReactiveApplication.Invariant.policyInvariant app
    (runtime.reactiveStoreInvariant leaks (.inr 0)
      (.success (PendingMenus.selectedValue (projectedAction action))))
      (fun _ => policy)).runRounds scheduler count (included action) final
        (selected_binding action) reached
  change final.application.config.outputs 0 = _ at stored
  cases published : final.application.config.outputs 1 with
  | none => norm_num [PendingMenus.publicUtility]
  | some value =>
      cases value with
      | failure => norm_num [PendingMenus.publicUtility]
      | success value =>
          have bound := PendingMenus.publication_matches_binding _
            invariant.reachable value published
          have same := PublicationResult.success.inj (Option.some.inj (bound.symm.trans stored))
          rw [same]
          unfold PendingMenus.selectedValue
          split <;> norm_num [PendingMenus.publicUtility]

theorem native_value_sum_le (policy : app.Policy) :
    (run policy).expect (fun final => PendingMenus.publicUtility true (result final.state)) +
      (run policy).expect (fun final => PendingMenus.publicUtility false
        (result final.state)) ≤ 3 := by
  rw [← FinDist.expect_add]
  have expected := congrArg (fun law : FinDist app.ProtocolState => law.expect (fun state =>
    PendingMenus.publicUtility true (result state) + PendingMenus.publicUtility false
      (result state))) (run_state policy)
  simp only [FinDist.expect_map] at expected
  rw [expected]
  rw [show 5 = 2 + 3 from rfl, app.runRounds_add, first_two_rounds, FinDist.bind_map]
  rw [FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro action _
  apply FinDist.expect_le_of_forall
  intro final reached
  exact residual_utility_sum_le policy action 3 final reached

def preferredValue (preferOne : Bool) : Int := if preferOne then 1 else 2
def preferredSlot (preferOne : Bool) : Nat := if preferOne then 0 else 1

def opening (preferOne : Bool) : app.Action := ⟨some (.submit
  ⟨⟨.opening 1 ((), .prepared (preferredSlot preferOne))
    ⟨.int, preferredValue preferOne⟩, none⟩, .none⟩)⟩

/-- Only the public grant is inspected. Private scheduler control is absent. -/
def recovery (preferOne : Bool) : app.Policy := fun _ view => FinDist.pure
  (if view.application.publicView.serviceGrant == some 1 then opening preferOne
    else if preferOne then runtime.reactiveBinding leaks () 0 .int (.success 0) 2
    else ⟨none⟩)

def selection (preferOne : Bool) : app.Action :=
  if preferOne then runtime.reactiveBinding leaks () 0 .int (.success 0) 2 else ⟨none⟩

private theorem selected_slot (preferOne : Bool) :
    selected (selection preferOne) = preferredSlot preferOne := by cases preferOne <;> rfl

private theorem selected_pending (preferOne : Bool) :
    (afterAction (selection preferOne)).network.lookup ((), preferredSlot preferOne) =
      some ⟨((), preferredSlot preferOne),
        ⟨.commitment 0 ((), .prepared (preferredSlot preferOne)), none⟩⟩ :=
  by cases preferOne <;> rfl

private theorem binding_ready (preferOne : Bool) :
    (afterAction (selection preferOne)).application.config.cut.Ready 0 :=
  by cases preferOne <;> decide

private def boundState (preferOne : Bool) : State graph :=
  let before := (afterAction (selection preferOne)).application
  let candidate := ((), Slot.prepared (preferredSlot preferOne))
  { before.complete 0 (binding_ready preferOne) (.success (preferredValue preferOne))
      (.success (preferredValue preferOne)) with
    accepted := Function.update before.accepted (.inr 0) (some candidate)
    candidates := before.candidates.freeze candidate }

private theorem binding_handler (preferOne : Bool) :
    handle runtime (afterAction (selection preferOne)).application
      ⟨((), preferredSlot preferOne), .commitment 0 ((), .prepared (preferredSlot preferOne))⟩ =
        some (boundState preferOne) := by
  have law := handle_commitment_eq runtime (afterAction (selection preferOne)).application
    ((), preferredSlot preferOne) 0 ((), .prepared (preferredSlot preferOne)) () .int rfl rfl rfl
    (binding_ready preferOne) (by cases preferOne <;> change 0 < 2 <;> decide) rfl rfl
    (by cases preferOne <;> rfl) (by
      intro field
      cases field with
      | inl empty => exact Fin.elim0 empty
      | inr event =>
          cases preferOne <;> change (none : Option (Handle graph)) ≠ some _ <;> simp)
  have meaning : (afterAction (selection preferOne)).application.bindingResult
      ((), .prepared (preferredSlot preferOne)) .int = .success (preferredValue preferOne) :=
    by cases preferOne <;> rfl
  simpa only [meaning, boundState, cast_eq] using law

private theorem included_state (preferOne : Bool) :
    (included (selection preferOne)).application = boundState preferOne := by
  dsimp only [included, ReactiveApplication.Execution.includePending, MessageNetwork.includePending]
  rw [selected_slot, selected_pending]
  dsimp only [app, reactiveApplication]
  rw [binding_handler]
  rfl

def granted (preferOne : Bool) : app.Execution :=
  let before := included (selection preferOne)
  { before with
    application := { before.application with serviceGrant := some 1 }
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, .application (.grant 1)⟩] }

def disclosed (preferOne : Bool) : app.Execution :=
  (activated (granted preferOne)).respond app () (opening preferOne)

def finalExecution (preferOne : Bool) : app.Execution :=
  let before := disclosed preferOne
  let id := ((), if preferOne then 3 else 2)
  { before.includePending app id with environmentRecall := before.environmentRecall ++
    [⟨before.observeEnvironment app, .include id⟩] }

private theorem recovery_first_two (preferOne : Bool) :
    app.runRounds scheduler (fun _ => recovery preferOne) 2 contested =
      FinDist.pure (included (selection preferOne)) := by
  have choice : recovery preferOne ((activated contested).recall ())
      ((activated contested).observe app ()) = FinDist.pure (selection preferOne) :=
    by cases preferOne <;> rfl
  rw [first_two_rounds, choice, FinDist.map_pure]

private theorem grant_round (preferOne : Bool) :
    app.round scheduler (fun _ => recovery preferOne) (included (selection preferOne)) =
      FinDist.pure (granted preferOne) := by
  have choice : scheduler (included (selection preferOne)).environmentRecall
      ((included (selection preferOne)).observeEnvironment app) =
      FinDist.pure (.application (.grant 1)) := by cases preferOne <;> rfl
  rw [ReactiveApplication.round, choice, FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, app, reactiveApplication, environmentStep,
    FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume]
  rfl

private theorem disclosure_round (preferOne : Bool) :
    app.round scheduler (fun _ => recovery preferOne) (granted preferOne) =
      FinDist.pure (disclosed preferOne) := by
  have choice : scheduler (granted preferOne).environmentRecall
      ((granted preferOne).observeEnvironment app) = FinDist.pure (.activate ()) :=
    by cases preferOne <;> rfl
  rw [ReactiveApplication.round, choice, FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
    FinDist.map_pure, FinDist.pure_bind, MessageNetwork.learn_empty,
    ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.invoke]
  have responds : recovery preferOne ((activated (granted preferOne)).recall ())
      ((activated (granted preferOne)).observe app ()) = FinDist.pure (opening preferOne) :=
    by cases preferOne <;> rfl
  change (recovery preferOne ((activated (granted preferOne)).recall ())
    ((activated (granted preferOne)).observe app ())).map _ = _
  rw [responds]
  rw [FinDist.map_pure]
  rfl

private theorem publication_round (preferOne : Bool) :
    app.round scheduler (fun _ => recovery preferOne) (disclosed preferOne) =
      FinDist.pure (finalExecution preferOne) := by
  have choice : scheduler (disclosed preferOne).environmentRecall
      ((disclosed preferOne).observeEnvironment app) =
        FinDist.pure (.include ((), if preferOne then 3 else 2)) :=
    by cases preferOne <;> rfl
  simp only [ReactiveApplication.round, choice, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem recovery_rounds (preferOne : Bool) :
    app.runRounds scheduler (fun _ => recovery preferOne) 5 contested =
      FinDist.pure (finalExecution preferOne) := by
  rw [show 5 = 2 + 3 from rfl, app.runRounds_add, recovery_first_two, FinDist.pure_bind]
  simp only [ReactiveApplication.runRounds, grant_round, disclosure_round, publication_round,
    FinDist.pure_bind]

private theorem disclosed_state (preferOne : Bool) :
    (disclosed preferOne).application = { boundState preferOne with serviceGrant := some 1 } := by
  change { (included (selection preferOne)).application with serviceGrant := some 1 } = _
  rw [included_state]

theorem recovery_publication (preferOne : Bool) :
    (finalExecution preferOne).application.config.outputs 1 =
      some (.success (preferredValue preferOne)) := by
  have ready : (disclosed preferOne).application.config.cut.Ready 1 := by
    rw [disclosed_state]
    cases preferOne <;> decide
  have timely : (disclosed preferOne).application.WithinDeadline runtime 1 := by
    rw [disclosed_state]
    cases preferOne <;> change 0 < 2 <;> decide
  have associated : (disclosed preferOne).application.accepted PendingMenus.binding.field =
      some ((), .prepared (preferredSlot preferOne)) := by
    rw [disclosed_state]
    simp only [boundState, Function.update_self]
  have meaning : (disclosed preferOne).application.candidates.lookup
      ((), .prepared (preferredSlot preferOne)) = .openable ⟨.int, preferredValue preferOne⟩ := by
    rw [disclosed_state]
    cases preferOne <;> rfl
  have stored : PendingMenus.binding.get? (disclosed preferOne).application.config.store =
      some (.success (preferredValue preferOne)) := by
    rw [disclosed_state]
    exact EventGraph.Config.complete_output_same ..
  have resolved : EventGraph.EventCode.resolveOutput? PendingMenus.binding [] true
      (disclosed preferOne).application.config.store =
        some (.success (preferredValue preferOne)) := by
    simp [EventGraph.EventCode.resolveOutput?, stored, EventGraph.GuardCheck.allAccepted?]
  have accepted := handle_opening_eq runtime (disclosed preferOne).application
    ((), if preferOne then 3 else 2) 1 ((), .prepared (preferredSlot preferOne)) () .int
    PendingMenus.binding [] rfl rfl rfl ready timely rfl rfl associated
    (preferredValue preferOne) meaning stored (.success (preferredValue preferOne)) resolved
  have pending : (disclosed preferOne).network.lookup ((), if preferOne then 3 else 2) =
      some ⟨((), if preferOne then 3 else 2),
        ⟨.opening 1 ((), .prepared (preferredSlot preferOne))
          ⟨.int, preferredValue preferOne⟩, none⟩⟩ :=
    by cases preferOne <;> rfl
  dsimp only [finalExecution, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending]
  rw [pending]
  dsimp only [app, reactiveApplication]
  rw [accepted]
  exact EventGraph.Config.complete_output_same ..

/-- Each preference has an information-local deviation attaining value two. -/
theorem recovery_value (preferOne : Bool) :
    (run (recovery preferOne)).expect (fun final => PendingMenus.publicUtility preferOne
      (result final.state)) = 2 := by
  have expected := congrArg (fun law : FinDist app.ProtocolState => law.expect
    (fun state => PendingMenus.publicUtility preferOne (result state)))
    (run_state (recovery preferOne))
  simp only [FinDist.expect_map] at expected
  rw [expected, recovery_rounds, FinDist.expect_pure]
  change PendingMenus.publicUtility preferOne
    ((finalExecution preferOne).application.config.outputs 1) = 2
  rw [recovery_publication]
  cases preferOne <;> norm_num [preferredValue, PendingMenus.publicUtility]

def payoff (preferOne : Bool) (final : arena.History) (_who : Unit) : ℝ :=
  PendingMenus.publicUtility preferOne (result final.state)

/-- No behavioral profile is an SPE for both public utilities, even though
the source has a common SPE. This quantifies over all native policies. -/
theorem no_common_spe :
    ¬ ∃ profile : Profile model.behavioralSignature,
      model.IsBehavioralSubgamePerfect (app.singleMover (FinDist.pure initialState) 7 scheduler)
        (app.bounded (FinDist.pure initialState) 7 scheduler) profile (payoff true) ∧
      model.IsBehavioralSubgamePerfect (app.singleMover (FinDist.pure initialState) 7 scheduler)
        (app.bounded (FinDist.pure initialState) 7 scheduler) profile (payoff false) := by
  rintro ⟨profile, one, two⟩
  let policy := app.decodePolicy (profile ())
  have profileEq : profile = fun _ => app.encodePolicy policy := by
    funext who
    cases who
    exact (app.encode_decodePolicy (profile ())).symm
  have deviation (preferOne : Bool) :
      Profile.update profile () (app.encodePolicy (recovery preferOne)) =
        fun _ => app.encodePolicy (recovery preferOne) := by
    funext who
    cases who
    simp [Profile.update]
  rw [InformationModel.isBehavioralSubgamePerfect_iff] at one two
  have left := one (secondHistory first second) contested_isSubgameRoot ()
    (app.encodePolicy (recovery true))
  have right := two (secondHistory first second) contested_isSubgameRoot ()
    (app.encodePolicy (recovery false))
  rw [deviation, profileEq] at left right
  change (run (recovery true)).expect (fun final => PendingMenus.publicUtility true
    (result final.state)) ≤ (run policy).expect
      (fun final => PendingMenus.publicUtility true (result final.state)) at left
  change (run (recovery false)).expect (fun final => PendingMenus.publicUtility false
    (result final.state)) ≤ (run policy).expect
      (fun final => PendingMenus.publicUtility false (result final.state)) at right
  rw [recovery_value] at left right
  linarith [native_value_sum_le policy]

end VegasTests.ReactivePendingMenus
