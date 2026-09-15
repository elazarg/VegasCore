/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionCylinder
import VegasTests.PendingSource

/-! # Stopped native cylinders do not constrain later registrations

The focal player first waits, then an honest player registers its assigned
value. Stopping after the wait retains a real invocation and its local memory,
but no honest coordinate. The stopped law is a point mass under every joint
assignment distribution; the complete traces still distinguish honest values.
-/

noncomputable section

namespace VegasTests.SealedResolutionCylinder

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability PendingSource

abbrev Value := Option Bool
abbrev runtime := sealedFragment.resolvingRuntime none 3
abbrev app := runtime.messageApplication

private def initial := PolicyExecution.initial app (State.initial app runtime.initial)

private def waited : app.PolicyExecution :=
  { initial with
    principalHistory := fun who => if who = 1 then
      [⟨State.observe app initial.native 1, .wait⟩] else [] }

private def registered (values : Fin graph.nodeCount → Value) : app.PolicyExecution :=
  { waited with
    native.application.service :=
      (IdealCommitments.empty.sealValue 0 0 (values (node 0))).state
    principalHistory := fun who => if who = 0 then
      [⟨State.observe app waited.native 0, .privateCommand ⟨(0, values (node 0))⟩⟩]
      else waited.principalHistory who
    nativeTrace := [.privateCommand 0 ⟨(0, values (node 0))⟩] }

private def release (execution : app.PolicyExecution) : Bool :=
  !(execution.principalHistory 1).isEmpty

private def replay (values : Fin graph.nodeCount → Value) :=
  sealedFragment.resolvingReplay none 3 values 1 (fun _ _ => .wait) (fun _ _ => .wait)
    [.player 1, .player 0]

private theorem replay_eq (values : Fin graph.nodeCount → Value) :
    replay values = .step initial (.step waited (.finish (registered values))) := by
  have hwait : app.playerStep 1 initial .wait = FinDist.pure waited := by
    simp only [playerStep, advance, PlayerCommand.toAction, FinDist.pure_bind]
    rfl
  have hpolicy : sealedFragment.resolvingProposalPolicy none 3 0
      (sealedFragment.assignedProposals values 0)
      (waited.principalHistory 0) (State.observe app waited.native 0) =
        FinDist.pure (.privateCommand ⟨(0, values (node 0))⟩ : app.PlayerCommand) := by
    change sealedFragment.commitCommand 0 (sealedFragment.assignedProposals values 0)
      (node 0) _ rfl [] _ = _
    unfold SealedShape.commitCommand
    simp only [ChoiceEncoding.cachedValue_nil]
    exact FinDist.map_pure _ _
  have hregister : app.playerStep 0 waited (.privateCommand ⟨(0, values (node 0))⟩) =
      FinDist.pure (registered values) := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind]
    rfl
  have hlaw := sealedFragment.resolvingReplay_law none 3 values 1
    (fun _ _ => .wait) (fun _ _ => .wait) [.player 1, .player 0]
  simp only [tracePolicies, invoke, SealedShape.resolvingValuePlayers,
    GameTheory.Profile.update_same,
    GameTheory.Profile.update_of_ne _ _ (show (0 : PendingSource.Player) ≠ 1 by decide),
    FinDist.pure_bind] at hlaw
  erw [hwait] at hlaw
  simp only [FinDist.pure_bind] at hlaw
  erw [hpolicy] at hlaw
  simp only [FinDist.pure_bind] at hlaw
  erw [hregister] at hlaw
  simp only [FinDist.pure_bind, FinDist.map_pure] at hlaw
  exact FinDist.mem_support_pure.mp (hlaw ▸ FinDist.mem_support_pure.mpr rfl)

private theorem prefix_eq (values : Fin graph.nodeCount → Value) :
    (replay values).prefixThrough release = .step initial (.finish waited) := by
  rw [replay_eq]
  rfl

/-- An actual invocation prefix can ignore a value that changes the complete
native trace. The cutoff is not the empty schedule or an initially true test. -/
theorem stopped_equal_full_distinct (left right : Fin graph.nodeCount → Value)
    (hne : left (node 0) ≠ right (node 0)) :
    (replay left).prefixThrough release = (replay right).prefixThrough release ∧
      replay left ≠ replay right := by
  refine ⟨by rw [prefix_eq, prefix_eq], ?_⟩
  intro heq
  have htrace := congrArg (fun trace : app.PolicyTrace => trace.last.nativeTrace) heq
  rw [replay_eq, replay_eq] at htrace
  simp only [PolicyTrace.last, registered, List.cons.injEq,
    MessageInterface.Action.privateCommand.injEq, true_and, and_true] at htrace
  exact hne (congrArg (fun request => request.down.2) htrace)

/-- The generic cylinder theorem gives mass one without assuming that the
honest assignment coordinates are independent. -/
theorem stopped_mass (assignments : FinDist (Fin graph.nodeCount → Value))
    (reference : Fin graph.nodeCount → Value) :
    (assignments.map (fun values => (replay values).prefixThrough release)).prob
      ((replay reference).prefixThrough release) = 1 := by
  simp only [replay]
  rw [sealedFragment.resolvingReplay_cylinder_probability]
  change assignments.probOf {values | ∀ owner index value, owner ≠ (1 : PendingSource.Player) →
    (.privateCommand owner ⟨(index.val, value)⟩ : app.Action) ∈
      ((replay reference).prefixThrough release).last.nativeTrace →
        reference index = values index} = 1
  rw [prefix_eq]
  simp only [PolicyTrace.last, waited, initial, PolicyExecution.initial, List.not_mem_nil,
    false_implies, implies_true, Set.ofPred_true]
  rw [← FinDist.expect_indicator_eq_probOf]
  simp only [Set.mem_univ, ↓reduceIte, FinDist.expect_const]

private def timeoutTraffic (value : Value) : List app.Action :=
  [.privateCommand 0 ⟨(0, value)⟩, .privateCommand 0 ⟨(0, none)⟩,
    .submit 1 .malformed, .include (1, 0),
    .environment ⟨()⟩, .environment ⟨()⟩, .environment ⟨()⟩, .environment ⟨()⟩]

/-- Retrying a private registration, submitting garbage, and expiring public
nodes cannot create a private registration for the other player. The run has
nonempty support, so the test also checks a real native execution. -/
theorem timeout_does_not_fabricate_registration (value : Value) :
    ∃ final ∈ (app.run (timeoutTraffic value) (State.initial app runtime.initial)).support,
      final.application.service.lookup (1, 1) = none := by
  obtain ⟨final, hfinal⟩ :=
    (app.run (timeoutTraffic value) (State.initial app runtime.initial)).support_nonempty
  refine ⟨final, hfinal, ?_⟩
  cases hlookup : final.application.service.lookup (1, 1) with
  | none => rfl
  | some registered =>
      rcases runtime.run_lookup_origin (timeoutTraffic value) _ final hfinal
        1 1 registered hlookup with hprior | hrecorded
      · cases hprior
      · simp only [timeoutTraffic, List.mem_cons, List.not_mem_nil, or_false,
          MessageInterface.Action.privateCommand.injEq, reduceCtorEq] at hrecorded
        rcases hrecorded with ⟨howner, _⟩ | ⟨howner, _⟩ <;> cases howner

end VegasTests.SealedResolutionCylinder
