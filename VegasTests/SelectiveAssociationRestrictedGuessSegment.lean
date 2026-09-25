/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedGuessVisibility
import VegasTests.SelectiveAssociationRestrictedPrefixExecution
import VegasTests.SelectiveAssociationRestrictedOutcome

/-! # The actual continuation between Carol's and Bob's bindings

Seven protocol steps contain Carol's response and the six scheduled environment
operations before Bob responds. No player can insert another response there.
The prescribed uncertified correction leaves their public guessing input equal.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def afterCarol (execution : app.Execution) (action : app.Action) : app.Execution :=
  let submitted := execution.respond app carol action
  let included := Prefix.includeLatest submitted carolBinding carol
  let firstTick := Prefix.environmentResult included (.application .advanceClock)
  let secondTick := Prefix.environmentResult firstTick (.application .advanceClock)
  let expired := Prefix.environmentResult secondTick (.application (.expire carolBinding))
  activate (Prefix.environmentResult expired (.application (.grant bobBinding))) bob

theorem afterCarol_guess (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some carol)
    (granted : control.execution.application.serviceGrant = some carolBinding) (bit : Bool) :
    publicGuess ((afterCarol control.execution
      (correctiveBinding carol carolBinding bit (control.execution.observe app carol))).observe
        app bob) = publicGuess (control.execution.observe app carol) := by
  simp only [afterCarol, publicGuess_activate, publicGuess_environment]
  rw [corrective_inclusion_keeps_guess control trace active granted bit bob]
  exact publicGuess_congr _ _ _ _ rfl rfl

theorem afterCarol_kernel (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 9) (action : app.Action)
    (chooses : players carol (execution.recall carol) (execution.observe app carol) =
      FinDist.pure action) :
    (fun distribution => distribution.bind
      (app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players))^[7]
        (FinDist.pure (some ⟨80, some carol, execution⟩)) =
          FinDist.pure (some ⟨74, some bob, afterCarol execution action⟩) := by
  simp (disch := decide) only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, Prefix.step_player, Prefix.step_environment, chooses, FinDist.map_pure,
    scheduler, serviceScheduler, ReactiveApplication.respond_environmentRecall,
    Prefix.environmentResult_recall, cursor, List.length_append,
    List.length_singleton, Prefix.prefix_lookup, List.getElem?_cons_zero,
    List.getElem?_cons_succ, interactionInstruction, Prefix.selection_passive,
    Prefix.activation_actor, Prefix.application_actor, Prefix.environmentResult_activate]
  rfl

theorem afterCarol_history (players : Profile model.behavioralSignature)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some carol)
    (granted : control.execution.application.serviceGrant = some carolBinding)
    (action : app.Action)
    (chooses : menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players
      carol (control.execution.recall carol) (control.execution.observe app carol) =
        FinDist.pure action)
    (later : arena.History)
    (supported : later ∈ (model.runBehavioralFrom players 7 ⟨some control, trace⟩).support) :
    later.state = some ⟨74, some bob, afterCarol control.execution action⟩ := by
  have cursor := (native_decision_cursor (observation := leaks) carolBinding control trace carol
    active granted).2
  change control.execution.environmentRecall.length = 9 at cursor
  have rank := decision_rank carolBinding control trace active granted
  change 2 * control.remaining + (if control.actor.isSome then 1 else 0) = 161 at rank
  rw [active] at rank
  simp only [Option.isSome_some, ↓reduceIte] at rank
  have remaining : control.remaining = 80 := by omega
  have projection := menu.run_map_controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler
    players 7 ⟨some control, trace⟩
  have kernel := afterCarol_kernel
    (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players)
      control.execution cursor action chooses
  have kernel' : (fun distribution => distribution.bind
      (app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler
        (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players)))^[7]
        (FinDist.pure (some control)) =
          FinDist.pure (some ⟨74, some bob, afterCarol control.execution action⟩) := by
    simpa only [← remaining, ← active] using kernel
  have law : (model.runBehavioralFrom players 7 ⟨some control, trace⟩).map
      (fun history => history.state) =
        FinDist.pure (some ⟨74, some bob, afterCarol control.execution action⟩) :=
    projection.trans kernel'
  have reached : later.state ∈ ((model.runBehavioralFrom players 7
      ⟨some control, trace⟩).map (fun history => history.state)).support :=
    FinDist.support_map .. ▸ ⟨later, supported, rfl⟩
  exact FinDist.mem_support_pure.mp (law ▸ reached)

end VegasTests.SelectiveAssociation.Restricted
