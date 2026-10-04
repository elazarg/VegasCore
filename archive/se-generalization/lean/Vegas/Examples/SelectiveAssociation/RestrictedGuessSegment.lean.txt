/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.RestrictedGuessVisibility
import Vegas.Examples.SelectiveAssociation.RestrictedPrefixExecution
import Vegas.Examples.SelectiveAssociation.RestrictedOutcome

/-! # The actual continuation between Carol's and Bob's bindings

Six protocol steps contain Carol's response and the five scheduled environment
operations before Bob responds. No player can insert another response there.
The prescribed uncertified correction leaves their public guessing input equal.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def afterCarol (execution : app.Execution) (action : app.Action) : app.Execution :=
  let submitted := execution.respond app carol action
  let included := Prefix.includeLatest submitted carolBinding carol
  let firstTick := Prefix.environmentResult included (.application .advanceClock)
  let secondTick := Prefix.environmentResult firstTick (.application .advanceClock)
  let expired := Prefix.environmentResult secondTick (.application (.expire carolBinding))
  activate expired bob

theorem afterCarol_guess (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some carol)
    (turn : NativeTurn carolBinding control) (bit : Bool) :
    publicGuess ((afterCarol control.execution
      (correctiveBinding carol carolBinding bit (control.execution.observe app carol))).observe
        app bob) = publicGuess (control.execution.observe app carol) := by
  simp only [afterCarol, publicGuess_activate, publicGuess_environment]
  rw [corrective_inclusion_keeps_guess control trace active turn bit bob]
  exact publicGuess_congr _ _ _ _ rfl rfl

theorem afterCarol_kernel (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 7) (action : app.Action)
    (chooses : players carol (execution.recall carol) (execution.observe app carol) =
      PMF.pure action) :
    (fun distribution => distribution.bind
      (app.controlStep (PMF.pure nativeInitial) nativeHorizon scheduler players))^[6]
        (PMF.pure (some ⟨76, some carol, execution⟩)) =
          PMF.pure (some ⟨71, some bob, afterCarol execution action⟩) := by
  simp (disch := decide) only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, Prefix.step_player, Prefix.step_environment, chooses, PMF.pure_map,
    scheduler, serviceScheduler, ReactiveApplication.respond_environmentRecall,
    Prefix.environmentResult_recall, cursor, List.length_append,
    List.length_singleton, Prefix.prefix_lookup, List.getElem?_cons_zero,
    List.getElem?_cons_succ, interactionInstruction, Prefix.selection_passive,
    Prefix.activation_actor, Prefix.application_actor, Prefix.environmentResult_activate]
  rfl

theorem afterCarol_history (players : Profile model.behavioralSignature)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some carol)
    (turn : NativeTurn carolBinding control)
    (action : app.Action)
    (chooses : menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler players
      carol (control.execution.recall carol) (control.execution.observe app carol) =
        PMF.pure action)
    (later : arena.History)
    (supported : later ∈ (model.runBehavioralFrom players 6 ⟨some control, trace⟩).support) :
    later.state = some ⟨71, some bob, afterCarol control.execution action⟩ := by
  have cursor := (native_decision_cursor (observation := leaks) carolBinding control trace carol
    active turn).2
  change control.execution.environmentRecall.length = 7 at cursor
  have rank := decision_rank carolBinding control trace active turn
  change 2 * control.remaining + (if control.actor.isSome then 1 else 0) = 153 at rank
  rw [active] at rank
  simp only [Option.isSome_some, ↓reduceIte] at rank
  have remaining : control.remaining = 76 := by omega
  have projection := menu.run_map_controlStep (PMF.pure nativeInitial) nativeHorizon scheduler
    players 6 ⟨some control, trace⟩
  have kernel := afterCarol_kernel
    (menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler players)
      control.execution cursor action chooses
  have kernel' : (fun distribution => distribution.bind
      (app.controlStep (PMF.pure nativeInitial) nativeHorizon scheduler
        (menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler players)))^[6]
        (PMF.pure (some control)) =
          PMF.pure (some ⟨71, some bob, afterCarol control.execution action⟩) := by
    simpa only [← remaining, ← active] using kernel
  have law : (model.runBehavioralFrom players 6 ⟨some control, trace⟩).map
      (fun history => history.state) =
        PMF.pure (some ⟨71, some bob, afterCarol control.execution action⟩) :=
    projection.trans kernel'
  have reached : later.state ∈ ((model.runBehavioralFrom players 6
      ⟨some control, trace⟩).map (fun history => history.state)).support :=
    PMF.support_map .. ▸ ⟨later, supported, rfl⟩
  exact (PMF.mem_support_pure_iff _ _).mp (law ▸ reached)

end Vegas.Examples.SelectiveAssociation.Restricted
