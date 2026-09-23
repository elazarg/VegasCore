/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMemorySubgames

/-! # An idle private bit destroys a later canonical subgame

Alice records one Boolean and transmits nothing. Bob is then activated. His
decision is not a proper subgame root, even though the application is a unit
state and no packet or private observation has occurred.
-/

noncomputable section

namespace InteractionTests.ReactiveMemory

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

abbrev app : ReactiveApplication Bool where
  State := Unit
  Payload := Unit
  Submission := Unit
  Memory := Bool
  EnvironmentCommand := Empty
  LocalObservation := Unit
  PublicObservation := Unit
  packet _ := ()
  submit state _ _ := state
  handle state _ := some state
  environment _ command := nomatch command
  observePlayer _ _ := ()
  observePublic _ := ()
  observePending _ _ := FinDist.pure ∅

def scheduler : app.Scheduler := fun history _ =>
  FinDist.pure (.activate (history.length != 0))

abbrev arena := app.protocol (FinDist.pure ()) 2 scheduler
abbrev model := app.information (FinDist.pure ()) 2 scheduler

private def extendPure (history : arena.History) (joint : Bool → Option app.Action)
    (legal : arena.Legal history.state joint) (target : arena.State)
    (law : arena.step history.state ⟨joint, legal⟩ = FinDist.pure target) : arena.History :=
  history.extend legal (by rw [law]; exact FinDist.mem_support_pure.mpr rfl)

def initial : app.Execution := .initial app ()

def aliceExecution : app.Execution := { initial with
  environmentRecall := [⟨initial.observeEnvironment app, .activate false⟩] }

def afterAlice (bit : Bool) : app.Execution := aliceExecution.respond app false ⟨bit, none⟩

def bobExecution (bit : Bool) : app.Execution := { afterAlice bit with
  environmentRecall := (afterAlice bit).environmentRecall ++
    [⟨(afterAlice bit).observeEnvironment app, .activate true⟩] }

def setup : arena.History := extendPure arena.initHistory (fun _ => none)
  ⟨id, fun who => by change ¬ (none : Option Bool) = some who; simp⟩
  (some ⟨2, none, initial⟩) (by
    change (FinDist.pure ()).map _ = _
    rw [FinDist.map_pure]
    rfl)

def aliceHistory : arena.History := extendPure setup (fun _ => none)
  ⟨by change ¬ (2 = 0 ∧ _); simp,
    fun who => by change ¬ (none : Option Bool) = some who; simp⟩
  (some ⟨1, some false, aliceExecution⟩) (by
      change (FinDist.pure (.activate false : app.Command)).bind _ = _
      simp [ReactiveApplication.Execution.environmentStep]
      rfl)

def aliceResponse (bit : Bool) : arena.History := extendPure aliceHistory
  (fun who => if who then none else some ⟨bit, none⟩)
  ⟨by change ¬ (1 = 0 ∧ _); simp, fun who => by
    cases who
    · exact ⟨rfl, Set.mem_univ _⟩
    · change ¬ (some false : Option Bool) = some true
      decide⟩
  (some ⟨1, none, afterAlice bit⟩) rfl

def bobHistory (bit : Bool) : arena.History := extendPure (aliceResponse bit) (fun _ => none)
  ⟨by exact fun stopped => Nat.one_ne_zero stopped.1,
    fun who => by change ¬ (none : Option Bool) = some who; simp⟩
  (some ⟨0, some true, bobExecution bit⟩) (by
    change (FinDist.pure (.activate true : app.Command)).bind _ = _
    simp [ReactiveApplication.Execution.environmentStep, bobExecution]
    rfl)

theorem bob_observation_equal : app.observe true (some ⟨0, some true, bobExecution false⟩) =
    app.observe true (some ⟨0, some true, bobExecution true⟩) := rfl

theorem bob_not_proper (bit : Bool) : ¬ model.IsSubgameRoot (bobHistory bit) := by
  apply app.not_subgameRoot_of_foreign_recall (FinDist.pure ()) 2 scheduler
    (bobHistory bit) (bobHistory bit) ⟨0, some true, bobExecution bit⟩ rfl false true (by decide)
  · change [(_ : app.PlayerEntry)] ≠ []
    exact List.cons_ne_nil _ _
  · exact HistoryReaches.refl arena _
  · intro stopped
    have impossible : (some true : Option Bool) = none := stopped.2
    cases impossible
  · rfl

end InteractionTests.ReactiveMemory
