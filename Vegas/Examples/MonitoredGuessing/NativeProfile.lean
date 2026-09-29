/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResponses
import GameTheory.Core.Signature

/-! # Prescribed native play for an arbitrary source guess law -/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem native_guess_admissible (guesses : PMF Bool) :
    nativeMenu.Admissible nativeInitialLaw nativeHorizon nativeScheduler bob
      (nativeGuessPolicy guesses) := by
  intro control _ _ action supported
  obtain ⟨guess, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact native_guess_available _ _ guess

def nativeGuessBehavior (guesses : PMF Bool) : nativeModel.BehavioralPolicy bob :=
  nativeMenu.restrictPolicy nativeInitialLaw nativeHorizon nativeScheduler bob
    (nativeGuessPolicy guesses)

theorem decode_native_guess (guesses : PMF Bool) :
    nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon nativeScheduler
      bob (nativeGuessBehavior guesses)) = nativeGuessPolicy guesses := by
  apply nativeMenu.decode_restrictPolicy_of_covered
  intro past view action supported
  obtain ⟨guess, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact native_guess_available past view guess

def nativeBaseline (guesses : PMF Bool) : Profile nativeModel.behavioralSignature :=
  Fin.cases nativeAliceBehavior
    (Fin.cases (nativeGuessBehavior guesses) (Fin.cases nativeWatcherBehavior (fun i => i.elim0)))

@[simp] theorem nativeBaseline_alice (guesses : PMF Bool) :
    nativeBaseline guesses alice = nativeAliceBehavior := rfl

@[simp] theorem nativeBaseline_bob (guesses : PMF Bool) :
    nativeBaseline guesses bob = nativeGuessBehavior guesses := rfl

@[simp] theorem nativeBaseline_watcher (guesses : PMF Bool) :
    nativeBaseline guesses watcher = nativeWatcherBehavior := rfl

end Vegas.Examples.MonitoredGuessing
