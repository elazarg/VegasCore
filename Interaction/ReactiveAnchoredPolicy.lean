/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecovery

/-! # Continuing an execution reached by other players

An execution reached by some players can be continued by others. The anchored
profile (`Interaction.ReactiveApplication.anchoredPolicy`) replays, at every
input lying on a player's recall at the anchor execution, the response that
player recorded there
(`Interaction.ReactiveApplication.anchoredPolicy_of_recorded`), and follows the
continuing profile at every other input. From the anchor on, the anchored
profile runs exactly as the continuing profile
(`Interaction.ReactiveApplication.runRounds_anchoredPolicy`).
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

open Classical in
/-- **The anchored profile.** At an input whose recall is a strict prefix of
the player's recall at `anchor`, recorded next at that input's view, respond
with the recorded response; elsewhere follow `players`. -/
def anchoredPolicy (anchor : app.Execution) (players : Principal → app.Policy) :
    Principal → app.Policy := fun who past view =>
  match (anchor.recall who)[past.length]? with
  | some entry =>
      if past ++ [entry] <+: anchor.recall who ∧ entry.beforeView = view then
        PMF.pure entry.action
      else players who past view
  | none => players who past view

omit [DecidableEq Principal] in
/-- From a recall extending the anchor's, the anchored profile follows the
continuing profile. -/
theorem anchoredPolicy_of_extends (anchor : app.Execution) (players : Principal → app.Policy)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (extends_ : anchor.recall who <+: past) :
    anchoredPolicy anchor players who past view = players who past view := by
  have none : (anchor.recall who)[past.length]? = none :=
    List.getElem?_eq_none (extends_.length_le)
  unfold anchoredPolicy
  rw [none]

omit [DecidableEq Principal] in
/-- At an input on the anchor's recall, the anchored profile replays the
recorded response. -/
theorem anchoredPolicy_of_recorded (anchor : app.Execution) (players : Principal → app.Policy)
    (who : Principal) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (recorded : past ++ [entry] <+: anchor.recall who) :
    anchoredPolicy anchor players who past entry.beforeView = PMF.pure entry.action := by
  classical
  have found : (anchor.recall who)[past.length]? = some entry := by
    obtain ⟨rest, same⟩ := recorded
    rw [← same]
    simp
  unfold anchoredPolicy
  rw [found]
  simp [recorded]

private theorem respond_recall_self (execution : app.Execution) (who : Principal)
    (action : app.Action) :
    ∃ emitted, (execution.respond app who action).recall who =
      execution.recall who ++ [⟨execution.observe app who, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission <;> simp only [Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩

/-- **From the anchor on, the anchored profile is the continuing profile.** -/
theorem runRounds_anchoredPolicy (scheduler : app.Scheduler) (anchor : app.Execution)
    (players : Principal → app.Policy) (count : Nat) :
    app.runRounds scheduler (anchoredPolicy anchor players) count anchor =
      app.runRounds scheduler players count anchor := by
  refine PolicyInvariant.runRounds_congr (predicate := fun execution =>
    ∀ who, anchor.recall who <+: execution.recall who) ⟨?_, ?_⟩ players ?_ scheduler count
    anchor fun _ => List.prefix_refl _
  · intro execution responder action valid _ who
    by_cases same : who = responder
    · subst same
      obtain ⟨emitted, recalled⟩ := respond_recall_self execution who action
      rw [recalled]
      exact (valid who).trans (List.prefix_append _ _)
    · rw [app.respond_recall_other execution responder who same action]
      exact valid who
  · intro execution next command valid moved who
    rw [app.environmentStep_recall execution next command moved]
    exact valid who
  · intro execution valid who
    exact anchoredPolicy_of_extends anchor players who _ _ (valid who)

end Interaction.ReactiveApplication
