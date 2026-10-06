/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveResponseEvaluation
import GameTheoryExtensions.Protocol.MenuRestriction

/-! # Action restrictions from nested reactive response menus

Both games use the same application, initial law, scheduler and horizon. The
smaller menu's protocol is the larger one's with fewer available responses, and
its information model is the larger one's with a smaller local menu, so the
generic menu restriction
(`GameTheory.Protocol.InformationModel.menuRestriction`) applies. Menu
inclusion embeds every legal history without changing any state, response or
observation; no execution, information or incentive premise is added.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} {app : ReactiveApplication Principal}

/-- Inclusion at every possible local input, independent of policies or reachability. -/
def IncludedIn (smaller larger : app.ResponseMenu) : Prop :=
  ∀ who past view, smaller.actions who past view ⊆ larger.actions who past view

namespace IncludedIn

variable {smaller larger : app.ResponseMenu} (included : smaller.IncludedIn larger)
  [DecidableEq Principal]
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

omit [DecidableEq Principal] in
include included in
theorem available_subset (state : app.ProtocolState) (who : Principal) :
    smaller.available state who ⊆ larger.available state who := by
  cases state with
  | none => exact subset_rfl
  | some control => exact fun _ member => included who _ _ member

include included in
theorem menu_subset (who : Principal) (info : app.Info) :
    (smaller.information initial horizon scheduler).menu who info ⊆
      (larger.information initial horizon scheduler).menu who info := by
  intro choice member
  cases info with
  | none => exact member
  | some data =>
      obtain ⟨response, permitted, same⟩ := member
      exact ⟨response, included who data.1 data.2 permitted, same⟩

/-- Nested finite menus give the structural restriction used by the general SE
theorem: the smaller game is the larger one with a restricted menu. -/
def actionRestriction :
    (smaller.information initial horizon scheduler).ActionRestriction
      (larger.information initial horizon scheduler) :=
  (larger.information initial horizon scheduler).menuRestriction
    (available := smaller.available) (included := included.available_subset)
    (progress := (smaller.protocol initial horizon scheduler).progress)
    (smaller.information initial horizon scheduler).menu
    (fun who state trace choice => by
      change choice ∈ (smaller.information initial horizon scheduler).menu who
        ((larger.signals initial horizon scheduler).infoOf who
          (restrictAvailable.trace trace)) ↔ _
      rw [larger.info]
      have adequate := (smaller.information initial horizon scheduler).menu_adequate who
        (state := state) trace choice
      change choice ∈ (smaller.information initial horizon scheduler).menu who
        ((smaller.signals initial horizon scheduler).infoOf who trace) ↔ _ at adequate
      rwa [smaller.info] at adequate)
    (included.menu_subset initial horizon scheduler)

/-- The trace embedding: the same transitions. -/
def trace {state} (original : (smaller.protocol initial horizon scheduler).Trace state) :
    (larger.protocol initial horizon scheduler).Trace state :=
  restrictAvailable.trace (E := larger.protocol initial horizon scheduler)
    (available := smaller.available) (included := included.available_subset)
    (progress := (smaller.protocol initial horizon scheduler).progress) original

/-- The history embedding: the same state and the same transitions. -/
def history (original : (smaller.protocol initial horizon scheduler).History) :
    (larger.protocol initial horizon scheduler).History :=
  (included.actionRestriction initial horizon scheduler).history original

@[simp] theorem history_state (original : (smaller.protocol initial horizon scheduler).History) :
    (included.history initial horizon scheduler original).state = original.state := rfl

/-- The choice embedding: the same physical response. -/
def choice (who : Principal) (info : app.Info)
    (original : (smaller.information initial horizon scheduler).Choice who info) :
    (larger.information initial horizon scheduler).Choice who info :=
  (included.actionRestriction initial horizon scheduler).choice who info original

/-- An additional local choice is exactly a physical response absent from the
smaller menu. The result applies to every input, not only reached histories. -/
theorem extra_choice_response (who : Principal)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (action : (larger.information initial horizon scheduler).Choice who (some (past, view)))
    (extra : action ∉ Set.range
      ((included.actionRestriction initial horizon scheduler).choice who (some (past, view)))) :
    ∃ response, action.1 = some response ∧ response ∈ larger.actions who past view ∧
      response ∉ smaller.actions who past view := by
  obtain ⟨response, allowed, same⟩ := action.2
  refine ⟨response, same, allowed, fun permitted => ?_⟩
  exact (larger.information initial horizon scheduler).menuRestriction_extra_choice _ _ _ who _
    action extra ⟨response, permitted, same⟩

/-- Extending a behavioral profile means answering with the same physical
response law at each retained decision input. -/
theorem decoded_at_site
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) (site : (smaller.information initial horizon scheduler).InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView) (observed : site.1 = some (past, view)) :
    larger.decodeProfile initial horizon scheduler target who past view =
      smaller.decodeProfile initial horizon scheduler source who past view := by
  have same := agrees who site
  change target who site.1 =
    (source who site.1).map (included.choice initial horizon scheduler who site.1) at same
  rw [observed] at same
  simp only [decodeProfile, ReactiveApplication.decodePolicy, embedPolicy, PMF.map_comp]
  rw [same, PMF.map_comp]
  rfl

end IncludedIn
end Interaction.ReactiveApplication.ResponseMenu
