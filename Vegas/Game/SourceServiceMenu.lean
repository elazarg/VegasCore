/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPolicy
import Vegas.Pending.ReactiveCompiledMenu

/-! # Deferred binding opportunities in the source service

The retained menu uses the existing public grant and the player's own response
count to identify the last owner visit of a fixed finite roster. Before that
visit, a binding may wait or replay. At the last visit an unsent binding must
submit a typed value. Once submitted, no second fresh call of the event is
permitted. Resolution keeps the ordinary guarded-opening menu.

This is an information-local restriction of the unchanged bounded raw runtime.
The actual-history count lemma below identifies its last-visit test; covered
binding checkpoints make the total fallback unreachable. Source correspondence
and deadline evidence remain separate obligations.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The only compulsory response is an unsent binding at its last owner visit.
Every ingredient is already present in the local input or the static roster. -/
def bindingRequired (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Prop :=
  ∃ event payload,
    view.application.publicView.serviceGrant = some event ∧
    (graph setup).outputLayout event = .binding who payload ∧
    (graph setup).actor? event = some who ∧
    view.application.publicView.EventReady event ∧
    (runtime setup).eventRecorded leaks past event = false ∧
    past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who

theorem bindingRequired_iff_last
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (event : (graph setup).EventId) (payload : L.Ty)
    (granted : view.application.publicView.serviceGrant = some event)
    (binding : (graph setup).outputLayout event = .binding who payload)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : (runtime setup).eventRecorded leaks past event = false) :
    bindingRequired setup leaks rosters who past view ↔
      past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who := by
  constructor
  · rintro ⟨selected, _, selectedGrant, _, _, _, _, last⟩
    cases Option.some.inj (selectedGrant.symm.trans granted)
    exact last
  · intro last
    exact ⟨event, payload, granted, binding, owned, ready, unsent, last⟩

/-- At a real roster position, the local count test means there is no later
owner occurrence. It permits arbitrary intervening visits of other players. -/
theorem bindingRequired_iff_no_later_owner
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (event : (graph setup).EventId) (payload : L.Ty)
    (granted : view.application.publicView.serviceGrant = some event)
    (binding : (graph setup).outputLayout event = .binding who payload)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : (runtime setup).eventRecorded leaks past event = false)
    (visited remaining : List Player) (position : rosters event = visited ++ who :: remaining)
    (counted : past.length = rosterOffset setup rosters who event + visited.count who) :
    bindingRequired setup leaks rosters who past view ↔ remaining.count who = 0 := by
  rw [bindingRequired_iff_last setup leaks rosters who past view event payload
    granted binding owned ready unsent, counted, position, List.count_append]
  simp only [List.count_cons_self]
  omega

variable [Fintype Player]

open Classical in
def sourceServiceActions (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Finset (application setup leaks).Action :=
  if bindingRequired setup leaks rosters who past view then
    bounds.requiredBindingActions (runtime setup) leaks who past view
  else bounds.compiledActions (runtime setup) leaks who past view

def sourceServiceMenu (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (application setup leaks).ResponseMenu where
  actions := sourceServiceActions setup leaks bounds rosters
  nonempty who past view := by
    classical
    unfold sourceServiceActions
    split
    · exact bounds.requiredBindingActions_nonempty (runtime setup) leaks who past view
    · exact bounds.compiledActions_nonempty (runtime setup) leaks who past view

theorem sourceServiceMenu_in_compiled
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (sourceServiceMenu setup leaks bounds rosters).IncludedIn
      (bounds.compiledMenu (runtime setup) leaks) := by
  classical
  intro who past view
  change sourceServiceActions setup leaks bounds rosters who past view ⊆ _
  unfold sourceServiceActions
  split
  · exact bounds.requiredBindingActions_subset_compiled (runtime setup) leaks who past view
  · exact Finset.Subset.refl _

theorem sourceServiceMenu_in_effective
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (sourceServiceMenu setup leaks bounds rosters).IncludedIn
      (bounds.menu (runtime setup) leaks) := by
  intro who past view response member
  exact bounds.compiledActions_effective (runtime setup) leaks who past view
    (sourceServiceMenu_in_compiled setup leaks bounds rosters who past view member)

theorem sourceServiceMenu_in_raw
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (sourceServiceMenu setup leaks bounds rosters).IncludedIn
      (bounds.rawMenu (runtime setup) leaks) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ := ((runtime setup).reactiveNormalization leaks).menu_mem
    (bounds.rawMenu (runtime setup) leaks) who past view response |>.mp
      (sourceServiceMenu_in_effective setup leaks bounds rosters who past view member)
  rw [← normal]
  exact bounds.rawMenu_closed (runtime setup) leaks who past view original allowed

/-- Every covered source binding value remains available at every unsent owner
visit, independently of which of those visits will be the last. -/
theorem required_binding_sourceService
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (member : response ∈ bounds.requiredBindingActions (runtime setup) leaks who past view) :
    response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
  classical
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view
  unfold sourceServiceActions
  split
  · exact member
  · exact bounds.requiredBindingActions_subset_compiled (runtime setup) leaks who past view member

/-- The total menu's fallback cannot admit silence at a real covered final
binding opportunity. Every response submits exactly one original typed value. -/
theorem sourceService_final_binding_cases
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (covered : bounds.CoversBindingValues) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : (runtime setup).eventRecorded leaks past event = false)
    (last : past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount) (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view) :
    ∃ value ∈ bounds.typedValues payload,
      response = ((runtime setup).reactiveNormalization leaks).action who past view
        ((runtime setup).reactiveBinding leaks who event payload (.success value) serial) := by
  classical
  have required := (bindingRequired_iff_last setup leaks rosters who past view event payload
    granted outputEq owned ready unsent).mpr last
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view at member
  rw [sourceServiceActions, ite_eq_left required] at member
  exact bounds.required_binding_cases (runtime setup) leaks covered who past view event payload
    outputEq codeEq node granted owned ready unsent serial fresh capacity response member

end Vegas.SourceProgram.RevealService
