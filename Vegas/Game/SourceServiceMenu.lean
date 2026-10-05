/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterPolicy
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveCompiledResolution

/-! # Deferred decision opportunities in the source service

The retained menu uses the player's turn and its own response
count to identify the last owner visit of a fixed finite roster. Before that
visit, an owned event may wait. At the last visit an unsent event must submit
an actual source decision. Once submitted, no second fresh call of the event
is permitted. Resolution has authenticated false and true decisions.

This is an information-local restriction of the unchanged bounded raw runtime.
The actual-history count lemma below identifies its last-visit test; covered
decision checkpoints make the total fallback unreachable. Source correspondence
and deadline evidence remain separate obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An unsent owned event requires a decision at its last owner visit.
Every ingredient is already present in the local input or the static roster. -/
def decisionRequired (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Prop :=
  ∃ event,
    view.application.publicView.ownTurn? who = some event ∧
    (graph setup).actor? event = some who ∧
    view.application.publicView.EventReady event ∧
    (runtime setup).eventRecorded leaks past event = false ∧
    past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who

theorem decisionRequired_iff_last
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (event : (graph setup).EventId)
    (selected : view.application.publicView.ownTurn? who = some event)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : (runtime setup).eventRecorded leaks past event = false) :
    decisionRequired setup leaks rosters who past view ↔
      past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who := by
  constructor
  · rintro ⟨chosen, chosenTurn, _, _, _, last⟩
    cases Option.some.inj (chosenTurn.symm.trans selected)
    exact last
  · intro last
    exact ⟨event, selected, owned, ready, unsent, last⟩

/-- At a real roster position, the local count test means there is no later
owner occurrence. It permits arbitrary intervening visits of other players. -/
theorem decisionRequired_iff_no_later_owner
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (event : (graph setup).EventId)
    (selected : view.application.publicView.ownTurn? who = some event)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : (runtime setup).eventRecorded leaks past event = false)
    (visited remaining : List Player) (position : rosters event = visited ++ who :: remaining)
    (counted : past.length = rosterOffset setup rosters who event + visited.count who) :
    decisionRequired setup leaks rosters who past view ↔ remaining.count who = 0 := by
  rw [decisionRequired_iff_last setup leaks rosters who past view event
    selected owned ready unsent, counted, position, List.count_append]
  simp only [List.count_cons_self]
  omega

variable [Fintype Player]

open Classical in
def sourceServiceActions (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Finset (application setup leaks).Action :=
  if decisionRequired setup leaks rosters who past view then
    bounds.requiredDecisionActions (runtime setup) leaks who past view
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
    · exact bounds.requiredDecisionActions_nonempty (runtime setup) leaks who past view
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
  · exact bounds.requiredDecisionActions_subset_compiled (runtime setup) leaks who past view
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

/-- Every covered source decision remains available at every unsent owner
visit, independently of which of those visits will be the last. -/
theorem required_decision_sourceService
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (member : response ∈ bounds.requiredDecisionActions (runtime setup) leaks who past view) :
    response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
  classical
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view
  unfold sourceServiceActions
  split
  · exact member
  · exact bounds.requiredDecisionActions_subset_compiled (runtime setup) leaks who past view member

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
    (turn : view.application.publicView.OwnTurn who event)
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
  have required := (decisionRequired_iff_last setup leaks rosters who past view event
    (view.application.publicView.ownTurn?_of_ownTurn who event turn) owned ready
    unsent).mpr last
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view at member
  rw [sourceServiceActions, ite_eq_left required] at member
  exact bounds.required_binding_cases (runtime setup) leaks covered who past view event payload
    outputEq codeEq node turn owned ready unsent serial fresh capacity response member


/-- The evidence-free false decision makes the required resolution menu
nonempty. Every last unsent resolution response therefore submits its event. -/
theorem sourceService_final_resolution_submits
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : (runtime setup).eventRecorded leaks past event = false)
    (last : past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view) :
    (runtime setup).submittedEvent? leaks response = some event := by
  classical
  let runtime := runtime setup
  let app := application setup leaks
  let decision := runtime.serviceDecision leaks who past view event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  have shape : decision = (⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ : app.Action) :=
    runtime.serviceDecision_resolution_false leaks who past view event who payload
      binding checks outputEq codeEq node
  have decisionMember : decision ∈ bounds.decisionActions runtime leaks who past view := by
    simp only [MessageBounds.decisionActions, turnSome, owned, ready, and_self, ↓reduceIte,
      node]
    exact Finset.mem_image.mpr ⟨false, Finset.mem_univ _, rfl⟩
  have first : runtime.firstSubmission leaks past decision = true := by
    rw [shape]
    change (!(Vegas.runtime setup).eventRecorded leaks past event) = true
    rw [unsent]
    rfl
  have available : decision ∈ (bounds.menu runtime leaks).actions who past view := by
    rw [shape, bounds.menu_mem]
    refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      EvidenceRequest.normalize_none]
  have nonempty : ((bounds.decisionActions runtime leaks who past view).filter
      (fun response => runtime.firstSubmission leaks past response) ∩
        (bounds.menu runtime leaks).actions who past view).Nonempty :=
    ⟨decision, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨decisionMember, first⟩, available⟩⟩
  have required := (decisionRequired_iff_last setup leaks rosters who past view event
    turnSome owned ready unsent).mpr last
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view at member
  rw [sourceServiceActions, ite_eq_left required] at member
  change response ∈ bounds.requiredDecisionActions runtime leaks who past view at member
  rw [MessageBounds.requiredDecisionActions, ite_eq_left nonempty] at member
  have chosen := (Finset.mem_filter.mp (Finset.mem_inter.mp member).1).1
  simp only [MessageBounds.decisionActions, turnSome, owned, ready, and_self, ↓reduceIte,
    node] at chosen
  obtain ⟨disclose, _, rfl⟩ := Finset.mem_image.mp chosen
  rcases runtime.serviceDecision_resolution_cases leaks who past view event who payload
    binding checks outputEq codeEq node disclose with withheld |
      ⟨candidate, value, evidence, _, _, _, opening⟩
  · rw [withheld]
    rfl
  · rw [opening]
    rfl

end Vegas
