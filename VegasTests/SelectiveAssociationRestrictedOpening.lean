/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedRealization
import VegasTests.SelectiveAssociationOpeningContinuation
import VegasTests.SelectiveAssociationDecisionContinuation
import VegasTests.SelectiveAssociationPublication
import VegasTests.SelectiveAssociationUnfinished
import Interaction.ReactiveInvariantContinuation

/-! # Prescribed opening in the restricted native game

These are continuation facts about the actual complete raw response menu.
Successful frozen bindings are opened by the prescribed profile at every
legal opening history, including histories outside that profile's path.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem decode_profile :
    menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler profile = policy := by
  funext who
  exact menu.decode_restrictPolicy_of_covered (FinDist.pure nativeInitial) nativeHorizon
    scheduler who (policy who) _ (policy_available who)

theorem response_opens (who : Player) (view : app.PlayerView)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who)) :
    response who view = nativeOpeningResponse (observation := leaks) who view := by
  have owner : who = nativeOwner (nativePublicationEvent who) :=
    (native_publication_owner who).symm
  have publication : ¬ (nativePublicationEvent who).val < 3 := by fin_cases who <;> decide
  simp only [response, granted, ite_eq_left owner, ite_eq_right publication]
  rfl

theorem profile_opens (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who)) :
    menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler profile who past view =
      FinDist.pure (nativeOpeningResponse (observation := leaks) who view) := by
  rw [decode_profile]
  exact congrArg FinDist.pure (response_opens who view granted)

theorem binding_invariant (who : Player) (value : PublicationResult Bool) :
    app.Invariant (fun state => (nativeBindingRef who).get? state.config.store = some value) := by
  fin_cases who
  · exact nativeRuntime.reactiveStoreInvariant leaks (.inr aliceBinding) value
  · exact nativeRuntime.reactiveStoreInvariant leaks (.inr bobBinding) value
  · exact nativeRuntime.reactiveStoreInvariant leaks (.inr carolBinding) value

theorem earlier_completed (event earlier : nativeGraph.EventId)
    (before : earlier.val < event.val) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event) :
    earlier ∈ control.execution.application.config.cut.completed := by
  have position := (native_decision_cursor (observation := leaks) event control trace _ active
    granted).2
  obtain ⟨_, prior, priorMem, activated⟩ :=
    native_decision_predecessor (observation := leaks) event control trace active position
  obtain ⟨valid, _, completed⟩ :=
    native_response_prefix_facts (observation := leaks) menu.uniformResponses event prior priorMem
  exact (nativeRuntime.reactive_environment_progress leaks nativeInputs prior
    control.execution (.activate (nativeOwner event)) valid activated).completed
      (completed earlier before)

theorem binding_present_at_opening (who owner : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some owner)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent owner)) :
    ∃ value, (nativeBindingRef who).get?
      control.execution.application.config.store = some value := by
  have before : (bindingEvent who).val < (nativePublicationEvent owner).val := by
    fin_cases who <;> fin_cases owner <;> decide
  have complete := earlier_completed (nativePublicationEvent owner) (bindingEvent who) before
    control trace (by rwa [native_publication_owner]) granted
  have field := (control.execution.application.config.output_available (bindingEvent who)).mpr
    complete
  have present := (nativeBindingRef who).get?_isSome control.execution.application.config.store
    (by rw [binding_ref_eq]; exact field)
  exact Option.isSome_iff_exists.mp present

theorem finish_law (players : Profile model.behavioralSignature)
    (control : app.Control) (trace : arena.Trace (some control)) (fuel : Nat)
    (enough : app.rank nativeHorizon (some control) ≤ fuel) :
    (model.runBehavioralFrom players fuel ⟨some control, trace⟩).map
        ExecutionProtocol.History.state =
      app.finish (FinDist.pure nativeInitial) nativeHorizon scheduler
        (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players)
          (some control) :=
  menu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon scheduler players fuel
    ⟨some control, trace⟩ enough

/-- Opening succeeds under any complete continuation profile whose current
response is prescribed. This assumption concerns one actual response law;
every later response remains unrestricted. -/
theorem opening_success (players : Profile model.behavioralSignature)
    (who : Player) (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (bit : Bool) (stored : (nativeBindingRef who).get?
      control.execution.application.config.store = some (.success bit))
    (opens : menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players
      who (control.execution.recall who) (control.execution.observe app who) =
        FinDist.pure (nativeOpeningResponse (observation := leaks) who
          (control.execution.observe app who)))
    (fuel : Nat) (enough : app.rank nativeHorizon (some control) ≤ fuel)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players fuel ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ (nativePublicationRef who).get?
      result.execution.application.config.store = some (.success bit) := by
  apply native_opening_finish (observation := leaks) _ control trace who bit active granted
    (native_decision_unfinished (observation := leaks) _ control trace who active granted)
      stored opens final.state
  change final.state ∈ (app.finish (FinDist.pure nativeInitial) nativeHorizon scheduler
    (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players)
      (some control)).support
  rw [← finish_law players control trace fuel enough, FinDist.support_map]
  exact ⟨final, supported, rfl⟩

theorem profile_opening_success (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (bit : Bool) (stored : (nativeBindingRef who).get?
      control.execution.application.config.store = some (.success bit))
    (fuel : Nat) (enough : app.rank nativeHorizon (some control) ≤ fuel)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile fuel ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ (nativePublicationRef who).get?
      result.execution.application.config.store = some (.success bit) :=
  opening_success profile who control trace active granted bit stored
    (profile_opens who _ _ granted) fuel enough final supported

def openingSteps (first last : Player) : Nat :=
  (nativeBeforeResponse (nativePublicationEvent last)).length -
    (nativeBeforeResponse (nativePublicationEvent first)).length +
      ((nativePublicationEvent last).val - (nativePublicationEvent first).val)

theorem opening_rank (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who)) :
    app.rank nativeHorizon (some control) =
      2 * (nativeHorizon - ((nativeBeforeResponse (nativePublicationEvent who)).length + 1)) + 1 :=
    by
  have position := (native_decision_cursor (observation := leaks) (nativePublicationEvent who)
    control trace who active granted).2
  have accounted := (native_decision_predecessor (observation := leaks)
    (nativePublicationEvent who) control trace (by rwa [native_publication_owner]) position).1
  change 2 * control.remaining + (if control.actor.isSome then 1 else 0) = _
  rw [active]
  simp only [Option.isSome_some, ite_true]
  omega

/-- The next opening information site is reached by the actual behavioral
execution, regardless of the intervening raw responses. -/
theorem future_opening (players : Profile model.behavioralSignature) (first last : Player)
    (ordered : (nativePublicationEvent first).val ≤ (nativePublicationEvent last).val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some first)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent first))
    (later : arena.History)
    (supported : later ∈ (model.runBehavioralFrom players (openingSteps first last)
      ⟨some control, trace⟩).support) :
    ∃ result, later.state = some result ∧ result.actor = some last ∧
      result.execution.application.serviceGrant = some (nativePublicationEvent last) := by
  have position := (native_decision_cursor (observation := leaks) (nativePublicationEvent first)
    control trace first active granted).2
  have accounted := (native_decision_predecessor (observation := leaks)
    (nativePublicationEvent first) control trace (by rwa [native_publication_owner]) position).1
  have remaining : control.remaining =
      nativeHorizon - ((nativeBeforeResponse (nativePublicationEvent first)).length + 1) := by omega
  have computed := native_behavioral_position (observation := leaks) players _
    ⟨some control, trace⟩ later supported
  change nativePosition later.state = nativeAdvancePosition^[openingSteps first last]
    (some (control.remaining, control.actor, control.execution.environmentRecall.length))
      at computed
  rw [remaining, active, position] at computed
  have advance : nativeAdvancePosition^[openingSteps first last]
      (some (nativeHorizon - ((nativeBeforeResponse (nativePublicationEvent first)).length + 1),
        some first, (nativeBeforeResponse (nativePublicationEvent first)).length + 1)) =
      some (nativeHorizon - ((nativeBeforeResponse (nativePublicationEvent last)).length + 1),
        some last, (nativeBeforeResponse (nativePublicationEvent last)).length + 1) := by
    fin_cases first <;> fin_cases last <;>
      first | decide | exact False.elim (by
        norm_num [nativePublicationEvent, alice, bob, carol] at ordered)
  rw [advance] at computed
  rcases later with ⟨state, laterTrace⟩
  cases state with
  | none => cases computed
  | some result =>
      have fields := Option.some.inj computed
      have actor := congrArg (fun value : Nat × Option Player × Nat => value.2.1) fields
      have cursor := congrArg (fun value : Nat × Option Player × Nat => value.2.2) fields
      exact ⟨result, rfl, actor, native_grant_of_decision_cursor (observation := leaks)
        (nativePublicationEvent last) result laterTrace
          (by rwa [native_publication_owner]) cursor⟩

def Opens (players : Profile model.behavioralSignature) (who : Player) : Prop :=
  ∀ past view, view.application.publicView.serviceGrant = some (nativePublicationEvent who) →
    menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players who past view =
      FinDist.pure (nativeOpeningResponse (observation := leaks) who view)

theorem profile_Opens (who : Player) : Opens profile who := profile_opens who

/-- A later owner who follows the prescribed opening publishes its frozen
successful binding, even if any other player changes its complete policy. -/
theorem future_opening_success (players : Profile model.behavioralSignature)
    (first last : Player)
    (ordered : (nativePublicationEvent first).val ≤ (nativePublicationEvent last).val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some first)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent first))
    (bit : Bool) (stored : (nativeBindingRef last).get?
      control.execution.application.config.store = some (.success bit))
    (opens : Opens players last) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ (nativePublicationRef last).get?
      result.execution.application.config.store = some (.success bit) := by
  have short : openingSteps first last ≤ 2 * nativeHorizon + 1 := by
    fin_cases first <;> fin_cases last <;> decide
  rw [← Nat.add_sub_of_le short, model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨atOpening, stateEq, ownerActive, ownerGrant⟩ :=
    future_opening players first last ordered control trace active granted later laterMem
  obtain ⟨preservedControl, preservedEq, preserved⟩ :=
    (binding_invariant last (.success bit)).behavioral_continuation menu
      (FinDist.pure nativeInitial) nativeHorizon scheduler players (openingSteps first last)
        control trace later stored laterMem
  have same : preservedControl = atOpening := Option.some.inj (preservedEq.symm.trans stateEq)
  subst preservedControl
  rcases later with ⟨laterState, laterTrace⟩
  change laterState = some atOpening at stateEq
  subst laterState
  apply opening_success players last atOpening laterTrace ownerActive ownerGrant bit preserved
    (opens _ _ ownerGrant) _ _ final finalMem
  rw [opening_rank last atOpening laterTrace ownerActive ownerGrant]
  fin_cases first <;> fin_cases last <;> decide

end VegasTests.SelectiveAssociation.Restricted
