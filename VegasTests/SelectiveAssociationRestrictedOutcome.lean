/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedBinding
import VegasTests.SelectiveAssociationRestrictedOpeningOptimality

/-! # Native outcomes from earlier service decisions

The fixed calendar reaches each later information site independently of all
raw responses. Prescribed opening therefore publishes a fixed earlier binding,
and also publishes any successful binding established during the continuation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def decisionSteps (first last : nativeGraph.EventId) : Nat :=
  (nativeBeforeResponse last).length - (nativeBeforeResponse first).length + (last.val - first.val)

theorem decision_rank (event : nativeGraph.EventId) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event) :
    app.rank nativeHorizon (some control) =
      2 * (nativeHorizon - ((nativeBeforeResponse event).length + 1)) + 1 := by
  have position := (native_decision_cursor (observation := leaks) event control trace _ active
    granted).2
  have accounted := (native_decision_predecessor (observation := leaks) event control trace active
    position).1
  change 2 * control.remaining + (if control.actor.isSome then 1 else 0) = _
  rw [active]
  simp only [Option.isSome_some, ite_true]
  omega

theorem full_enough (control : app.Control) (trace : arena.Trace (some control)) :
    app.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1 := by
  have bound := app.trace_bound (FinDist.pure nativeInitial) nativeHorizon scheduler
    (menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace)
  omega

theorem full_continuation_state (players : Profile model.behavioralSignature)
    (control : app.Control) (trace : arena.Trace (some control)) (fuel : Nat)
    (enough : app.rank nativeHorizon (some control) ≤ fuel) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players fuel ⟨some control, trace⟩).support) :
    ∃ other ∈ (model.runBehavioralFrom players (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support, other.state = final.state := by
  have short := finish_law players control trace fuel enough
  have long := finish_law players control trace (2 * nativeHorizon + 1) (full_enough control trace)
  have mapped : final.state ∈ ((model.runBehavioralFrom players fuel
      ⟨some control, trace⟩).map ExecutionProtocol.History.state).support :=
    FinDist.support_map .. ▸ ⟨final, supported, rfl⟩
  rw [short, ← long, FinDist.support_map] at mapped
  exact mapped

theorem future_decision (players : Profile model.behavioralSignature)
    (first last : nativeGraph.EventId) (ordered : first.val ≤ last.val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some (nativeOwner first))
    (granted : control.execution.application.serviceGrant = some first)
    (later : arena.History)
    (supported : later ∈ (model.runBehavioralFrom players (decisionSteps first last)
      ⟨some control, trace⟩).support) :
    ∃ result, later.state = some result ∧ result.actor = some (nativeOwner last) ∧
      result.execution.application.serviceGrant = some last := by
  have position := (native_decision_cursor (observation := leaks) first control trace _ active
    granted).2
  have accounted := (native_decision_predecessor (observation := leaks) first control trace active
    position).1
  have remaining : control.remaining =
      nativeHorizon - ((nativeBeforeResponse first).length + 1) := by omega
  have computed := native_behavioral_position (observation := leaks) players _
    ⟨some control, trace⟩ later supported
  change nativePosition later.state = nativeAdvancePosition^[decisionSteps first last]
    (some (control.remaining, control.actor, control.execution.environmentRecall.length))
      at computed
  rw [remaining, active, position] at computed
  have advance : nativeAdvancePosition^[decisionSteps first last]
      (some (nativeHorizon - ((nativeBeforeResponse first).length + 1),
        some (nativeOwner first), (nativeBeforeResponse first).length + 1)) =
      some (nativeHorizon - ((nativeBeforeResponse last).length + 1),
        some (nativeOwner last), (nativeBeforeResponse last).length + 1) := by
    fin_cases first <;> fin_cases last <;>
      first | decide | exact False.elim (by norm_num at ordered)
  rw [advance] at computed
  rcases later with ⟨state, laterTrace⟩
  cases state with
  | none => cases computed
  | some result =>
      have fields := Option.some.inj computed
      have actor := congrArg (fun value : Nat × Option Player × Nat => value.2.1) fields
      have cursor := congrArg (fun value : Nat × Option Player × Nat => value.2.2) fields
      exact ⟨result, rfl, actor,
        native_grant_of_decision_cursor (observation := leaks) last result laterTrace actor cursor⟩

theorem publication_from_earlier_binding (players : Profile model.behavioralSignature)
    (event : nativeGraph.EventId) (who : Player)
    (ordered : event.val ≤ (nativePublicationEvent who).val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event)
    (value : PublicationResult Bool)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store = some value)
    (opens : Opens players who) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) : publication who final.state = value := by
  cases value with
  | failure =>
      have failed := publication_or_failure players who control trace .failure stored _ final
        supported
      exact failed.elim id id
  | success bit =>
      have short : decisionSteps event (nativePublicationEvent who) ≤ 2 * nativeHorizon + 1 := by
        fin_cases event <;> fin_cases who <;> decide
      rw [← Nat.add_sub_of_le short, model.runBehavioralFrom_add] at supported
      obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨atOpening, stateEq, ownerActive, ownerGrant⟩ := future_decision players event
        (nativePublicationEvent who) ordered control trace active granted later laterMem
      rw [native_publication_owner] at ownerActive
      obtain ⟨preservedControl, preservedEq, preserved⟩ :=
        (binding_invariant who (.success bit)).behavioral_continuation menu
          (FinDist.pure nativeInitial) nativeHorizon scheduler players
            (decisionSteps event (nativePublicationEvent who)) control trace later stored laterMem
      have same : preservedControl = atOpening := Option.some.inj
        (preservedEq.symm.trans stateEq)
      subst preservedControl
      rcases later with ⟨laterState, laterTrace⟩
      change laterState = some atOpening at stateEq
      subst laterState
      have enough : app.rank nativeHorizon (some atOpening) ≤
          2 * nativeHorizon + 1 - decisionSteps event (nativePublicationEvent who) := by
        rw [opening_rank who atOpening laterTrace ownerActive ownerGrant]
        fin_cases event <;> fin_cases who <;> decide
      obtain ⟨result, resultEq, published⟩ := opening_success players who atOpening laterTrace
        ownerActive ownerGrant bit preserved (opens _ _ ownerGrant) _ enough final finalMem
      simp only [publication, resultEq, Option.elim_some, published, Option.getD_some]

/-- A successful final binding was already fixed at its owner's opening site.
Prescribed opening therefore publishes it. The binding response before that
site is unrestricted, including malformed or replayed envelopes. -/
theorem final_binding_published (players : Profile model.behavioralSignature)
    (event : nativeGraph.EventId) (who : Player)
    (ordered : event.val ≤ (nativePublicationEvent who).val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event)
    (opens : Opens players who) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support)
    (result : app.Control) (stateEq : final.state = some result) (bit : Bool)
    (bound : (nativeBindingRef who).get? result.execution.application.config.store =
      some (.success bit)) : publication who final.state = .success bit := by
  have short : decisionSteps event (nativePublicationEvent who) ≤ 2 * nativeHorizon + 1 := by
    fin_cases event <;> fin_cases who <;> decide
  rw [← Nat.add_sub_of_le short, model.runBehavioralFrom_add] at supported
  obtain ⟨later, laterMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨atOpening, openingEq, ownerActive, ownerGrant⟩ := future_decision players event
    (nativePublicationEvent who) ordered control trace active granted later laterMem
  rw [native_publication_owner] at ownerActive
  rcases later with ⟨laterState, laterTrace⟩
  change laterState = some atOpening at openingEq
  subst laterState
  obtain ⟨value, stored⟩ := binding_present_at_opening who who atOpening laterTrace ownerActive
    ownerGrant
  obtain ⟨preservedControl, preservedEq, preserved⟩ :=
    (binding_invariant who value).behavioral_continuation menu (FinDist.pure nativeInitial)
      nativeHorizon scheduler players _ atOpening laterTrace final stored finalMem
  have same : preservedControl = result := Option.some.inj (preservedEq.symm.trans stateEq)
  subst preservedControl
  have valueEq := Option.some.inj (preserved.symm.trans bound)
  subst value
  have enough : app.rank nativeHorizon (some atOpening) ≤
      2 * nativeHorizon + 1 - decisionSteps event (nativePublicationEvent who) := by
    rw [opening_rank who atOpening laterTrace ownerActive ownerGrant]
    fin_cases event <;> fin_cases who <;> decide
  obtain ⟨opened, openedEq, published⟩ := opening_success players who atOpening laterTrace
    ownerActive ownerGrant bit stored (opens _ _ ownerGrant) _ enough final finalMem
  simp only [publication, openedEq, Option.elim_some, published, Option.getD_some]

/-- Earlier completed bindings cannot acquire their final value only later.
This is useful when a complete run is split at a later decision site. -/
theorem binding_from_final (players : Profile model.behavioralSignature)
    (event : nativeGraph.EventId) (who : Player)
    (earlier : (nativeBindingEvent who).val < event.val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event)
    (fuel : Nat) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players fuel ⟨some control, trace⟩).support)
    (result : app.Control) (stateEq : final.state = some result) (value : PublicationResult Bool)
    (bound : (nativeBindingRef who).get? result.execution.application.config.store = some value) :
    (nativeBindingRef who).get? control.execution.application.config.store = some value := by
  have complete := earlier_completed event (nativeBindingEvent who) earlier control trace active
    granted
  have field := (control.execution.application.config.output_available (nativeBindingEvent who)).mpr
    complete
  obtain ⟨original, stored⟩ := Option.isSome_iff_exists.mp
    ((nativeBindingRef who).get?_isSome control.execution.application.config.store
      (by rw [native_binding_ref_eq]; exact field))
  obtain ⟨preservedControl, preservedEq, preserved⟩ :=
    (binding_invariant who original).behavioral_continuation menu (FinDist.pure nativeInitial)
      nativeHorizon scheduler players fuel control trace final stored supported
  have same : preservedControl = result := Option.some.inj (preservedEq.symm.trans stateEq)
  subst preservedControl
  exact stored.trans (preserved.symm.trans bound)

theorem publicGuess_false_of_alice_false (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (bound : aliceBindingRef.get? control.execution.application.config.store =
      some (.success false)) : publicGuess (control.execution.observe app who) = false := by
  cases selected : publicGuess (control.execution.observe app who) with
  | false => rfl
  | true =>
      have information : model.infoOf who trace =
          some (control.execution.recall who, control.execution.observe app who) := by
        change (menu.signals (FinDist.pure nativeInitial) nativeHorizon scheduler).infoOf
          who trace = _
        rw [menu.info]
        simp only [ReactiveApplication.observe, active, ↓reduceIte]
      have known := publicGuess_true_known who _ _ selected
        ⟨⟨some control, trace⟩, information⟩
      change aliceBindingRef.get? control.execution.application.config.store = some (.success true)
        at known
      rw [bound] at known
      cases known

end VegasTests.SelectiveAssociation.Restricted
