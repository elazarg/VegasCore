/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedOpening
import VegasTests.SelectiveAssociationReservedContinuation

/-! # Binding correction throughout the restricted native continuation

The fresh corrective response fixes either chosen Boolean through the entire
continuation from every legal binding information site. This includes histories
created by arbitrary earlier raw submissions. Later response policies remain
unrestricted. Choosing the best Boolean requires a separate posterior argument.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def prescribedBit (who : Player) (view : app.PlayerView) : Bool :=
  if who = alice then false else publicGuess view

theorem response_binds (who : Player) (view : app.PlayerView)
    (granted : view.application.publicView.serviceGrant = some (nativeBindingEvent who)) :
    response who view = correctiveBinding who (nativeBindingEvent who) (prescribedBit who view)
      view :=
    by
  have owner : who = nativeOwner (nativeBindingEvent who) := (native_binding_owner who).symm
  have binding : (nativeBindingEvent who).val < 3 := by fin_cases who <;> decide
  simp only [response, granted, ite_eq_left owner, ite_eq_left binding, prescribedBit]

/-- One corrective response fixes the binding against every subsequent raw
policy. The hypothesis fixes just the current response law. -/
theorem binding_success (players : Profile model.behavioralSignature)
    (who : Player) (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (bit : Bool)
    (chooses : menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players
      who (control.execution.recall who) (control.execution.observe app who) =
        FinDist.pure (correctiveBinding who (nativeBindingEvent who) bit
          (control.execution.observe app who)))
    (fuel : Nat) (enough : app.rank nativeHorizon (some control) ≤ fuel)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players fuel ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ (nativeBindingRef who).get?
      result.execution.application.config.store = some (.success bit) := by
  let decoded := menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler players
  obtain ⟨next, stored, law⟩ := correctiveBinding_realizes decoded control trace who active granted
    (native_decision_unfinished (observation := leaks) (nativeBindingEvent who) control trace who
      active
      granted) bit
  refine native_reserved_finish (observation := leaks) decoded control trace (nativeBindingEvent
    who)
    (correctiveBinding who (nativeBindingEvent who) bit (control.execution.observe app who))
    (fun state => (nativeBindingRef who).get? state.config.store = some (.success bit))
    (binding_invariant who (.success bit)) (by rwa [native_binding_owner]) granted
    (by simpa only [native_binding_owner] using chooses) ?_ final.state ?_
  · intro middle reached
    rw [native_binding_owner] at reached
    have projected : middle.application ∈
        ((nativeRuntime.interactionStep leaks decoded network
          (.includeLatest (nativeBindingEvent who) who)
          (control.execution.respond app who
            (correctiveBinding who (nativeBindingEvent who) bit
              (control.execution.observe app who)))).map
                (fun result => result.application)).support :=
      FinDist.support_map .. ▸ ⟨middle, reached, rfl⟩
    rw [law, FinDist.mem_support_pure] at projected
    rw [projected]
    exact stored
  · change final.state ∈ (app.finish (FinDist.pure nativeInitial) nativeHorizon scheduler
      decoded (some control)).support
    rw [← finish_law players control trace fuel enough, FinDist.support_map]
    exact ⟨final, supported, rfl⟩

theorem profile_binding_success (who : Player) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (fuel : Nat) (enough : app.rank nativeHorizon (some control) ≤ fuel)
    (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom profile fuel ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧ (nativeBindingRef who).get?
      result.execution.application.config.store =
        some (.success (prescribedBit who (control.execution.observe app who))) := by
  apply binding_success profile who control trace active granted _ _ fuel enough final supported
  rw [decode_profile]
  exact congrArg FinDist.pure (response_binds who _ granted)

end VegasTests.SelectiveAssociation.Restricted
