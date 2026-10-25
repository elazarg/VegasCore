/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstActivation
import Vegas.Pending.ExclusionService
import Vegas.Pending.ReactiveFirstOpportunity

/-! # Timely first activations before actual recovery exclusion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A fresh first activation fits the protected inclusion window under the actual
recovery opportunity service, using only the public-clear native prefix. -/
theorem recovery_firstActivation_inclusionFits
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    {state : (application setup leaks).ProtocolState}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace state)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry) :
    execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  obtain ⟨previous, ⟨previousTrace⟩, applicationEq, recallEq⟩ :=
    (application setup leaks).decision_predecessor (initialLaw setup) horizon nativeScheduler
      trace current
  have spec := PublicView.ownTurn?_spec _ who event turn
  have ready := (execution.application.publicView_eventReady event).mp spec.1
  have strategic : ((graph setup).actor? event).isSome = true := by rw [spec.2]; rfl
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon nativeScheduler
    previousTrace).1
  rw [applicationEq] at invariant
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have previousClear : ExclusionEvidence 0 ∅
      (⟨previous.application, ∅⟩ : RecoveryState (graph setup)) := by
    rw [applicationEq]
    exact clear
  have actualTrace := previousTrace
  rw [← nativeLaw] at actualTrace
  have actual := Recovery.Opportunity.clear_native (runtime setup) leaks initialized opportunity
    ⟨remaining + 1, none, previous⟩ actualTrace previousClear
  have fits := inclusionFitsDeadline_of_unrecalled_turn (runtime setup) leaks (initialLaw setup)
    horizon nativeScheduler (serviceGraph_revealRelaxedOrdered setup .sequential)
    ⟨remaining + 1, none, previous⟩ previousTrace rfl delay bound timely actual event who spec.2
    (by rw [applicationEq]; exact spec.1) entered (by rw [applicationEq]; exact activated)
    (fun entry remembered => never entry (recallEq ▸ remembered))
  change previous.application.publicView.InclusionFitsDeadline (runtime setup) bound event at fits
  rwa [applicationEq] at fits

end Vegas
