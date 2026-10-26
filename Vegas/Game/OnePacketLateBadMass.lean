/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccessFree
import Vegas.Game.AsyncDeviationForeign

/-! # Unfailed completions without a completion point at a late binding

A stop of play until a late binding completes is *bad* when the binding has
completed without failing but the stop has no completion point
(`Vegas.lateBadStop`). After a commitment of an as-if-honest choice at a slot,
no stop is bad: the event completes at the intended target or fails. So, when
the owner plays the late owner shape, only its uniform tier makes bad stops,
and their mass is at most the cube of the scale per step of the horizon
(`Vegas.lateBinding_badMass`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

variable (setup runtime leaks bounds horizon scheduler) in
open Classical in
/-- **A bad stop.** The event has completed without failing, and the stop has no
completion point. -/
def lateBadStop (rank : Nat) (fresh : (application setup runtime leaks).Control → Prop)
    (event : (graph setup).EventId)
    (stop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) : ℝ :=
  if (∃ control, stop.state = some control ∧
      event ∈ control.execution.application.config.cut.completed ∧
      ¬ StoreEventFailed control.execution.application.config.store event) ∧
    completionPoint setup runtime leaks bounds horizon scheduler rank fresh stop = none then 1
      else 0

open Classical in
/-- **The bad mass at a late binding.** Under the hypotheses of
`Vegas.lateBinding_completionPointLaw` without value-free success, the mass of
bad stops of play until the event completes is at most the cube of the scale
per step of the horizon. -/
theorem lateBinding_badMass
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (positive : 0 < scale)
    (le_one : scale ≤ 1) {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (installed : ∀ player, (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    {event : (graph setup).EventId} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : runtime.eventRecorded leaks (execution.recall who) event = false)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {fresh : (application setup runtime leaks).Control → Prop}
    (freshIff : ∀ control, fresh control ↔
      ¬ StoreEventFailed control.execution.application.config.store event)
    (shape : LateOwnerShapeFrom setup runtime leaks bounds horizon scheduler assessment positive.le
      le_one slots installed who event execution) :
    expect ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
        scheduler).runBehavioralUntil
        ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories installed
        (LateStopped setup runtime leaks bounds horizon scheduler rank) start)
        (lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event) ≤
      scale ^ 3 * (2 * horizon + 1) := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let bad := lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event
  have badBounded : ∀ stop, |bad stop| ≤ 1 := by
    intro stop
    simp only [bad, lateBadStop]
    split <;> norm_num
  have committed : ∀ (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
      (later : Nat) (reached : (application setup runtime leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup runtime leaks who event execution.application.config (execution.recall who)
        history.state →
      (reached.recall who = execution.recall who →
        reached.observe (application setup runtime leaks) who =
          execution.observe (application setup runtime leaks) who) →
      (reached.recall who ≠ execution.recall who → ∃ response,
        execution.recall who ++ [respondEntry setup runtime leaks execution who response] <+:
          reached.recall who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup runtime leaks).outputs (reached.recall who))
          (slotEnvelope setup runtime leaks who (reached.recall who)
            (reached.observe (application setup runtime leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup runtime leaks assessment who
            (some (reached.recall who, reached.observe (application setup runtime leaks)
              who))).support,
          ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup runtime leaks) who
              (slotResponse setup runtime leaks who (reached.recall who)
                (reached.observe (application setup runtime leaks) who) event slot choice)⟩ →
            |expect (model.runBehavioralUntil certificate installed
                (LateStopped setup runtime leaks bounds horizon scheduler rank) next) bad -
              factor * (fun _ : Option (OwnAction Player L) => (0 : ℝ)) choice| ≤ 0 := by
    intro history later reached state holds _ _ slot below permitted
    have sameConfig : reached.application.config = execution.application.config := by
      have unsent := holds
      rw [state] at unsent
      exact unsent.1
    refine ⟨0, fun choice member next nextState => ?_⟩
    have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨later, some who, reached⟩) := state ▸ history.trace
    obtain ⟨readyHere, orderedHere, decodedHere, turnHere⟩ := lateUnsent_facts (runtime :=
      runtime) turn ordered
      decoded (by simpa only [state] using holds)
    obtain ⟨action, encoded, values⟩ := onePacket_honest_covered (runtime := runtime) assessment
      covers traceHere who
      event turnHere choice member
    obtain ⟨committedValue, successful, _⟩ := values who payload outputEq codeEq node
    obtain ⟨entry, message, invariant⟩ := openableCommitmentInvariant_slot (runtime := runtime)
      bounds horizon
      scheduler traceHere node readyHere slot choice action encoded successful permitted
      (nextState ▸ next.trace)
    obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (runtime := runtime)
      (failureProfile setup.program) menu horizon scheduler traceHere _ rfl
    have foundEq : found = rank := isPrefix_unique residualFound.checkpoint.ordered orderedHere
    have residual := foundEq ▸ residualFound
    cases choice with
    | none => simp at encoded
    | some source =>
    have encodedSource : encodeEventAction? setup.program event source = some action := encoded
    have decodeEq := decodeEventAction_encodeEventAction?_eq_some setup.program event source
      action encodedSource
    have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
    have pointDecoded : decodedPoint setup reached.application.config = some point :=
      (decodedPoint_eq_of_isPrefix orderedHere).trans decodedHere
    have acts : ∀ player, ProtocolView.actor player setup.program
        (ProtocolState.observe player setup.program point) = some who := fun player =>
      (decodedPoint_actor player readyHere pointDecoded).trans owned
    obtain ⟨stepTarget, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program
      point (fun _ => some source) (acts who)
    have stepEq' : ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action) = PMF.pure stepTarget := by
      rw [decodeEq]
      exact stepEq
    obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup runtime leaks
      assessment
      who reached rank orderedHere point decodedHere (reached.recall who) _).mp member
    have legal := intended.2
    change ProtocolView.intendedMenu who setup.program
      (ProtocolState.observe who setup.program point) intended.1 at legal
    rw [same] at legal
    have targetIntended : ProtocolState.Intended setup.program stepTarget := by
      refine ProtocolState.intended_step_of_actors setup.program point _ stepTarget intendedPoint
        (fun player active => ?_) (by rw [stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      cases (acts player).symm.trans active
      exact ⟨source, rfl, legal.2⟩
    have invariantNext : OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler
      who
        entry message event (who, .prepared slot) outputEq committedValue
        reached.application.config readyHere action next.state := by
      rw [nextState]
      exact invariant
    have zero : ∀ stop ∈ (model.runBehavioralUntil certificate installed
        (LateStopped setup runtime leaks bounds horizon scheduler rank) next).support, bad stop =
          0 := by
      intro stop stopMember
      obtain ⟨final, finalState, stepped⟩ := openableCommitment_stop (runtime := runtime) bounds
        horizon scheduler
        certificate installed codeEq successful residual.checkpoint.ordered
        (fun final trace ended same => terminalCompleted final trace ended
          (same.trans sameConfig)) next
        invariantNext stop stopMember
      simp only [bad, lateBadStop]
      rw [ite_eq_right_iff]
      rintro ⟨⟨control, controlState, _, notFailed⟩, pointNone⟩
      rw [finalState] at controlState
      cases Option.some.inj controlState
      rcases stepped with inStep | ⟨failing, failed, inStep⟩
      · have pointEq := completionPoint_of_mem_step (runtime := runtime) (fresh := fresh) residual
          decodedHere
          readyHere stepEq' finalState inStep
        rw [ite_eq_left ⟨targetIntended, (freshIff final).mpr notFailed⟩ ..] at pointEq
        rw [pointEq] at pointNone
        cases pointNone
      · have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) inStep
        exact (notFailed ⟨_, by rw [EventGraph.Config.store_output, output],
          (isFailure_cast_binding_iff outputEq _).mpr failed⟩).elim
    rw [expect_congr_on_support (g := fun _ => 0) zero, expect_constant]
    simp
  have main := lateBinding_exitBound (runtime := runtime) covers capacity assessment positive
    le_one slotsLe installed
    start current node turn unrecorded ordered shape bad badBounded
    (fun first second same => by
      simp only [bad, lateBadStop, completionPoint_congr_state (runtime := runtime) same, same])
    (fun stop control state atSent => by
      simp only [bad, lateBadStop]
      rw [ite_eq_right_iff]
      rintro ⟨⟨control', controlState, done, _⟩, _⟩
      rw [state] at controlState
      cases Option.some.inj controlState
      rw [atSent] at done
      have readySent : execution.application.config.cut.Ready event :=
        (execution.application.publicView_eventReady event).mp
          (PublicView.ownTurn?_spec _ who event turn).1
      exact (readySent.1 done).elim)
    (fun stop control state _ failed => by
      simp only [bad, lateBadStop]
      rw [ite_eq_right_iff]
      rintro ⟨⟨control', controlState, _, notFailed⟩, _⟩
      rw [state] at controlState
      cases Option.some.inj controlState
      exact (notFailed failed).elim)
    (fun _ => 0) (fun _ => by rw [abs_zero]; norm_num) le_rfl
    (fun _ _ _ _ _ => expect_constant _ 0) committed
  have nonneg : 0 ≤ expect (model.runBehavioralUntil certificate installed
      (LateStopped setup runtime leaks bounds horizon scheduler rank) start) bad := by
    apply expect_nonneg
    intro stop
    simp only [bad, lateBadStop]
    split <;> norm_num
  rw [abs_of_nonneg nonneg] at main
  linarith

end Vegas
