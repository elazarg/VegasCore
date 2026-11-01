/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCompletionLaw

/-! # Value-free success after a late commitment

**Completion mass is the success probability.** After a commitment of a binding
to an openable value whose source action reaches an intended point, the mass of
stops with a completion point is one less the probability that terminal play
fails the event (`Vegas.expect_completionIndicator_of_openableCommitment`): the
event completes by the committed action, at a fresh intended point, or by a
failure, and either outcome stays on the store.
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

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem cast_option_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

variable (setup runtime leaks) in
/-- The event has completed with a failure. -/
def EventFailedState (event : (graph setup).EventId) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control => event ∈ control.execution.application.config.cut.completed ∧
      StoreEventFailed control.execution.application.config.store event

open Classical in
/-- At a stop one step of the event from `sent` by the committed action, the
completion point is the target when it is intended and the control fresh. -/
theorem completionPoint_of_mem_step {rank : Nat} {profile : BehavioralProfile setup.program}
    {sent : (graph setup).Config} (residual : SourceResidual setup profile rank sent)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    {event : (graph setup).EventId} (ready : sent.cut.Ready event)
    {action : (graph setup).Action event} {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    {fresh : (application setup runtime leaks).Control → Prop}
    {stop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History} {final : (application setup runtime leaks).Control}
    (state : stop.state = some final)
    (inStep : final.execution.application.config ∈ (sent.step event ready action).support) :
    completionPoint setup runtime leaks bounds horizon scheduler rank fresh stop =
      if ProtocolState.Intended setup.program target ∧ fresh final then some target
      else none := by
  have ordered := residual.checkpoint.ordered
  obtain ⟨before, after, beforeDecoded, afterDecoded, reachedPoint⟩ :=
    decodedPoint_step residual event ready action _ inStep
  rw [decodedPoint_eq_of_isPrefix ordered, decoded] at beforeDecoded
  cases Option.some.inj beforeDecoded
  rw [stepEq, PMF.mem_support_pure_iff] at reachedPoint
  subst reachedPoint
  have stopped : LateStopped setup runtime leaks bounds horizon scheduler rank stop := by
    refine ⟨final, state, event, ?_, (ready_iff_rank setup sent rank ordered event).mp ready⟩
    rw [sent.step_cut event ready action _ inStep, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  unfold completionPoint
  rw [state]
  dsimp only
  rw [ite_eq_left stopped .., afterDecoded]

omit [Fintype Player] in
/-- A primitive source step to an intended target has no public default. -/
theorem defaulted_eq_empty_of_intended_source_step {rank : Nat}
    {profile : BehavioralProfile setup.program} {sent : (graph setup).Config}
    (residual : SourceResidual setup profile rank sent)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    {event : (graph setup).EventId} (ready : sent.cut.Ready event)
    {action : (graph setup).Action event} {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    (intended : ProtocolState.Intended setup.program target)
    (primary : EventGraphRuntime.State (graph setup))
    (member : primary.config ∈ (sent.step event ready action).support) :
    primary.config.defaulted = ∅ := by
  obtain ⟨before, after, beforeDecoded, afterDecoded, reachedPoint⟩ :=
    decodedPoint_step residual event ready action _ member
  rw [decodedPoint_eq_of_isPrefix residual.checkpoint.ordered, decoded] at beforeDecoded
  cases Option.some.inj beforeDecoded
  rw [stepEq, PMF.mem_support_pure_iff] at reachedPoint
  subst reachedPoint
  exact defaulted_eq_empty_of_decodedIntended afterDecoded intended

open Classical in
/-- **Completion mass is the success probability.** Under a scheduler completing
play, from a history at which the openable-commitment invariant holds for the
binding of rank `rank`, whose configuration `sent` has a source residual and
decodes at `rank` to a point at which the committed action's source action
reaches the intended point `target`, the completion mass under play until the
event completes is one less the probability that terminal play from the
history fails the event, for every property `fresh` of controls that holds
exactly when the event has not failed. -/
theorem expect_completionIndicator_of_openableCommitment
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Option (PublicationResult (L.Val payload))) = some (.success value))
    {rank : Nat} {profile : BehavioralProfile setup.program}
    (residual : SourceResidual setup profile rank sent) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    (targetIntended : ProtocolState.Intended setup.program target)
    {fresh : (application setup runtime leaks).Control → Prop}
    (freshIff : ∀ control, fresh control ↔
      ¬ StoreEventFailed control.execution.application.config.store event)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry
      message
      event candidate outputEq value sent ready action start.state) :
    expect (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil
        ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories players
        (LateStopped setup runtime leaks bounds horizon scheduler rank) start)
        (completionIndicator setup runtime leaks bounds horizon scheduler rank fresh) =
      1 - expect (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralFrom players (2 * horizon + 1) start)
        (fun final => if EventFailedState setup runtime leaks event final.state then 1 else 0) := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let stopped := LateStopped setup runtime leaks bounds horizon scheduler rank
  let failure := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if EventFailedState setup runtime leaks event final.state then (1 : ℝ) else 0
  have failureBounded : ∀ final, |failure final| ≤ 1 := by
    intro final
    simp only [failure]
    split <;> norm_num
  have ordered := residual.checkpoint.ordered
  -- The event's output stays on the store along terminal play.
  have kept : ∀ stop : (menu.protocol (initialLaw setup) horizon scheduler).History,
      ∀ control, stop.state = some control →
      ∀ final ∈ (model.runBehavioralTerminalFrom certificate players stop).support,
        ∃ finalControl, final.state = some finalControl ∧
          ∀ stored, control.execution.application.config.store (.inr event) = some stored →
            finalControl.execution.application.config.store (.inr event) = some stored := by
    intro stop control state
    exact model.runBehavioralTerminalFrom_support_closed certificate players
      (fun reachedState => ∃ reachedControl, reachedState = some reachedControl ∧
        ∀ stored, control.execution.application.config.store (.inr event) = some stored →
          reachedControl.execution.application.config.store (.inr event) = some stored)
      (fun state joint legal target holds reached => by
        obtain ⟨reachedControl, rfl, keeps⟩ := holds
        obtain ⟨next, rfl, _⟩ := (application setup runtime leaks).transition_recall_prefix
          (initialLaw setup) horizon scheduler reachedControl target joint reached
        have keptStore := (keepsStore_step runtime leaks).transition
          (initialLaw setup) horizon scheduler reachedControl next joint reached
        exact ⟨next, rfl, fun stored storedEq =>
          keptStore (.inr event) stored (keeps stored storedEq)⟩)
      stop ⟨control, state, fun _ storedEq => storedEq⟩
  -- At each stop the completion mass is one exactly when terminal play does not fail.
  have pointwise : ∀ stop ∈ (model.runBehavioralUntil certificate players stopped start).support,
      completionIndicator setup runtime leaks bounds horizon scheduler rank fresh stop =
        1 - expect (model.runBehavioralTerminalFrom certificate players stop) failure := by
    intro stop member
    obtain ⟨final, finalState, stepped⟩ := openableCommitment_stop (runtime := runtime) bounds
      horizon scheduler
      certificate players codeEq successful ordered terminalCompleted start holds stop member
    rcases stepped with storeFailed | ⟨primary, primaryStep, drained⟩
    · have pointNone := completionPoint_eq_none_of_not_fresh (runtime := runtime) (rank := rank)
        (fresh := fresh) finalState (fun freshHere => (freshIff final).mp freshHere storeFailed)
      have always : expect (model.runBehavioralTerminalFrom certificate players stop) failure =
          1 := by
        rw [expect_congr_on_support (g := fun _ => 1) (fun later laterMember => ?_),
          expect_constant]
        obtain ⟨laterControl, laterState, keeps⟩ := kept stop final finalState later laterMember
        obtain ⟨stored, storedEq, isFailed⟩ := storeFailed
        have laterStored := keeps stored storedEq
        have done : event ∈ laterControl.execution.application.config.cut.completed :=
          (laterControl.execution.application.config.output_available event).mp
            (by rw [← EventGraph.Config.store_output, laterStored]; rfl)
        simp only [failure, laterState, EventFailedState]
        rw [ite_eq_left_iff.mpr fun notFailed =>
          (notFailed ⟨done, stored, laterStored, isFailed⟩).elim]
      simp only [completionIndicator, pointNone, Option.elim_none, always, sub_self]
    · have clear := defaulted_eq_empty_of_intended_source_step residual decoded ready stepEq
        targetIntended primary primaryStep
      have same : final.execution.application.config = primary.config := by
        rw [drained, primary.drain_eq_of_empty clear]
      have inStep : final.execution.application.config ∈ (sent.step event ready action).support :=
        same.symm ▸ primaryStep
      have active : who ∉ sent.defaulted := by
        intro present
        have there := (sent.defaulted_step event ready action primary.config primaryStep) present
        simp only [clear, Finset.notMem_empty] at there
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (some (PublicationResult.success value)) := by
        rw [← successful]
        simp only [cast_cast, cast_eq]
      have law := commit_step sent event ready outputEq codeEq (some (.success value))
      rw [← actionEq] at law
      simp only [active, ite_false, Option.getD_some] at law
      have endpoint := (PMF.mem_support_pure_iff _ _).mp (law ▸ inStep)
      have output : final.execution.application.config.store (.inr event) = some
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value)) := by
        rw [endpoint]
        exact Function.update_self ..
      have read : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.binding who payload)).get? final.execution.application.config.store =
          some (.success value) := by
        simp only [EventGraph.FieldRef.get?]
        rw [output, cast_option_some (congrArg EventGraph.EventField.Value outputEq)]
        simp only [cast_cast, cast_eq]
      have succeeded := outputSucceeded_of_ref _ event ⟨.inr event, outputEq⟩ rfl read
        (by intro impossible; cases impossible)
      have notFailed := not_storeEventFailed_of_outputSucceeded succeeded
      have pointEq := completionPoint_of_mem_step (runtime := runtime) (fresh := fresh) residual
        decoded ready stepEq finalState inStep
      rw [ite_eq_left ⟨targetIntended, (freshIff final).mpr notFailed⟩ ..] at pointEq
      have never : expect (model.runBehavioralTerminalFrom certificate players stop) failure =
          0 := by
        rw [expect_congr_on_support (g := fun _ => 0) (fun later laterMember => ?_),
          expect_constant]
        obtain ⟨laterControl, laterState, keeps⟩ := kept stop final finalState later laterMember
        simp only [failure, laterState, EventFailedState]
        rw [ite_eq_right_iff]
        rintro ⟨_, stored, storedEq, isFailed⟩
        obtain ⟨actual, actualStored, notFail⟩ := succeeded
        rw [keeps actual actualStored] at storedEq
        cases Option.some.inj storedEq
        exact (notFail isFailed).elim
      simp only [completionIndicator, pointEq, Option.elim_some, never, sub_zero]
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate horizonBound
      players start,
    model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players stopped start,
    expect_bind_tower_bounded _ _ _ failureBounded,
    expect_congr_on_support pointwise]
  have terminalIntegrable : PayoffIntegrable (model.runBehavioralUntil certificate players
      stopped start) (fun stop => expect (model.runBehavioralTerminalFrom certificate players
        stop) failure) :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun stop =>
      expect_abs_le_of_bounded zero_le_one failureBounded
  rw [expect_sub (payoffIntegrable_constant _ 1) terminalIntegrable, expect_constant]

end Vegas
