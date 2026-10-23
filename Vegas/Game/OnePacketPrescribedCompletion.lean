/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstActivationCompletion

/-! # Trembled expectations, behavioral steps and canonical transmissions

**Trembles move an expectation by the scale.** A slot-trembled mixture whose
main law has expectation target of a function bounded by bound has
expectation within six times the scale times bound of target
(`Vegas.abs_expect_slotTrembledChoice_sub_le`).

**The behavioral step at an actor's point** draws the actor's choice and steps
with it (`Vegas.SourceProgram.ProtocolState.behavioralStateStep_eq_bind_of_actor`),
so at a turn the source step of the as-if-honest law of an intended assessment
is the step of its intended effective opening
(`Vegas.asIfHonest_bind_step_eq_behavioralStateStep`).

**Canonical decisions at a binding transmit.** Along every history of the
one-packet game, the canonical decision of every encoded source action at a
binding of the player transmits (`Vegas.canonicalTransmitsAt_of_binding`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A step at a point where owner acts reads only owner's choice. -/
theorem step_eq_of_actor (who owner : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (state : ProtocolState program) → (joint : Player → Option (OwnAction Player L)) →
    ProtocolView.actor who program (observe who program state) = some owner →
    step program state joint = step program state (fun _ => joint owner)
  | _, _, .ret _, _, _, acts => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, state, joint, acts => by
      cases state with
      | inl config =>
          change none = some owner at acts
          cases acts
      | inr rest =>
          simp only [step, Sum.elim_inr]
          rw [step_eq_of_actor who owner next rest joint acts]
  | _, _, .commit _ _ _ _ next, state, joint, acts => by
      cases state with
      | inl config =>
          change some _ = some owner at acts
          cases Option.some.inj acts
          rfl
      | inr rest =>
          simp only [step, Sum.elim_inr]
          rw [step_eq_of_actor who owner next rest joint acts]
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, acts => by
      cases state with
      | inl config =>
          change some _ = some owner at acts
          cases Option.some.inj acts
          rfl
      | inr rest =>
          simp only [step, Sum.elim_inr]
          rw [step_eq_of_actor who owner next rest joint acts]

/-- A point where some player acts is not terminal. -/
theorem not_terminal_of_actor (who owner : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (state : ProtocolState program) →
    ProtocolView.actor who program (observe who program state) = some owner →
    ¬ terminal program state
  | _, _, .ret _, _, acts => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, state, acts => by
      cases state with
      | inl config => exact id
      | inr rest => exact not_terminal_of_actor who owner next rest acts
  | _, _, .commit _ _ _ _ next, state, acts => by
      cases state with
      | inl config => exact id
      | inr rest => exact not_terminal_of_actor who owner next rest acts
  | _, _, .reveal _ _ _ _ _ _ next, state, acts => by
      cases state with
      | inl config => exact id
      | inr rest => exact not_terminal_of_actor who owner next rest acts

/-- **The behavioral step at an actor's point** draws the actor's choice and
steps with it. -/
theorem behavioralStateStep_eq_bind_of_actor [Fintype Player] {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (state : ProtocolState program) (owner : Player)
    (acts : ∀ player, ProtocolView.actor player program (observe player program state) =
      some owner) :
    behavioralStateStep program profile state =
      ((profile owner).protocolAction program (observe owner program state)).bind
        fun choice => step program state (fun _ => choice) := by
  classical
  unfold behavioralStateStep
  rw [ite_eq_right_iff.mpr fun stopped =>
    (not_terminal_of_actor owner owner program state (acts owner) stopped).elim]
  calc (independentProduct fun player => (profile player).protocolAction program
          (observe player program state)).bind (step program state)
      = (independentProduct fun player => (profile player).protocolAction program
          (observe player program state)).bind
          (fun joint => step program state (fun _ => joint owner)) := by
        congr 1
        funext joint
        exact step_eq_of_actor owner owner program state joint (acts owner)
    _ = ((independentProduct fun player => (profile player).protocolAction program
          (observe player program state)).map (fun joint => joint owner)).bind
          (fun choice => step program state (fun _ => choice)) := by
        rw [PMF.bind_map]
        rfl
    _ = _ := by rw [independentProduct_map_eval]

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A mixture of two values bounded by left and right is bounded by the
weight times left plus right. -/
private theorem abs_mix_le {weight first second left right : ℝ} (nonnegative : 0 ≤ weight)
    (le_one : weight ≤ 1) (firstBound : |first| ≤ left) (secondBound : |second| ≤ right) :
    |weight * first + (1 - weight) * second| ≤ weight * left + right := by
  have rest : 0 ≤ 1 - weight := by linarith
  have rightNonneg : 0 ≤ right := (abs_nonneg _).trans secondBound
  calc |weight * first + (1 - weight) * second|
      ≤ |weight * first| + |(1 - weight) * second| := abs_add_le _ _
    _ = weight * |first| + (1 - weight) * |second| := by
        rw [abs_mul, abs_mul, abs_of_nonneg nonnegative, abs_of_nonneg rest]
    _ ≤ weight * left + (1 - weight) * right := by
        gcongr
    _ ≤ weight * left + right := by nlinarith

/-- **Trembles move an expectation by the scale.** If the main law of a
slot-trembled mixture gives a function bounded by bound the expectation
target, with target bounded by bound, the mixture gives it an expectation
within six times the scale times bound of target. -/
theorem abs_expect_slotTrembledChoice_sub_le {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
        info))
    (value : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      info → ℝ) {target bound : ℝ} (bounded : ∀ choice, |value choice| ≤ bound)
    (targetBounded : |target| ≤ bound) (mainEq : expect main value = target) :
    |expect (slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one who info main alternative slot) value - target| ≤
      6 * scale * bound := by
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans targetBounded
  have gap : ∀ law : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who info), |expect law value - target| ≤ 2 * bound := by
    intro law
    have inside := abs_le.mp (expect_abs_le_of_bounded (μ := law) boundNonneg bounded)
    have targetInside := abs_le.mp targetBounded
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold slotTrembledChoice
  rw [expect_mix_of_finite, expect_mix_of_finite, expect_mix_of_finite, mainEq]
  have cube : scale ^ 3 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have square : scale ^ 2 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have innermost : |scale * (expect alternative value - target) +
      (1 - scale) * (target - target)| ≤ scale * (2 * bound) + 0 :=
    abs_mix_le nonnegative le_one (gap alternative) (by rw [sub_self, abs_zero])
  have middle := abs_mix_le (sq_nonneg scale) (pow_le_one₀ nonnegative le_one) (gap slot)
    innermost
  have outer := abs_mix_le (pow_nonneg nonnegative 3) (pow_le_one₀ nonnegative le_one)
    (gap ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
      scheduler who info)) middle
  have regroup : scale ^ 3 * expect ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
        (initialLaw setup) horizon scheduler who info) value +
      (1 - scale ^ 3) * (scale ^ 2 * expect slot value +
        (1 - scale ^ 2) * (scale * expect alternative value + (1 - scale) * target)) - target =
      scale ^ 3 * (expect ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
        (initialLaw setup) horizon scheduler who info) value - target) +
      (1 - scale ^ 3) * (scale ^ 2 * (expect slot value - target) +
        (1 - scale ^ 2) * (scale * (expect alternative value - target) +
          (1 - scale) * (target - target))) := by ring
  rw [regroup]
  refine outer.trans ?_
  nlinarith [mul_le_mul_of_nonneg_right cube boundNonneg,
    mul_le_mul_of_nonneg_right square boundNonneg]

/-- **The as-if-honest step is the effective opening's step.** At the player's
turn at an execution whose configuration decodes at its completed prefix to a
point of the intended game, the source step at that point of the as-if-honest
law of an intended assessment, for any recall, is the behavioral step there of
the assessment's intended effective opening. -/
theorem asIfHonest_bind_step_eq_behavioralStateStep
    (source : setup.intendedModel.BehavioralAssessment) (who : Player)
    (execution : (application setup leaks).Execution) {rank : Nat}
    (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event)
    (past : List (application setup leaks).PlayerEntry) :
    (asIfHonestProfile setup leaks source who
        (some (past, execution.observe (application setup leaks) who))).bind
        (fun choice => ProtocolState.step setup.program point (fun _ => choice)) =
      ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  have disclosing : Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.values setup.program) (setup.intendedSourceProfile source.strategy)
      who) :=
    BehavioralPolicy.disclosing_fromProtocol setup.program _ _
      (fun view => setup.intendedSourceProfile_notRefusal source.strategy who (some view))
  have actionLaw : (setup.intendedOpeningProfile source.strategy who).protocolAction
      setup.program (ProtocolState.observe who setup.program point) =
      (source.strategy who (setup.protocolObserve who (some point))).map Subtype.val := by
    change ((setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.intendedSourceProfile source.strategy) who).effectiveOpening setup.program []
        (Revelations.initial setup.context)).protocolAction setup.program _ = _
    rw [BehavioralPolicy.protocolAction_effectiveOpening setup.program _ _ _ disclosing point
      (decodedPoint_staticAt pointDecoded) intendedPoint]
    refine (BehavioralPolicy.protocolAction_fromProtocol setup.program _ _ _).trans ?_
    change ((source.strategy who (some (ProtocolState.observe who setup.program point))).map
      _).map Subtype.val = _
    rw [PMF.map_comp]
    rfl
  rw [ProtocolState.behavioralStateStep_eq_bind_of_actor setup.program _ point who acts,
    actionLaw, asIfHonestProfile_observe setup leaks source who execution rank ordered point
      decoded past]

/-- **Canonical decisions at a binding transmit.** Along every history of the
one-packet game, at a binding of who, the canonical decision of every encoded
source action transmits. -/
theorem canonicalTransmitsAt_of_binding {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    CanonicalTransmitsAt setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event := by
  intro action graphAction _ _ _
  obtain ⟨serial, selected⟩ := onePacket_canonicalFreshSlot_exists trace who
  obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
      graphAction = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
    ⟨cast (congrArg EventGraph.EventField.Action outputEq) graphAction, by simp⟩
  rw [(runtime setup).canonicalServiceDecision_binding leaks who _ _ event payload outputEq
    codeEq node serial selected choice]
  exact Option.some_ne_none _

end Vegas
