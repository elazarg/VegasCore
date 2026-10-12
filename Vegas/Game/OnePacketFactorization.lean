/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPendingPool
import Vegas.Game.OnePacketTrembles

/-! # The operational factorization of one-packet reach: statement

This module states, without proving it, how the reach of a forced one-packet
history should factor along a tremble sequence, together with its corollary for
late delivery.

**Keyed components.** A keyed component is a trembled choice whose main law
sends the as-if-honest response with a weight read from the late-delivery key,
and keeps silence otherwise, while its timing deviation uses the opposite
weight (`Vegas.keyedComponent`). The prescribed component is the keyed
component of weight one (`Vegas.prescribedComponent_eq_keyed`), and the
waiting component is the one of weight zero (`Vegas.waitComponent_eq_keyed`). A
keyed-component profile plays a keyed component at every forced agent, with the
weight a function of the agent's late-delivery key, and a fully supported law
everywhere (`Vegas.KeyedComponentProfile`). The silent component is not keyed:
it sends the as-if-honest response only through the uniform tremble.

**Three factors of a history.** The *source weight* of a native history for an
observer `who` multiplies Nature's initial draw, the chance mass of every
completed event, and, at every transmission of another player, the mass that
the as-if-honest response gives the transmitted action
(`Vegas.othersSourceWeight`). It is taken when the action is transmitted, not
when its event completes: a pending commitment already carries the law of its
hidden value. The *operational record* lists, along the history, the
scheduler's recall and view, the leaked packets, the control position, and the
value an opening at each player's turn would deliver
(`Vegas.operationalRecord`). The *owner record* is the observer's own recall
(`Vegas.ownerRecall`).

**The factorization.** At every forced history of `who` whose source weight is
positive, meaning that every other player's transmission is its as-if-honest
response, the reach under the `n`-th profile equals the source weight times a
function of the operational record times a function of the owner record, up to
a relative error that vanishes uniformly
(`Vegas.OnePacketReachFactorization`). The claim is that every sequence of
keyed-component profiles on the tremble scale of an intended assessment
sequence factors this way (`Vegas.OnePacketFactorizationClaim`).

The relative error absorbs the uniform tremble's mass on the as-if-honest
action, which is at most the square of the scale divided by the menu size. That
mass depends on the private menu, so no exact product holds, and the
factorization is consumed in the approximate form of
`GameTheory.Math.Probability.NearProductWeights`, whose `regular_close` field is
this inequality. `GameTheory.Protocol.InformationModel.FactoredHistoryLikelihood`
needs an exact identity, which fails here.

**Late delivery.** From a late decision of an event's actor, success means that
an accepted packet of the actor completes the event. When the actor follows a
send rule keyed by its late-delivery key and the others follow the `n`-th
profile, the success probability should be the same at any two forced histories
with the same operational record (`Vegas.LateDeliveryClaim`). Pathwise, the
late-delivery key alone does not determine it, because a scheduler may recall
commands that the actor never observed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Keyed

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- Send the as-if-honest response with probability `weight`, and keep silence
otherwise. -/
def sendLaw (assessment : setup.intendedModel.BehavioralAssessment) (weight : unitInterval)
    (who : Player) (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  mix weight weight.2.1 weight.2.2
    (honestChoice setup leaks bounds initial horizon scheduler assessment who info)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))

/-- **A keyed component.** A trembled choice whose main law sends the
as-if-honest response with probability `send`, and whose timing deviation sends
it with the opposite probability. -/
def keyedComponent (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (send : unitInterval) (who : Player)
    (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (sendLaw setup leaks bounds initial horizon scheduler assessment send who info)
    (sendLaw setup leaks bounds initial horizon scheduler assessment (unitInterval.symm send)
      who info)

/-- The prescribed component is the keyed component that sends. -/
theorem prescribedComponent_eq_keyed (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) :
    prescribedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one who info =
      keyedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one 1 who info := by
  unfold prescribedComponent keyedComponent sendLaw
  rw [unitInterval.symm_one]
  exact congrArg₂ _ (mix_one _ _).symm (mix_zero _ _).symm

/-- The waiting component is the keyed component that keeps silence. -/
theorem waitComponent_eq_keyed (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) :
    waitComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one who info =
      keyedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one 0 who info := by
  unfold waitComponent keyedComponent sendLaw
  rw [unitInterval.symm_zero]
  exact congrArg₂ _ (mix_zero _ _).symm (mix_one _ _).symm

/-- **A keyed-component profile.** At every forced agent the policy is the
keyed component whose send weight the timing rule reads from the agent's
late-delivery key; every policy is fully supported. -/
def KeyedComponentProfile (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (timing : LateKey setup leaks → unitInterval)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who) :
    Prop :=
  (∀ who info, forcedAgent (bounds.onePacketMenu (runtime setup) leaks) initial horizon
      scheduler who info → ∀ key, lateKey setup leaks who info = some key →
        profile who info = keyedComponent setup leaks bounds initial horizon scheduler
          assessment scale nonnegative le_one (timing key) who info) ∧
    ∀ who info, FullSupport (profile who info)

end Keyed

section Records

/-- The operational part of a native protocol state: the control position, the
scheduler's recall and view (with the pending payloads), every player's leaked
packets, and the value an opening at each player's turn would deliver. -/
structure OperationalState where
  /-- Scheduler rounds left. -/
  remaining : Nat
  /-- The player being activated, if any. -/
  actor : Option Player
  /-- The scheduler's command recall. -/
  environmentRecall : List (application setup leaks).EnvironmentEntry
  /-- The scheduler's view: public network state, public contract view, receipts. -/
  environment : (application setup leaks).EnvironmentView
  /-- The pending packets leaked to each player. -/
  leaked : Player → List (Message Player (application setup leaks).Payload)
  /-- At each player's reveal turn, the value its opening delivers. -/
  delivered : Player → Option (Σ kind : EventGraph.EventField Player L, Option kind.Value)

/-- The operational part of a native protocol state. -/
def operationalState : (application setup leaks).ProtocolState →
    Option (OperationalState setup leaks)
  | none => none
  | some control => some
      { remaining := control.remaining
        actor := control.actor
        environmentRecall := control.execution.environmentRecall
        environment := control.execution.observeEnvironment (application setup leaks)
        leaked := control.execution.network.leaked
        delivered := fun who => deliveredValue setup leaks who
          (control.execution.observe (application setup leaks) who) }

/-- The observer's own recall at a native protocol state. -/
def ownerRecall (who : Player) :
    (application setup leaks).ProtocolState → List (application setup leaks).PlayerEntry
  | none => []
  | some control => control.execution.recall who

/-- The chance mass of the event a configuration step completes: the mass the
graph step gives the reached configuration, which is one at a decision and the
draw's probability at a sample. It is one when no event completes. -/
def completionMass (before after : EventGraphRuntime.State (graph setup)) : ℝ :=
  match after.config.history.drop before.config.history.length with
  | [⟨event, action⟩] =>
      if ready : before.config.cut.Ready event then
        (before.config.step event ready action after.config).toReal
      else 0
  | _ => 1

/-- The source factor of one native transition for an observer `who`:
Nature's initial draw; at another player's transmission, the mass of the
transmitted action under its as-if-honest response; at a scheduler round, the
chance mass of the completed event. -/
def transitionSourceFactor (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) : (application setup leaks).ProtocolState →
      (Player → Option (application setup leaks).Action) →
        (application setup leaks).ProtocolState → ℝ
  | none, _, some after => (initialLaw setup after.execution.application).toReal
  | some before, joint, some after =>
      match before.actor with
      | some actor =>
          if actor = who then 1 else
            match ((joint actor).getD ⟨none⟩).transmission with
            | none => 1
            | some _ => (honestResponse setup leaks assessment actor
                (before.execution.recall actor)
                (before.execution.observe (application setup leaks) actor)
                ((joint actor).getD ⟨none⟩)).toReal
      | none => completionMass setup before.execution.application after.execution.application
  | _, _, _ => 1

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- The native protocol of the one-packet game from the default initial law. -/
abbrev onePacketProtocol :=
  (bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon scheduler

/-- **The source weight.** The product, along a native history, of the source
factors of its transitions for the observer `who`. -/
def othersSourceWeight (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → ℝ
  | _, .start => 1
  | _, .extend (source := before) (target := after) prior joint _ _ =>
      othersSourceWeight assessment who prior *
        transitionSourceFactor setup leaks assessment who before joint after

/-- **The operational record.** The operational states along a native
history. -/
def operationalRecord :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state →
      List (Option (OperationalState setup leaks))
  | _, .start => [operationalState setup leaks none]
  | _, .extend (target := after) prior _ _ _ =>
      operationalRecord prior ++ [operationalState setup leaks after]

end Records

section Claims

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **The operational factorization of reach.** At every forced history of
`who` whose source weight under the `n`-th assessment is positive, the reach
under the `n`-th profile is the source weight, times a function of the
operational record, times a function of `who`'s own recall, up to a relative
error that vanishes uniformly in the history. -/
def OnePacketReachFactorization
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (profiles : ℕ → ∀ who, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy who)
    (who : Player) : Prop :=
  ∃ (operational : ℕ → List (Option (OperationalState setup leaks)) → ℝ)
    (owner : ℕ → List (application setup leaks).PlayerEntry → ℝ) (error : ℕ → ℝ),
    Tendsto error atTop (nhds 0) ∧
    ∀ n (history : (onePacketProtocol setup leaks bounds horizon scheduler).History),
      ForcedState setup leaks who history.state →
      0 < othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who
        history.trace →
      |((onePacketModel setup leaks bounds (initialLaw setup) horizon
          scheduler).historyReachWeight (profiles n) history).toReal -
        othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who history.trace *
          operational n (operationalRecord setup leaks bounds horizon scheduler history.trace) *
          owner n (ownerRecall setup leaks who history.state)| ≤
        error n * (othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who
          history.trace *
          operational n (operationalRecord setup leaks bounds horizon scheduler history.trace) *
          owner n (ownerRecall setup leaks who history.state))

variable [Finite setup.intendedProtocol.History]

/-- The tremble scale of an intended assessment at depth `depth` and index
`n`. -/
abbrev componentScale (assessment : setup.intendedModel.BehavioralAssessment)
    (depth n : ℕ) : ℝ :=
  trembleScale (setup.intendedStepFloor assessment) depth n

theorem componentScale_nonneg (assessment : setup.intendedModel.BehavioralAssessment)
    (depth n : ℕ) : 0 ≤ componentScale setup assessment depth n :=
  trembleScale_nonneg (setup.intendedStepFloor_pos assessment).le

theorem componentScale_le_one (assessment : setup.intendedModel.BehavioralAssessment)
    (depth n : ℕ) : componentScale setup assessment depth n ≤ 1 :=
  trembleScale_le_one (setup.intendedStepFloor_pos assessment).le
    (setup.intendedStepFloor_le_one assessment)

/-- **The factorization claim.** Every sequence of keyed-component profiles on
the tremble scale of an intended assessment sequence factors operationally for
every observer. -/
def OnePacketFactorizationClaim (depth : ℕ) : Prop :=
  ∀ (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (timing : ℕ → LateKey setup leaks → unitInterval)
    (profiles : ℕ → ∀ who, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy who),
    (∀ n, KeyedComponentProfile setup leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) (componentScale setup (sequence n) depth n)
      (componentScale_nonneg setup (sequence n) depth n)
      (componentScale_le_one setup (sequence n) depth n) (timing n) (profiles n)) →
    ∀ who, OnePacketReachFactorization setup leaks bounds horizon scheduler sequence profiles who

/-- An accepted packet naming `event` is on the ledger. -/
def DeliveredBy (event : (graph setup).EventId) : (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ message ∈ control.execution.network.ledger,
      (message.id, true) ∈ control.execution.receipts ∧
        message.payload.call.event? (graph setup) = some event

/-- A late decision: `owner` is activated while its event is ready, and it has
emitted no packet naming that event. -/
def LateDecision (owner : Player) (event : (graph setup).EventId) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => control.actor = some owner ∧
      control.execution.application.config.cut.Ready event ∧
      (graph setup).actor? event = some owner ∧
      ∀ message ∈ control.execution.network.inputs, message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event

/-- The send rule keyed by the late-delivery key: the keyed component whose
send weight the rule reads from the key. -/
def keyedSendPolicy (assessment : setup.intendedModel.BehavioralAssessment) (depth n : ℕ)
    (rule : LateKey setup leaks → unitInterval) (owner : Player) :
    (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy
      owner := fun info =>
  keyedComponent setup leaks bounds (initialLaw setup) horizon scheduler assessment
    (componentScale setup assessment depth n) (componentScale_nonneg setup assessment depth n)
    (componentScale_le_one setup assessment depth n) ((lateKey setup leaks owner info).elim 0 rule)
    owner info

/-- The probability that terminal play from a history delivers `event`. -/
def lateDeliverySuccess
    (certificate : (onePacketProtocol setup leaks bounds horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy who)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (event : (graph setup).EventId) : ℝ :=
  (((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom certificate profile history).toOuterMeasure
      {final | DeliveredBy setup leaks event final.state}).toReal

/-- **The late-delivery claim.** Along keyed-component profiles, when the actor
of a late decision follows a keyed send rule and the others follow the `n`-th
profile, the success probability is the same at any two forced histories of the
actor with the same operational record. -/
def LateDeliveryClaim (depth : ℕ)
    (certificate : (onePacketProtocol setup leaks bounds horizon scheduler).WellFoundedHistories) :
    Prop :=
  ∀ (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (timing : ℕ → LateKey setup leaks → unitInterval)
    (profiles : ℕ → ∀ who, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy who),
    (∀ n, KeyedComponentProfile setup leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) (componentScale setup (sequence n) depth n)
      (componentScale_nonneg setup (sequence n) depth n)
      (componentScale_le_one setup (sequence n) depth n) (timing n) (profiles n)) →
    ∀ n (rule : LateKey setup leaks → unitInterval) (owner : Player)
      (event : (graph setup).EventId)
      (first second : (onePacketProtocol setup leaks bounds horizon scheduler).History),
      ForcedState setup leaks owner first.state → ForcedState setup leaks owner second.state →
      LateDecision setup leaks owner event first.state →
      LateDecision setup leaks owner event second.state →
      operationalRecord setup leaks bounds horizon scheduler first.trace =
        operationalRecord setup leaks bounds horizon scheduler second.trace →
      lateDeliverySuccess setup leaks bounds horizon scheduler certificate
          (Function.update (profiles n) owner
            (keyedSendPolicy setup leaks bounds horizon scheduler (sequence n) depth n rule owner))
          first event =
        lateDeliverySuccess setup leaks bounds horizon scheduler certificate
          (Function.update (profiles n) owner
            (keyedSendPolicy setup leaks bounds horizon scheduler (sequence n) depth n rule owner))
          second event

end Claims

end Vegas
