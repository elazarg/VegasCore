/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDelivery
import Vegas.Game.OnePacketIntendedProjection
import Vegas.Pending.ExclusionInformationHistory
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools

/-! # Free and keyed components of the native one-packet game

The clear forced region retains the source slot and late operational laws.
Every other agent has a separate free pool, including every decision after
any public default. All laws inhabit the ordinary native menu's choice carrier.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup runtime leaks).State)
  (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu runtime leaks).protocol initial horizon scheduler).History]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds initial horizon scheduler

variable [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds initial horizon
  scheduler).InfoState who)]

/-- An agent owing a failure: it owes one at the decoded point of some history
of its information state. -/
def OwingAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ∃ history : (onePacketN).InformationHistory agent.1 agent.2.1, ∃ point,
    nativeDecodedState setup runtime leaks history.1.state = some point ∧
      ProtocolState.OwesFailure agent.1 setup.program point

/-- Decisions outside the clear forced region have a free pool. Clearance
requires the whole displayed public default set to be empty. -/
def FreeAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ¬ (runtime.ClearInput leaks agent.2.1 ∧
    forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) initial horizon
      scheduler agent.1 agent.2.1)

/-- An agent that is not free is in the forced region. -/
theorem forcedAgent_of_not_free
    {agent : (onePacketN).InformationAgent (onePacketN).playedInformation}
    (notFree : ¬ FreeAgent setup runtime leaks bounds initial horizon scheduler agent) :
    forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) initial horizon
      scheduler agent.1 agent.2.1 :=
  (Classical.not_not.mp notFree).2

/-- **The pools of the one-packet certificate.** A free agent sits alone,
choosing among its choices; forced late deliveries sharing a late-delivery key
form a pool with the late options as parts; every other agent sits in one pool
with one part. -/
abbrev onePacketPool :=
  freeKeyedPool (FreeAgent setup runtime leaks bounds initial horizon scheduler)
    (LateDeliveryAgent setup runtime leaks bounds initial horizon scheduler)
    (agentLateKey setup runtime leaks bounds initial horizon scheduler)

/-- The parts of the pools of the one-packet certificate. -/
abbrev OnePacketPart (slots : Nat) :=
  FreeKeyedPart (FreeAgent setup runtime leaks bounds initial horizon scheduler)
    (LateDeliveryAgent setup runtime leaks bounds initial horizon scheduler)
    (agentLateKey setup runtime leaks bounds initial horizon scheduler) (LateOption
      slots)

/-- The free law of an unforced agent's choice: the choice trembled toward the
uniform law over its menu with weight `scale`. -/
def unforcedLaw (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  mix scale nonnegative le_one
    ((bounds.onePacketMenu runtime leaks).uniformPolicy initial horizon
      scheduler agent.1 agent.2.1) (PMF.pure choice)

/-- **The components of the one-packet certificate.** Unforced agents tremble
each choice; forced late deliveries play the late component of each option;
every other agent plays the slot-trembled prescribed component, all with the
intended assessment `assessment` and the tremble scale `scale`. -/
def onePacketComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    OnePacketPart setup runtime leaks bounds initial horizon scheduler slots
        (onePacketPool setup runtime leaks bounds initial horizon scheduler agent) →
      PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  freeKeyedComponent (unforcedLaw setup runtime leaks bounds initial horizon scheduler scale
    nonnegative le_one)
    (fun agent => slotPrescribedComponent setup runtime leaks bounds initial horizon
      scheduler
      assessment scale nonnegative le_one agent.1 agent.2.1)
    (fun agent option => lateComponent setup runtime leaks bounds initial horizon
      scheduler
      assessment scale nonnegative le_one agent.1 agent.2.1 option) agent

theorem unforcedLaw_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    FullSupport (unforcedLaw setup runtime leaks bounds initial horizon scheduler scale positive.le
      le_one agent choice) := by
  intro other
  let := Fintype.ofFinite ((onePacketN).Choice agent.1 agent.2.1)
  exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype other)

theorem onePacketComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (part : OnePacketPart setup runtime leaks bounds initial horizon scheduler slots
      (onePacketPool setup runtime leaks bounds initial horizon scheduler agent)) :
    FullSupport (onePacketComponent setup runtime leaks bounds initial horizon scheduler assessment
      scale positive.le le_one agent part) :=
  freeKeyedComponent_fullSupport _ _ _
    (unforcedLaw_fullSupport setup runtime leaks bounds initial horizon scheduler positive le_one)
    (fun agent => by
      unfold slotPrescribedComponent
      exact slotTrembledChoice_fullSupport setup runtime leaks bounds initial horizon
        scheduler positive le_one agent.1 agent.2.1 _ _ _)
    (fun agent option => lateComponent_fullSupport setup runtime leaks bounds initial
      horizon
      scheduler assessment positive le_one agent.1 agent.2.1 option) agent part


/-- A non-free decision displays an empty whole public default set. -/
theorem clearInput_of_not_free
    {agent : (onePacketN).InformationAgent (onePacketN).playedInformation}
    (notFree : ¬ FreeAgent setup runtime leaks bounds initial horizon scheduler agent) :
    runtime.ClearInput leaks agent.2.1 :=
  (Classical.not_not.mp notFree).1

/-- Every decision after any public default has its own free pool. -/
theorem freeAgent_of_publicDefault
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (flagged : runtime.PublicDefaultInput leaks agent.2.1) :
    FreeAgent setup runtime leaks bounds initial horizon scheduler agent := by
  have deciding : agent.2.1.isSome := by
    obtain ⟨past, view, same, _⟩ := flagged
    rw [same]
    rfl
  exact fun forced =>
    ((runtime.clearInput_iff_not_publicDefaultInput leaks agent.2.1 deciding).mp forced.1) flagged

/-- A free component converges to its selected pure choice as the common
reference perturbation vanishes. -/
theorem unforcedLaw_converges (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n)
    (le_one : ∀ n, scale n ≤ 1) (vanishes : Tendsto scale atTop (nhds 0))
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    PMFConvergesPointwise (fun n => unforcedLaw setup runtime leaks bounds initial horizon scheduler
      (scale n) (positive n).le (le_one n) agent choice) (PMF.pure choice) :=
  pmfConvergesPointwise_mix_zero scale (fun n => (positive n).le) le_one vanishes
    ((bounds.onePacketMenu runtime leaks).uniformPolicy initial horizon scheduler agent.1
      agent.2.1) (PMF.pure choice)

end Vegas
