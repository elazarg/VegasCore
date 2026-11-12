module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketDelivery
public import Vegas.Game.OnePacketIntendedProjection
public import Vegas.Pending.ExclusionInformationHistory
public import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

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
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup timeouts leaks).State)
  (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu timeouts leaks).protocol initial horizon scheduler).History]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds initial horizon scheduler

variable [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds initial horizon
  scheduler).InfoState who)]

/-- An agent owing a failure: it owes one at the decoded point of some history
of its information state. -/
def OwingAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ∃ history : (onePacketN).InformationHistory agent.1 agent.2.1, ∃ point,
    nativeDecodedState setup timeouts leaks history.1.state = some point ∧
      ProtocolState.OwesFailure agent.1 setup.program point

/-- Decisions outside the clear forced region have a free pool. Clearance
requires the whole displayed public default set to be empty. -/
def FreeAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : Prop :=
  ¬ ((ClearInput timeouts) leaks agent.2.1 ∧
    forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) initial horizon
      scheduler agent.1 agent.2.1)

/-- An agent that is not free is in the forced region. -/
theorem forcedAgent_of_not_free
    {agent : (onePacketN).InformationAgent (onePacketN).playedInformation}
    (notFree : ¬ FreeAgent setup timeouts leaks bounds initial horizon scheduler agent) :
    forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) initial horizon
      scheduler agent.1 agent.2.1 :=
  (Classical.not_not.mp notFree).2

/-- **The pools of the one-packet certificate.** A free agent sits alone,
choosing among its choices; forced late deliveries sharing a late-delivery key
form a pool with the late options as parts; every other agent sits in one pool
with one part. -/
abbrev onePacketPool :=
  freeKeyedPool (FreeAgent setup timeouts leaks bounds initial horizon scheduler)
    (LateDeliveryAgent setup timeouts leaks bounds initial horizon scheduler)
    (agentLateKey setup timeouts leaks bounds initial horizon scheduler)

/-- The parts of the pools of the one-packet certificate. -/
abbrev OnePacketPart (slots : Nat) :=
  FreeKeyedPart (FreeAgent setup timeouts leaks bounds initial horizon scheduler)
    (LateDeliveryAgent setup timeouts leaks bounds initial horizon scheduler)
    (agentLateKey setup timeouts leaks bounds initial horizon scheduler) (LateOption
      slots)

/-- The free law of an unforced agent's choice: the choice trembled toward the
uniform law over its menu with weight `scale`. -/
def unforcedLaw (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  mix scale nonnegative le_one
    ((bounds.onePacketMenu timeouts leaks).uniformPolicy initial horizon
      scheduler agent.1 agent.2.1) (PMF.pure choice)

/-- **The components of the one-packet certificate.** Unforced agents tremble
each choice; forced late deliveries play the late component of each option;
every other agent plays the slot-trembled prescribed component, all with the
intended assessment `assessment` and the tremble scale `scale`. -/
def onePacketComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    OnePacketPart setup timeouts leaks bounds initial horizon scheduler slots
        (onePacketPool setup timeouts leaks bounds initial horizon scheduler agent) →
      PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  freeKeyedComponent (unforcedLaw setup timeouts leaks bounds initial horizon scheduler scale
    nonnegative le_one)
    (fun agent => slotPrescribedComponent setup timeouts leaks bounds initial horizon
      scheduler
      assessment scale nonnegative le_one agent.1 agent.2.1)
    (fun agent option => lateComponent setup timeouts leaks bounds initial horizon
      scheduler
      assessment scale nonnegative le_one agent.1 agent.2.1 option) agent

theorem unforcedLaw_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    FullSupport (unforcedLaw setup timeouts leaks bounds initial horizon scheduler scale positive.le
      le_one agent choice) := by
  intro other
  let := Fintype.ofFinite ((onePacketN).Choice agent.1 agent.2.1)
  exact mem_support_mix_left _ _ _ positive (mem_support_uniformLaw other)

theorem onePacketComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (part : OnePacketPart setup timeouts leaks bounds initial horizon scheduler slots
      (onePacketPool setup timeouts leaks bounds initial horizon scheduler agent)) :
    FullSupport (onePacketComponent setup timeouts leaks bounds initial horizon scheduler assessment
      scale positive.le le_one agent part) :=
  freeKeyedComponent_fullSupport _ _ _
    (unforcedLaw_fullSupport setup timeouts leaks bounds initial horizon scheduler positive le_one)
    (fun agent => by
      unfold slotPrescribedComponent
      exact slotTrembledChoice_fullSupport setup timeouts leaks bounds initial horizon
        scheduler positive le_one agent.1 agent.2.1 _ _ _)
    (fun agent option => lateComponent_fullSupport setup timeouts leaks bounds initial
      horizon
      scheduler assessment positive le_one agent.1 agent.2.1 option) agent part


/-- A non-free decision displays an empty whole public default set. -/
theorem clearInput_of_not_free
    {agent : (onePacketN).InformationAgent (onePacketN).playedInformation}
    (notFree : ¬ FreeAgent setup timeouts leaks bounds initial horizon scheduler agent) :
    (ClearInput timeouts) leaks agent.2.1 :=
  (Classical.not_not.mp notFree).1

/-- Every decision after any public default has its own free pool. -/
theorem freeAgent_of_publicDefault
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (flagged : (PublicDefaultInput timeouts) leaks agent.2.1) :
    FreeAgent setup timeouts leaks bounds initial horizon scheduler agent := by
  have deciding : agent.2.1.isSome := by
    obtain ⟨past, view, same, _⟩ := flagged
    rw [same]
    rfl
  exact fun forced =>
    (((clearInput_iff_not_publicDefaultInput timeouts) leaks agent.2.1 deciding).mp forced.1)
      flagged

/-- A free component converges to its selected pure choice as the common
reference perturbation vanishes. -/
theorem unforcedLaw_converges (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n)
    (le_one : ∀ n, scale n ≤ 1) (vanishes : Tendsto scale atTop (nhds 0))
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (choice : (onePacketN).Choice agent.1 agent.2.1) :
    PMFConvergesPointwise (fun n => unforcedLaw setup timeouts leaks bounds initial horizon
      scheduler
      (scale n) (positive n).le (le_one n) agent choice) (PMF.pure choice) :=
  pmfConvergesPointwise_mix_zero scale (fun n => (positive n).le) le_one vanishes
    ((bounds.onePacketMenu timeouts leaks).uniformPolicy initial horizon scheduler agent.1
      agent.2.1) (PMF.pure choice)

end Vegas
