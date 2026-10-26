/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionBoundedLift
import Vegas.Game.OnePacketDelivery
import Vegas.Game.OnePacketIntendedProjection
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools

/-! # Free and keyed components of the recovery one-packet game

Public exclusion makes every player's remaining decision agents free. Before
exclusion, forced source regions retain their slot and late operational laws.
All components use the actual recovery menus and full private recall.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (RecoveryState (graph setup)))
  (horizon : Nat) (scheduler : (recoveryApplication runtime leaks).Scheduler)

abbrev model := (Recovery.onePacketMenu runtime leaks bounds).information initial horizon
  scheduler

local notation "N" => model setup runtime leaks bounds initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu runtime leaks bounds

/-- A nonempty permanent exclusion set in the deciding player's public input. -/
def PublicExclusion (input : (recoveryApplication runtime leaks).Info) : Prop :=
  ∃ past view, input = some (past, view) ∧ view.application.2 ≠ ∅

omit [Fintype Player] in
/-- Public exclusion prevents the full input from being a clear native lift. -/
theorem not_clearInput_of_publicExclusion
    {input : (recoveryApplication runtime leaks).Info}
    (excluded : PublicExclusion setup runtime leaks input) :
    ¬ ClearInput runtime leaks input := by
  obtain ⟨past, view, rfl, nonempty⟩ := excluded
  intro clear
  change some _ = some (past, view) at clear
  have flags := congrArg (fun data => data.2.application.2) (Option.some.inj clear)
  exact nonempty flags.symm

variable [Fintype ((Recovery.onePacketMenu runtime leaks bounds).protocol initial horizon
  scheduler).History]
  [∀ who, DecidableEq ((model setup runtime leaks bounds initial horizon scheduler).InfoState who)]

/-- A forced recovery input has a complete clear lift and an actual recovery
history whose native source point is in the focal forced region. -/
def ForcedAgent (agent : (N).InformationAgent (N).playedInformation) : Prop :=
  ClearInput runtime leaks agent.2.1 ∧
    ∃ history : (N).InformationHistory agent.1 agent.2.1,
      ForcedState setup runtime leaks agent.1 (protocolState runtime leaks history.1.state)

/-- Recovery decisions outside the clear forced region are completed freely. -/
def FreeAgent (agent : (N).InformationAgent (N).playedInformation) : Prop :=
  ¬ ForcedAgent setup runtime leaks bounds initial horizon scheduler agent

/-- Source debt at an actual history of a recovery information input. -/
def OwingAgent (agent : (N).InformationAgent (N).playedInformation) : Prop :=
  ∃ history : (N).InformationHistory agent.1 agent.2.1, ∃ point,
    nativeDecodedState setup runtime leaks (protocolState runtime leaks history.1.state) =
      some point ∧ ProtocolState.OwesFailure agent.1 setup.program point

/-- Late operational decisions are keyed by the projected complete native input. -/
def KeyedAgent (agent : (N).InformationAgent (N).playedInformation) : Prop :=
  LateDelivery setup runtime leaks agent.1 (RecoveryProjection.information runtime leaks agent.2.1)

def agentKey (agent : (N).InformationAgent (N).playedInformation) : Option (LateKey setup runtime
  leaks) :=
  lateKey setup runtime leaks agent.1 (RecoveryProjection.information runtime leaks agent.2.1)

abbrev pool := freeKeyedPool (FreeAgent setup runtime leaks bounds initial horizon scheduler)
  (KeyedAgent setup runtime leaks bounds initial horizon scheduler)
  (agentKey setup runtime leaks bounds initial horizon scheduler)

abbrev Part (slots : Nat) := FreeKeyedPart
  (FreeAgent setup runtime leaks bounds initial horizon scheduler)
  (KeyedAgent setup runtime leaks bounds initial horizon scheduler)
  (agentKey setup runtime leaks bounds initial horizon scheduler) (LateOption slots)

/-- Every decision input after any public exclusion has its own free pool. -/
theorem freeAgent_of_publicExclusion
    (agent : (N).InformationAgent (N).playedInformation)
    (excluded : PublicExclusion setup runtime leaks agent.2.1) :
    FreeAgent setup runtime leaks bounds initial horizon scheduler agent :=
  fun forced => not_clearInput_of_publicExclusion setup runtime leaks excluded forced.1

/-- The actual menu's uniform reference perturbs each freely selected choice. -/
def freeLaw (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (choice : (N).Choice agent.1 agent.2.1) : PMF ((N).Choice agent.1 agent.2.1) :=
  mix scale nonnegative le_one ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1)
    (PMF.pure choice)

/-- The source slot component, lifted into the actual clear recovery menu. -/
def prescribedComponent (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation) :
    PMF ((N).Choice agent.1 agent.2.1) :=
  boundedRecoveryLaw runtime leaks bounds initial horizon scheduler agent.1 agent.2.1
    (slotPrescribedComponent setup runtime leaks bounds (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) assessment scale nonnegative le_one agent.1
      (RecoveryProjection.information runtime leaks agent.2.1))

/-- Each late option keeps the same source value law at clear recovery inputs. -/
def keyedComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation) (option : LateOption slots) :
    PMF ((N).Choice agent.1 agent.2.1) :=
  boundedRecoveryLaw runtime leaks bounds initial horizon scheduler agent.1 agent.2.1
    (lateComponent setup runtime leaks bounds (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) assessment scale nonnegative le_one agent.1
      (RecoveryProjection.information runtime leaks agent.2.1) option)

def component (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation) :
    Part setup runtime leaks bounds initial horizon scheduler slots
        (pool setup runtime leaks bounds initial horizon scheduler agent) →
      PMF ((N).Choice agent.1 agent.2.1) :=
  freeKeyedComponent (freeLaw setup runtime leaks bounds initial horizon scheduler scale
    nonnegative le_one)
    (prescribedComponent setup runtime leaks bounds initial horizon scheduler assessment scale
      nonnegative
      le_one)
    (keyedComponent setup runtime leaks bounds initial horizon scheduler assessment scale
      nonnegative
      le_one)
    agent

theorem freeLaw_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (choice : (N).Choice agent.1 agent.2.1) :
    FullSupport (freeLaw setup runtime leaks bounds initial horizon scheduler scale positive.le
      le_one agent
      choice) := by
  intro other
  let := Fintype.ofFinite ((N).Choice agent.1 agent.2.1)
  exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype other)

theorem component_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (part : Part setup runtime leaks bounds initial horizon scheduler slots
      (pool setup runtime leaks bounds initial horizon scheduler agent)) :
    FullSupport (component setup runtime leaks bounds initial horizon scheduler assessment scale
      positive.le
      le_one agent part) := by
  apply freeKeyedComponent_fullSupport
  · exact freeLaw_fullSupport setup runtime leaks bounds initial horizon scheduler positive le_one
  · intro player
    unfold prescribedComponent
    apply boundedRecoveryLaw_fullSupport
    exact slotTrembledChoice_fullSupport setup runtime leaks bounds (initial.map
      RecoveryState.native)
      horizon (nativeScheduler runtime leaks scheduler) positive le_one player.1
      (RecoveryProjection.information runtime leaks player.2.1) _ _ _
  · intro player option
    unfold keyedComponent
    apply boundedRecoveryLaw_fullSupport
    exact lateComponent_fullSupport setup runtime leaks bounds (initial.map RecoveryState.native)
      horizon
      (nativeScheduler runtime leaks scheduler) assessment positive le_one player.1
      (RecoveryProjection.information runtime leaks player.2.1) option

/-- Free components converge to their selected pure choices when their common
reference perturbation vanishes. -/
theorem freeLaw_converges (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n)
    (le_one : ∀ n, scale n ≤ 1) (vanishes : Filter.Tendsto scale Filter.atTop (nhds 0))
    (agent : (N).InformationAgent (N).playedInformation)
    (choice : (N).Choice agent.1 agent.2.1) :
    PMFConvergesPointwise (fun n => freeLaw setup runtime leaks bounds initial horizon scheduler
      (scale n)
      (positive n).le (le_one n) agent choice) (PMF.pure choice) :=
  pmfConvergesPointwise_mix_zero scale (fun n => (positive n).le) le_one vanishes
    ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) (PMF.pure choice)

end Vegas.RecoveryOnePacket
