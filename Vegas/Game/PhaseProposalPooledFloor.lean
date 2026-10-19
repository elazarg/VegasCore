/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryFloor
import Vegas.Game.PhaseProposalOrdinaryCoverage
import Interaction.ReactiveMenuLikelihood

/-! # An actual response floor chosen before bad noise and pool optimization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))

private theorem ordinary_strategy_atom
    (startLaw : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (response : PhaseProposal.Response runtime leaks bounds who past view) :
    (phaseProposalOrdinaryStrategy setup mode runtime leaks bounds plan startLaw horizon scheduler
      values rates who (some (past, view)) ⟨some response.val, response.val, response.property,
        rfl⟩).toReal =
      (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan values rates who past
        view response).toReal := by
  let chosen : ((menu).information startLaw horizon scheduler).Choice who (some (past, view)) :=
    ⟨some response.val, response.val, response.property, rfl⟩
  let policy := phaseProposalOrdinaryPolicy setup mode runtime leaks bounds plan values rates who
  have rawAtom := (menu).restrictPolicy_atom startLaw horizon scheduler who policy past view
    response.val (phaseProposalOrdinaryPolicy_covered setup mode runtime leaks bounds plan values
      rates who past view)
  have chosenAtom := pmf_map_apply_of_injective
    (f := fun choice : ((menu).information startLaw horizon scheduler).Choice who
      (some (past, view)) => choice.val)
    ((menu).restrictPolicy startLaw horizon scheduler who policy (some (past, view)))
    Subtype.val_injective chosen
  calc
    _ = ((((menu).restrictPolicy startLaw horizon scheduler who policy (some (past, view))).map
        Subtype.val) (some response.val)).toReal := congrArg ENNReal.toReal chosenAtom.symm
    _ = (policy past view response.val).toReal := congrArg ENNReal.toReal rawAtom
    _ = _ := congrArg ENNReal.toReal
      (pmf_map_apply_of_injective _ Subtype.val_injective response)

/-- Choose the floor from ALL intrinsic counted information sites before
choosing the private bad rate, honest pins or free source pool weights. Every
actual prepared response, including each historical alias, has this floor. -/
theorem exists_phaseProposalPooled_response_floor
    [Fintype setup.proposalRecoveryProtocol.History]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (finite : setup.program.FiniteBindingTypes)
    (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1)
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (aliases : 0 < rates.aliases.val) (horizon : Nat) (scheduler : (app).Scheduler)
    [(app).FiniteNature initial scheduler] :
    ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
      ∀ (bad : Set.Icc (0 : ℝ) 1), 0 < bad.val → bad.val ≤ 1 / 2 →
      ∀ (pins : (pool : setup.ProposalRecoveryValuePool) →
          Option (PMF (setup.ProposalRecoveryPoolPart pool)))
        (weights : (pool : setup.ProposalRecoveryValuePool) →
          PMF (setup.ProposalRecoveryPoolPart pool))
        (remaining : Nat) (owner : Player) (execution : (app).Execution)
        (_trace : ((menu).protocol initial horizon scheduler).Trace
          (some ⟨remaining, some owner, execution⟩))
        (response : PhaseProposal.Response runtime leaks bounds owner (execution.recall owner)
          (execution.observe app owner)),
        phaseProposalResponsePrepared setup mode runtime leaks response.val →
        lower ≤ (phaseProposalReferenceResponses setup mode runtime leaks bounds plan
          (setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
            pins weights) { rates with badPreparation := bad } owner (execution.recall owner)
              (execution.observe app owner) response).toReal := by
  classical
  let values := fun who (key : setup.ProposalRecoveryComponent who) =>
    setup.commitRecoveryValueReference finite who key.1
  obtain ⟨minimum, minimumPositive, minimumBounded, minimumAt⟩ :=
    exists_phaseProposalOrdinaryStrategy_floor setup mode runtime leaks bounds plan initial
      horizon scheduler values rates
  let lower := (floor / 2) * minimum
  have lowerPositive : 0 < lower := mul_pos (by positivity) minimumPositive
  have lowerBounded : lower ≤ 1 := by
    have first := mul_le_of_le_one_right (show 0 ≤ floor / 2 by positivity) minimumBounded
    dsimp only [lower]
    linarith
  refine ⟨lower, lowerPositive, lowerBounded, ?_⟩
  intro bad badPositive badSmall pins weights remaining owner execution trace response prepared
  let target := setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
    pins weights
  let actualRates : PhaseProposalRates := { rates with badPreparation := bad }
  have targetFull : ∀ who key, FullSupport (target who key) :=
    setup.proposalRecoveryPooledDomainLaw_fullSupport finite floor floorPositive floorBounded
      pins weights
  have valuesFull : ∀ who key, FullSupport (values who key) :=
    fun who key => setup.commitRecoveryValueReference_fullSupport finite who key.1
  have ordinarySupported := phaseProposalOrdinaryResponses_supported_of_counted setup mode runtime
    leaks bounds plan complete covered maximal values valuesFull rates waitPositive waitBelow
      slotPositive aliases horizon scheduler remaining owner execution trace response prepared
  let history : ((menu).protocol initial horizon scheduler).History :=
    ⟨some ⟨remaining, some owner, execution⟩, trace⟩
  have running : ¬((menu).protocol initial horizon scheduler).terminal history.state := by
    intro stopped
    cases stopped.2
  obtain ⟨site, observed⟩ := (model horizon scheduler).exists_informationSite_of_active owner
    history running rfl
  have siteInfo : site.val = some (execution.recall owner, execution.observe app owner) := by
    rw [observed]
    change ((menu).signals initial horizon scheduler).infoOf owner trace = _
    rw [(menu).info]
    simp only [ReactiveApplication.observe, ite_true]
  have atSite := minimumAt owner site
  rw [siteInfo] at atSite
  let chosen : (model horizon scheduler).Choice owner
      (some (execution.recall owner, execution.observe app owner)) :=
    ⟨some response.val, response.val, response.property, rfl⟩
  have atomEq := ordinary_strategy_atom setup mode runtime leaks bounds plan initial horizon
    scheduler values rates owner (execution.recall owner) (execution.observe app owner) response
  have supported : chosen ∈ (phaseProposalOrdinaryStrategy setup mode runtime leaks bounds plan
      initial horizon scheduler values rates owner
        (some (execution.recall owner, execution.observe app owner))).support := by
    apply pmf_toReal_pos_iff.mp
    rw [atomEq]
    exact pmf_toReal_pos_iff.mpr ordinarySupported
  have ordinaryMinimum := atSite chosen supported
  rw [atomEq] at ordinaryMinimum
  have full := phaseProposalBaseClasses_fullSupport_of_counted setup mode runtime leaks bounds plan
    complete covered maximal target targetFull actualRates waitPositive waitBelow slotPositive
      badPositive (by dsimp only [actualRates]; linarith) horizon scheduler remaining owner
        execution trace
  have dominated := phaseProposalReferenceResponses_ordinary_domination setup mode runtime leaks
    bounds plan values target actualRates floor floorPositive.le floorBounded
      (phaseProposalPooledDomain_ordinary_domination setup finite floor floorPositive.le
        floorBounded pins weights) owner (execution.recall owner) (execution.observe app owner)
        full response
  have sameOrdinary : actualRates.ordinary = rates.ordinary := rfl
  dsimp only [phaseProposalOrdinaryResponses] at dominated ordinaryMinimum
  rw [sameOrdinary] at dominated
  have half : floor / 2 ≤ (1 - actualRates.badPreparation.val) * floor := by
    dsimp only [actualRates]
    nlinarith
  calc
    lower ≤ (floor / 2) * _ :=
      mul_le_mul_of_nonneg_left ordinaryMinimum (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right half ENNReal.toReal_nonneg
    _ ≤ _ := dominated

end Vegas
