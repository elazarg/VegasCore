/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServicePhase

/-! # Actual foreign survivor laws under private event service -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

section SurvivorLaw

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry → (phaseApplication runtime
      leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (horizon : Nat) (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (ordered : (serviceGraph setup
      mode).RevealRelaxedOrdered)
  (inputs : PMF (serviceGraph setup mode).Inputs)
  {LocalSeed RestSeed : Type}
  (seedLaw : PMF (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)))
  (family : (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)) →
      (phaseApplication runtime leaks).Scheduler)
  (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
    seedLaw family)
  (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan inputs horizon
    seedLaw family)
  (capacity : horizon ≤ bounds.candidateCount)
  (catalogue : ∀ owner event payload (_binding : (serviceGraph setup mode).outputLayout event =
      .binding owner payload),
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "rawWeight" => (0 : ℝ)
local notation "rawNonnegative" => (le_refl (0 : ℝ))
local notation "rawBounded" => (zero_le_one (α := ℝ))
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes

local notation "originalTapes" => independentProduct (fun _coordinate : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))


include ordered calendar privateSuccess capacity catalogue in
/-- The actual first-attempt stopped laws have the same joint foreign
survivor vector under arbitrary focal continuation policies. The ORIGINAL
supported zero-RAW timing table and original foreign event seeds are fixed;
endpoint controls, receipts and own-recall consistency are derived. -/
theorem phaseCountServiceTapePolicy_foreign_survivors_law
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (firstContract : PhaseService.AsyncContract runtime leaks initial horizon (family firstSeeds)
      delay bound)
    (secondContract : PhaseService.AsyncContract runtime leaks initial horizon (family secondSeeds)
      delay bound)
    (firstProfile : ∀ who, ((menu).information initial horizon
      (family firstSeeds)).BehavioralPolicy who)
    (secondProfile : ∀ who, ((menu).information initial horizon
      (family secondSeeds)).BehavioralPolicy who)
    (start : (app).Control)
    (firstStart : ((menu).protocol initial horizon (family firstSeeds)).Trace (some start))
    (secondStart : ((menu).protocol initial horizon (family secondSeeds)).Trace (some start))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (atEntry : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (start.execution.recall owner))
    (firstFollows : ∀ owner, owner ≠ focal → firstProfile owner =
      (menu).restrictPolicy initial horizon (family firstSeeds) owner (Q owner))
    (secondFollows : ∀ owner, owner ≠ focal → secondProfile owner =
      (menu).restrictPolicy initial horizon (family secondSeeds) owner (Q owner))
    (tapeSupport : tapes ∈ (originalTapes).support)
    (sameSeeds : ∀ owner, owner ≠ focal → ∀ event ∈ phase.events, (serviceGraph setup mode).actor?
      event = some owner →
      ∀ bounded, firstSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩) =
        secondSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩)) :
    let firstStopped := fun history : ((menu).protocol initial horizon
        (family firstSeeds)).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let secondStopped := fun history : ((menu).protocol initial horizon
        (family secondSeeds)).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let survivors := fun state : Option (app).Control => match state with
      | none => ∅
      | some control => Finset.univ.filter fun owner => owner ≠ focal ∧
          owner ∉ start.execution.application.current.excluded ∧
            owner ∉ control.execution.application.current.excluded
    ((((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
      ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
      firstStopped ⟨some start, firstStart⟩).map fun history => survivors history.state) =
    ((((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
      ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
      secondStopped ⟨some start, secondStart⟩).map fun history => survivors history.state) := by
  classical
  intro firstStopped secondStopped survivors
  let firstLaw := ((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
    ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
    firstStopped ⟨some start, firstStart⟩
  let secondLaw := ((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
    ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
    secondStopped ⟨some start, secondStart⟩
  have same : ∀ first ∈ firstLaw.support, ∀ second ∈ secondLaw.support,
      survivors first.state = survivors second.state := by
    rintro ⟨firstState, firstTrace⟩ firstRun ⟨secondState, secondTrace⟩ secondRun
    obtain ⟨first, firstEq, _changed, _idle, _snapshot⟩ :=
      phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon
        (family firstSeeds) delay bound firstContract firstProfile start firstStart phase installed
        ⟨firstState, firstTrace⟩ (by
          convert firstRun using 1; congr 3; funext history
          dsimp only [firstStopped]
          cases history.state <;> rfl)
    cases firstEq
    obtain ⟨second, secondEq, _changed, _idle, _snapshot⟩ :=
      phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon
        (family secondSeeds) delay bound secondContract secondProfile start secondStart phase
        installed ⟨secondState, secondTrace⟩ (by
          convert secondRun using 1; congr 3; funext history
          dsimp only [secondStopped]
          cases history.state <;> rfl)
    cases secondEq
    have common := phaseCountServiceTapePolicy_foreign_survival_iff setup mode runtime leaks
      bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded horizon tapes plan ordered inputs
      seedLaw family calendar privateSuccess capacity catalogue firstSeeds secondSeeds firstSupport
      secondSupport delay bound firstContract secondContract firstProfile secondProfile start first
      second firstStart secondStart firstTrace secondTrace phase installed commitment focal
      firstRun secondRun atEntry firstFollows secondFollows tapeSupport sameSeeds
    apply Finset.ext
    intro owner
    change (owner ∈ Finset.univ.filter fun who => who ≠ focal ∧
        who ∉ start.execution.application.current.excluded ∧
          who ∉ first.execution.application.current.excluded) ↔
      (owner ∈ Finset.univ.filter fun who => who ≠ focal ∧
        who ∉ start.execution.application.current.excluded ∧
          who ∉ second.execution.application.current.excluded)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨foreign, active, surviving⟩
    · exact ⟨foreign, active, (common.2 owner foreign active).mp surviving⟩
    · exact ⟨foreign, active, (common.2 owner foreign active).mpr surviving⟩
  obtain ⟨reference, supported⟩ := secondLaw.support_nonempty
  calc
    _ = firstLaw.map (fun _ => survivors reference.state) :=
      map_congr_on_support firstLaw (fun first member => same first member reference supported)
    _ = PMF.pure (survivors reference.state) := PMF.map_const _ _
    _ = secondLaw.map (fun _ => survivors reference.state) := (PMF.map_const _ _).symm
    _ = secondLaw.map (fun second => survivors second.state) :=
      map_congr_on_support secondLaw (fun second member => by
        obtain ⟨first, present⟩ := firstLaw.support_nonempty
        exact (same first present reference supported).symm.trans
          (same first present second member))

end SurvivorLaw

end Vegas
