/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTableEntry
import Vegas.Game.PhaseCountServiceGood

/-! # Original entry-conditioned timing tables preserve the native good-event law -/

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
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
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
  (seed : RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed))

local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon (family seed)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon (family seed)
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
local notation "P" => phaseCountServicePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))

open Classical in
include calendar privateSuccess capacity catalogue in
/-- The actual native good-event law, jointly with every original private
timing table, is unchanged by arbitrary focal future policies. The entry is
supported by the literal initialized prescription; its original posterior
supplies member consistency. No independent table prior is installed there. -/
theorem phaseCountServiceTapePolicy_original_good_joint
    (seedSupported : seed ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : PhaseService.AsyncContract runtime leaks initial horizon (family seed) delay bound)
    (start : (app).Control) (trace : (E).Trace (some start))
    (entryStop : (E).History → Prop)
    (entrySupported : ⟨some start, trace⟩ ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon (family seed)).wellFoundedHistories
        (fun who => (menu).restrictPolicy initial horizon (family seed) who (P who))
          entryStop (E).initHistory).support)
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (firstFocal secondFocal : (N).BehavioralPolicy focal) :
    let posterior := independentProduct (fun who =>
      ((app).policyMixture original (fun table => Q table who)).posterior
        (start.execution.recall who))
    let owned := fun (tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool)
        (address : PhaseSeedAddress graph) =>
      match (serviceGraph setup mode).actor? address.val.event with
      | none => fun _ : Fin horizon => (false, false)
      | some owner => tables owner address
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let good := fun tables (history : (E).History) => match history with
      | ⟨none, _⟩ => false
      | ⟨some control, finalTrace⟩ => decide
        ((∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
          owner ∉ control.execution.application.current.excluded) ∧
          phaseCountServiceRawFree setup mode runtime leaks bounds horizon (owned tables) plan
            inputs (family seed) start phase focal control finalTrace)
    (posterior.bind fun tables =>
      (((N).runBehavioralUntil
        ((menu).bounded initial horizon (family seed)).wellFoundedHistories
        (Function.update (fun who => (menu).restrictPolicy initial horizon (family seed) who
          (Q (tables who) who)) focal firstFocal) stopped ⟨some start, trace⟩).map
            fun final => (good tables final, tables))) =
      (posterior.bind fun tables =>
        (((N).runBehavioralUntil
          ((menu).bounded initial horizon (family seed)).wellFoundedHistories
          (Function.update (fun who => (menu).restrictPolicy initial horizon (family seed) who
            (Q (tables who) who)) focal secondFocal) stopped ⟨some start, trace⟩).map
              fun final => (good tables final, tables))) := by
  classical
  intro posterior owned stopped good
  apply bind_congr_on_support
  intro tables supported
  have consistent := phaseCountServiceTapePolicy_table_entry_consistent setup mode runtime leaks
    bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    plan inputs (family seed) entryStop ⟨some start, trace⟩ entrySupported tables supported
  let firstProfile := Function.update (fun who =>
    (menu).restrictPolicy initial horizon (family seed) who (Q (tables who) who)) focal firstFocal
  let secondProfile := Function.update (fun who =>
    (menu).restrictPolicy initial horizon (family seed) who (Q (tables who) who)) focal secondFocal
  have ownEq (owner : Player) : Q (tables owner) owner = Q (owned tables) owner :=
    phaseCountServiceTapePolicy_owned_table setup mode runtime leaks bounds values choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tables owner
  have firstFollows (owner : Player) (foreign : owner ≠ focal) : firstProfile owner =
      (menu).restrictPolicy initial horizon (family seed) owner (Q (owned tables) owner) := by
    dsimp only [firstProfile]
    rw [Function.update_of_ne foreign]
    exact congrArg ((menu).restrictPolicy initial horizon (family seed) owner) (ownEq owner)
  have secondFollows (owner : Player) (foreign : owner ≠ focal) : secondProfile owner =
      (menu).restrictPolicy initial horizon (family seed) owner (Q (owned tables) owner) := by
    dsimp only [secondProfile]
    rw [Function.update_of_ne foreign]
    exact congrArg ((menu).restrictPolicy initial horizon (family seed) owner) (ownEq owner)
  have atEntry (owner : Player) (_foreign : owner ≠ focal) :
      (Q (owned tables) owner).Consistent (start.execution.recall owner) := by
    have known := consistent owner
    change (Q (tables owner) owner).Consistent (start.execution.recall owner) at known
    rw [ownEq owner] at known
    exact known
  have same := phaseCountServiceTapePolicy_good_law setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon (owned tables) plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs seedLaw family calendar privateSuccess
    capacity catalogue seed seed seedSupported seedSupported delay bound contract contract
    firstProfile secondProfile start trace trace phase installed commitment focal atEntry
    firstFollows secondFollows (fun _owner _foreign _event _inside _actor _bounded => rfl)
  have tagged := congrArg (PMF.map fun result : Bool => (result, tables)) same
  simp only [PMF.map_comp, Function.comp_def, firstProfile, secondProfile] at tagged
  convert tagged using 1

end Vegas
