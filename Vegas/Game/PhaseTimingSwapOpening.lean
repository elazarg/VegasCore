/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingSwapKey
import Vegas.Game.PhaseTimingPoolPlan
import Vegas.Game.PhaseSourceSlotPolicyLaw
import Vegas.Game.PhaseTimingOpeningResponse
import Vegas.Game.PhaseTimingKeyProperties
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPoolObservation

/-! # Actual full-plan opening laws across hidden private input changes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

variable (wellFormed : setup.WellFormed)
  (source : setup.commitRecoveryModel.BehavioralAssessment)
  (swap : HiddenSwap (serviceGraph setup mode)) (remaining : Nat) (who : Player)
  (original : (phaseApplication runtime leaks).Execution)
  (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some ⟨remaining, some who, original⟩))
  (swappedTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some ⟨remaining, some who, swap.phaseExecution original⟩))
  (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
  (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
  (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
  (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
  (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
    ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
  (node : nodeView (serviceGraph setup mode) event =
    .resolve who payload binding checks outputEq codeEq)
  (request : original.application.SeedRequest who ⟨original.application.attempt, event⟩)
  (fixed : RevealFixed swap original.application.current.native event)
  (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (original.recall who),
    PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩)
  (value : L.Val payload)
  (stored : binding.get? original.application.current.native.config.store = some (.success value))
  (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values)

include plan inputs horizon scheduler trace swappedTrace node request fixed unsent stored values in
private theorem opening_dispatch_laws :
    ∃ response : (app).Action,
      phaseSourcePolicy setup mode runtime leaks bounds wellFormed source who
          (original.recall who) (original.observe app who) = PMF.pure response ∧
      phaseSourcePolicy setup mode runtime leaks bounds wellFormed source who
          ((swap.phaseExecution original).recall who)
          ((swap.phaseExecution original).observe app who) = PMF.pure response ∧
      phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed source who
          (original.recall who) (original.observe app who) = PMF.pure response ∧
      phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed source who
          ((swap.phaseExecution original).recall who)
          ((swap.phaseExecution original).observe app who) = PMF.pure response := by
  have field : swap.values.value binding.field = id := by
    have fixedAt : swap.values.value binding.field = id ∧
        ∀ candidate, original.application.current.native.accepted binding.field = some candidate →
          swap.raw candidate = id := by
      simpa only [RevealFixed, node] using fixed
    exact fixedAt.1
  have sameStore : swap.values.store original.application.current.native.config.store
      binding.field = original.application.current.native.config.store binding.field := by
    simp only [ValueSwap.store, field, Option.map_id, id_eq]
  have swappedStored : binding.get?
      (swap.phaseExecution original).application.current.native.config.store =
        some (.success value) := by
    change binding.get? (original.application.current.native.swap swap).config.store = _
    rw [State.swap_config, Config.swap_store, binding.get?_congr _ _ sameStore, stored]
  have swappedRequest : (swap.phaseExecution original).application.SeedRequest who
      ⟨(swap.phaseExecution original).application.attempt, event⟩ := request
  have swappedUnsent : ∀ message ∈ (app).outputs ((swap.phaseExecution original).recall who),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩ := by
    change ∀ message ∈ (app).outputs ((original.recall who).map swap.phaseEntry),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩
    rw [swap.phaseOutputs_entry]
    exact unsent
  obtain ⟨first, firstAccepted, firstLaw⟩ := phaseSourcePolicy_opening_of_history setup mode
    runtime leaks bounds wellFormed source plan inputs horizon scheduler trace who event payload
      binding checks outputEq codeEq node request unsent value stored values
  obtain ⟨second, secondAccepted, secondLaw⟩ := phaseSourcePolicy_opening_of_history setup mode
    runtime leaks bounds wellFormed source plan inputs horizon scheduler swappedTrace who event
      payload binding checks outputEq codeEq node swappedRequest swappedUnsent value swappedStored
        values
  obtain ⟨firstSlot, firstSlotAccepted, firstSlotLaw⟩ :=
    phaseSourceSlotPolicy_opening_of_history setup mode runtime leaks bounds wellFormed source plan
      inputs horizon scheduler trace who event payload binding checks outputEq codeEq node request
        unsent value stored values
  obtain ⟨secondSlot, secondSlotAccepted, secondSlotLaw⟩ :=
    phaseSourceSlotPolicy_opening_of_history setup mode runtime leaks bounds wellFormed source plan
      inputs horizon scheduler swappedTrace who event payload binding checks outputEq codeEq node
        swappedRequest swappedUnsent value swappedStored values
  have secondEq : second = first := Option.some.inj (secondAccepted.symm.trans firstAccepted)
  have firstSlotEq : firstSlot = first :=
    Option.some.inj (firstSlotAccepted.symm.trans firstAccepted)
  have secondSlotEq : secondSlot = first :=
    Option.some.inj (secondSlotAccepted.symm.trans firstAccepted)
  subst second
  subst firstSlot
  subst secondSlot
  exact ⟨PhaseCount.phaseOpeningResponse runtime leaks event first ⟨payload, value⟩,
    firstLaw, secondLaw, firstSlotLaw, secondSlotLaw⟩

variable (bound : (serviceGraph setup mode).EventId → Nat)
  [histories : Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).History]
  [infos : ∀ owner, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).InfoState owner)]

local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent =>
  PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent =>
  PhaseUnprotected runtime leaks bound (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

include plan inputs horizon scheduler histories infos in
private theorem opening_played (execution : (app).Execution)
    (history : (E).Trace (some ⟨remaining, some who, execution⟩)) :
    some (execution.recall who, execution.observe app who) ∈ (N).playedInformation who := by
  have present := (N).mem_playedInformation (who := who)
    (history := ⟨some ⟨remaining, some who, execution⟩, history⟩)
    (by change ¬ (remaining = 0 ∧ some who = none); simp)
  change ((menu).signals initial horizon scheduler).infoOf who history ∈ _ at present
  rw [(menu).info initial horizon scheduler who history] at present
  simpa only [ReactiveApplication.observe, ↓reduceIte] using present

include plan inputs horizon scheduler histories infos trace swappedTrace node request fixed
  unsent stored values in
/-- One original full timing plan has exactly the same whole opening law at
two genuine guarded callbacks related by a hidden swap of original private
inputs. Both WAIT options and the complete raw-noise law are retained. -/
theorem phaseTimingPlanPolicy_opening_swap
    (fallback : (owner : Player) → (N).Policy owner)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p)
    (clear : original.application.current.excluded = ∅) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        parts who (original.recall who) (original.observe app who) =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded parts who ((swap.phaseExecution original).recall who)
            ((swap.phaseExecution original).observe app who) := by
  classical
  have firstPlayed := opening_played setup mode runtime leaks bounds plan inputs horizon scheduler
    remaining who original trace
  have secondPlayed := opening_played setup mode runtime leaks bounds plan inputs horizon scheduler
    remaining who (swap.phaseExecution original) swappedTrace
  let first : Agent := ⟨who, ⟨_, firstPlayed⟩⟩
  let second : Agent := ⟨who, ⟨_, secondPlayed⟩⟩
  have firstNotFree : ¬ isFree first := by
    rintro ⟨past, view, equal, excluded⟩
    cases Option.some.inj equal
    exact excluded clear
  have secondNotFree : ¬ isFree second := by
    rintro ⟨past, view, equal, excluded⟩
    cases Option.some.inj equal
    exact excluded clear
  have sameKey : poolKey first = poolKey second :=
    (phaseTimingKey_swap_at_opening runtime leaks swap
      (serviceGraph_revealRelaxedOrdered setup mode) original who event payload binding checks
        outputEq codeEq node request fixed).symm
  have classified : isKeyed first ↔ isKeyed second :=
    phaseUnprotected_iff_of_timingKey_eq runtime leaks bound who _ _ _ _ sameKey
  have samePool : pool first = pool second :=
    freeKeyedPool_eq_of_not_free firstNotFree secondNotFree classified sameKey
  have uniform := (swap.opening_menu_law_eq_of_history bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who original
      trace swappedTrace event payload binding checks outputEq codeEq node request fixed).2
  obtain ⟨response, firstSource, secondSource, firstSlot, secondSlot⟩ :=
    opening_dispatch_laws setup mode runtime leaks bounds plan inputs horizon scheduler wellFormed
      source swap remaining who original trace swappedTrace event payload binding checks outputEq
        codeEq node request fixed unsent value stored values
  have prescribedSame :
      (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          who first.2.1).map Subtype.val =
      (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          who second.2.1).map Subtype.val := by
    simp only [phaseSourcePerturbedStrategy, mix_map]
    rw [uniform, phaseSourceSlotStrategy_map_val, phaseSourceSlotStrategy_map_val,
      phaseSourceStrategy_map_val, phaseSourceStrategy_map_val, firstSource, secondSource,
        firstSlot, secondSlot]
  have keyedSame (option : LateOption bounds.candidateCount) :
      (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          who first.2.1 option).map Subtype.val =
      (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          who second.2.1 option).map Subtype.val := by
    simp only [phaseSourceTimingComponent, mix_map]
    rw [uniform, phaseSourceSlotStrategy_map_val, phaseSourceSlotStrategy_map_val,
      phaseSourceTimingStrategy_map_val, phaseSourceTimingStrategy_map_val, firstSlot, secondSlot]
    cases option with
    | none => rfl
    | some serial =>
        obtain ⟨_, firstValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
          scheduler ((menu).toRawTrace initial horizon scheduler trace)
        obtain ⟨_, secondValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
          scheduler ((menu).toRawTrace initial horizon scheduler swappedTrace)
        rw [phaseSourceTimingPolicy_opening_eq_source setup mode runtime leaks bounds wellFormed
          source serial original firstValid who event payload binding checks outputEq codeEq
            request,
          phaseSourceTimingPolicy_opening_eq_source setup mode runtime leaks bounds wellFormed
            source serial _ secondValid who event payload binding checks outputEq codeEq request,
          firstSource, secondSource]
  have components := bind_freeKeyedComponent_map_eq_of_not_free
    (Outcome := Option (app).Action) (free := isFree) (keyed := isKeyed) (key := poolKey)
    (fun (agent : Agent) choice => mix noise noiseNonnegative noiseBounded
      ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) (PMF.pure choice))
    (fun agent => phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded agent.1 agent.2.1)
    (fun agent option => phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded agent.1 agent.2.1 option)
    (fun p => PMF.pure (parts p))
    (fun (agent : Agent) (choice : (N).Choice agent.1 agent.2.1) => choice.1)
    first second firstNotFree samePool
      prescribedSame keyedSame
  rw [PMF.pure_bind, PMF.pure_bind] at components
  rw [phaseTimingPlanPolicy_apply, dite_eq_left firstPlayed,
    phaseTimingPlanPolicy_apply, dite_eq_left secondPlayed]
  simpa only [PMF.map_comp, Function.comp_def, phaseTimingComponent, phaseTimingPool,
    first, second] using
    congrArg (PMF.map (fun response : Option (app).Action => response.getD ⟨none⟩)) components

end Vegas
