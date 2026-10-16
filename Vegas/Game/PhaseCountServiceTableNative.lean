/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTableOccupation
import GameTheory.Math.Probability.ConditionalObservation

/-! # An unread original timing coin at an actual full native information fiber -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player Tag : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

variable
  (values : Tag → ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
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

local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))
local notation "coinLaw" => PhaseCount.bindingServiceCoinLaw failure timing firstNonnegative
  firstBounded timingNonnegative timingBounded rawWeight rawNonnegative rawBounded
local notation "members" => fun (tag : Tag) (owner : Player)
  (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) =>
    phaseCountServiceTapePolicy setup mode runtime leaks bounds (values tag) choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon table owner

/-- A deterministic mask removes exactly the current coin. Every remaining
coordinate of the same original table stays in the actual posterior; the
masked table is reconstructed from the two nested remaining-coordinate lists. -/
theorem phaseCountServiceTapePolicy_mask_posterior
    (tag : Tag) (who : Player) (coordinate : PhaseSeedAddress graph)
    (past : List (app).PlayerEntry)
    (inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length <
      horizon) :
    let selected : Fin horizon :=
      ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length, inside⟩
    ∃ remainder : PMF (PhaseSeedAddress graph → Fin horizon → Bool × Bool),
      (((app).policyMixture original (members tag who)).posterior past).map
        (fun table => (table coordinate selected,
          Function.update table coordinate (Function.update (table coordinate) selected
            (false, false)))) =
      (coinLaw selected.val).bind (fun coin => remainder.map (Prod.mk coin)) := by
  classical
  intro selected
  obtain ⟨remaining, split⟩ := phaseCountServiceTapePolicy_table_posterior setup mode runtime leaks
    bounds (values tag) choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    who coordinate past inside
  let outer := Equiv.piSplitAt coordinate (fun _ : PhaseSeedAddress graph =>
    Fin horizon → Bool × Bool)
  let inner := Equiv.piSplitAt selected (fun _ : Fin horizon => Bool × Bool)
  let restore := fun rest :
      ({index : Fin horizon // index ≠ selected} → Bool × Bool) ×
        ({address : PhaseSeedAddress graph // address ≠ coordinate} →
          Fin horizon → Bool × Bool) =>
    outer.symm (inner.symm ((false, false), rest.1), rest.2)
  have restored (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) :
      restore ((fun index : {index : Fin horizon // index ≠ selected} => table coordinate index),
        (fun address : {address : PhaseSeedAddress graph // address ≠ coordinate} =>
          table address)) =
        Function.update table coordinate
          (Function.update (table coordinate) selected (false, false)) := by
    funext address index
    by_cases sameAddress : address = coordinate
    · subst address
      by_cases sameIndex : index = selected
      · subst index
        simp [restore, outer, inner, Equiv.piSplitAt]
      · simp [restore, outer, inner, Equiv.piSplitAt, sameIndex]
    · simp [restore, outer, inner, Equiv.piSplitAt, sameAddress]
  refine ⟨remaining.map restore, ?_⟩
  have mapped := congrArg (PMF.map fun pair => (pair.1, restore pair.2)) split
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, restored, selected] using mapped

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (tagLaw : PMF Tag) (input : Tag → (serviceGraph setup mode).Inputs)
  (scheduler : Tag → (phaseApplication runtime leaks).Scheduler) [NeZero horizon]

local notation "originalJoint" => phaseCountServiceTableOccupation setup mode runtime leaks bounds
  values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
  slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan tagLaw
  input scheduler

/-- Conditioning the ORIGINAL table-tagged native occupation law on full
owner information leaves its current unqueried coin independent of the entire
updated retained remainder. Primitive tags, all other owners' tables and the
actual command/control remain jointly in that remainder. -/
theorem phaseCountServiceTapePolicy_native_coin_product
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (coordinate : CommitAttemptEvent graph)
    (request : PhaseRuntimeState.requests view.application.2 who coordinate)
    (present : some (past, view) ∈
      ((originalJoint).map (fun pair => (app).observe who pair.1.2)).support) :
    ∃ (bounded : coordinate.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
        coordinate.attempt.generation ≤ Fintype.card Player)
      (inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate who past).length < horizon),
    let address : PhaseSeedAddress graph := ⟨coordinate, bounded⟩
    let selected : Fin horizon :=
      ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate who past).length, inside⟩
    ∃ remainder : PMF (((Fin horizon × Tag) × (app).ProtocolState) ×
        (Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool)),
      (fiberPosterior originalJoint (fun pair => (app).observe who pair.1.2)
        (some (past, view))).map (fun pair => (pair.2 who address selected,
          (pair.1, Function.update pair.2 who (Function.update (pair.2 who) address
            (Function.update (pair.2 who address) selected (false, false)))))) =
        (coinLaw selected.val).bind (fun coin => remainder.map (Prod.mk coin)) := by
  classical
  obtain ⟨bounded, inside⟩ := phaseCountServiceTapePolicy_native_coordinate setup mode runtime leaks
    bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    plan tagLaw input scheduler who past view coordinate request present
  refine ⟨bounded, inside, ?_⟩
  intro address selected
  let law := (PMF.uniformOfFintype (Fin horizon)).bind fun time => tagLaw.bind fun tag =>
    ((app).commandControlLaw (scheduler tag)
      (fun owner => ((app).policyMixture original (members tag owner)).policy)
        (PMF.pure (PhaseRuntimeState.initial plan (input tag))) (horizon - time.val - 1)
          time.val).map fun state => ((time, tag), state)
  let observe := fun branch : (Fin horizon × Tag) × (app).ProtocolState =>
    (app).observe who branch.2
  let factors := fun (branch : (Fin horizon × Tag) × (app).ProtocolState) (owner : Player) =>
    ((app).policyMixture original (members branch.1.2 owner)).posterior
      ((app).recallAt owner branch.2)
  let conditioned := fiberPosterior law observe (some (past, view))
  let mask := fun table : PhaseSeedAddress graph → Fin horizon → Bool × Bool =>
    Function.update table address (Function.update (table address) selected (false, false))
  let masked := fun tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool =>
    Function.update tables who (mask (tables who))
  let read := fun tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool =>
    (tables who address selected, masked tables)
  have joint := phaseCountServiceTapePolicy_occupation_tables_joint setup mode runtime leaks
    bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    plan tagLaw input scheduler
  change originalJoint = law.bind (fun branch =>
    (independentProduct (factors branch)).map (Prod.mk branch)) at joint
  have marginal : (originalJoint).map Prod.fst = law := by
    rw [joint]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    have constants (branch : (Fin horizon × Tag) × (app).ProtocolState) :
        (independentProduct (factors branch)).map (fun _ => branch) = PMF.pure branch :=
      PMF.map_const _ _
    simp_rw [constants]
    exact PMF.bind_pure _
  have lawPresent : some (past, view) ∈ (law.map observe).support := by
    rw [← marginal, PMF.map_comp]
    exact present
  have shifted := fiberPosterior_bind_of_observation law
    (fun branch => (independentProduct (factors branch)).map (Prod.mk branch)) observe
    (fun pair => observe pair.1) (by
      intro branch _supported pair admitted
      obtain ⟨tables, _possible, rfl⟩ := (PMF.mem_support_map_iff ..).mp admitted
      rfl) (some (past, view)) lawPresent
  rw [← joint] at shifted
  have perBranch : ∀ branch ∈ conditioned.support,
      ∃ remainder : PMF (Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool),
        (independentProduct (factors branch)).map read =
          (coinLaw selected.val).bind (fun coin => remainder.map (Prod.mk coin)) := by
    intro branch supported
    have observed := (mem_support_fiberPosterior lawPresent supported).1
    change (app).observe who branch.2 = some (past, view) at observed
    have ownRecall : (app).recallAt who branch.2 = past := by
      cases state : branch.2 with
      | none => simp only [state, ReactiveApplication.observe] at observed; cases observed
      | some control =>
          simp only [state, ReactiveApplication.observe] at observed
          split_ifs at observed with active
          exact congrArg Prod.fst (Option.some.inj observed)
    obtain ⟨remaining, split⟩ := phaseCountServiceTapePolicy_mask_posterior setup mode runtime leaks
      bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon branch.1.2 who address past inside
    have ownSplit : (factors branch who).map (fun table => (table address selected, mask table)) =
        (coinLaw selected.val).bind (fun coin => remaining.map (Prod.mk coin)) := by
      simpa only [factors, ownRecall, mask, address, selected] using split
    let ownerSplit := Equiv.piSplitAt who
      (fun _ : Player => PhaseSeedAddress graph → Fin horizon → Bool × Bool)
    let others := independentProduct
      (fun owner : {owner : Player // owner ≠ who} => factors branch owner.val)
    let rest := remaining.bind fun table => others.map fun other => ownerSplit.symm (table, other)
    have rebuild (table) (other) : read (ownerSplit.symm (table, other)) =
        (table address selected, ownerSplit.symm (mask table, other)) := by
      apply Prod.ext
      · simp [read, ownerSplit, Equiv.piSplitAt]
      · funext owner coordinate index
        by_cases same : owner = who
        · subst owner
          simp [read, masked, ownerSplit, Equiv.piSplitAt]
        · simp [read, masked, ownerSplit, Equiv.piSplitAt, same]
    refine ⟨rest, ?_⟩
    rw [independentProduct_splitAt (factors branch) who]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (factors branch who).bind (fun table =>
      others.map (fun other => read (ownerSplit.symm (table, other)))) = _
    simp_rw [rebuild]
    have evaluated := congrArg (fun distribution => distribution.bind fun pair =>
      others.map fun other => (pair.1, ownerSplit.symm (pair.2, other))) ownSplit
    simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def]
      at evaluated
    simpa only [rest, PMF.map_bind, PMF.map_comp, Function.comp_def] using evaluated
  let residual := fun branch => if supported : branch ∈ conditioned.support then
    (perBranch branch supported).choose else PMF.pure (fun _owner _address _index => (false, false))
  let remaining := conditioned.bind fun branch => (residual branch).map (Prod.mk branch)
  refine ⟨remaining, ?_⟩
  rw [shifted, PMF.map_bind]
  calc
    _ = conditioned.bind (fun branch => (coinLaw selected.val).bind fun coin =>
        (residual branch).map fun tables => (coin, (branch, tables))) := by
      apply bind_congr_on_support
      intro branch supported
      have product := (perBranch branch supported).choose_spec
      have attached := congrArg (PMF.map fun pair => (pair.1, (branch, pair.2))) product
      have residualEq : residual branch = (perBranch branch supported).choose := by
        dsimp only [residual]
        split
        · rfl
        · rename_i missing
          exact False.elim (missing supported)
      rw [residualEq]
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, read, masked, mask] using attached
    _ = _ := by
      rw [PMF.bind_comm]
      simp only [remaining, PMF.map_bind, PMF.map_comp, Function.comp_def]

end Vegas
