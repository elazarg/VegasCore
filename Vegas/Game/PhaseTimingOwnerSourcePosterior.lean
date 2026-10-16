/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingOwnerWordChannel
import Vegas.Source.CommitPrefixWord
import GameTheoryExtensions.Math.Probability.NestedPosterior

/-! # Original entry and source-word posteriors in the actual stopped replay run

The physical stopped runner is unchanged. Its full entry and full timing plan
remain tagged jointly. Conditioning a physical focal input updates that entry
tag, while retaining the original source-word fiber law at each surviving tag.
This describes a replay reference law, not the factual common Bayes assessment.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

include maximal

/-- Conditioning the actual stopped native input keeps its original full-entry
posterior and the SAME conditional source Config at each retained entry.
Separate full owner plans may be correlated with that entry tag. -/
theorem phaseTimingOwnerWordProfile_reference_posterior
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    {Entry : Type} (entryLaw : PMF Entry) (parts : Entry → Player → (p : Pool) → Parts p)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (profile : Entry → BehavioralProfile ((earlier.append later).prepend suffix))
    (sourceEntry : Entry → SourceProgram.Config Player L Γ) (focal : Player)
    (sourceView : Entry → DecisionView focal Δ)
    (low : Nat) (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight)
    (slotBounded : slotWeight ≤ 1)
    (control : Entry → (app).Control) (entry : Entry → (E).History)
    (current : ∀ index ∈ entryLaw.support, (entry index).state = some (control index))
    (clear : ∀ index ∈ entryLaw.support,
      (control index).execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : ∀ index ∈ entryLaw.support,
      (control index).execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment) (lower : phase.low = low)
    (upper : phase.high = low + (earlier.append later).length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (certificate : (E).WellFoundedHistories) (wanted : (N).InfoState focal)
    (intervention : Entry → (N).BehavioralPolicy focal)
    (observed : (N).InfoState focal)
    (sourcePresent : ∀ index ∈ entryLaw.support, sourceView index ∈
      (((earlier.append later).prefixLaw suffix (profile index) (sourceEntry index)).map
        (fun complete => later.entryView focal (complete.view focal))).support) :
    let reference := fun index => fiberPosterior
      ((earlier.append later).prefixLaw suffix (profile index) (sourceEntry index))
      (fun complete => later.entryView focal (complete.view focal)) (sourceView index)
    let exits : (E).History → Prop := fun history => match history.state with
      | none => True
      | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining
    let stopped : (E).History → Prop := fun history => exits history ∨
      ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
    let readout := fun history : (E).History =>
      @ite _ (exits history) (Classical.propDecidable (exits history)) none
        ((N).infoOf focal history.trace)
    let physical := fun index (complete : SourceProgram.Config Player L Ξ) =>
      ((N).runBehavioralUntil certificate
        (GameTheory.Profile.update (sig := (N).behavioralSignature)
          (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
            fallback wellFormed (approximation.sequence n) (earlier.append later) low 0 slotWeight
              slotNonnegative slotBounded (parts index) (fun who => complete.view who)) focal
                (intervention index)) stopped (entry index)).map readout
    let joint := entryLaw.bind fun index => (reference index).bind fun complete =>
      (physical index complete).map fun output => (output, (index, complete))
    let outer := entryLaw.bind fun index =>
      ((reference index).bind (physical index)).map fun output => (output, index)
    observed ∈ (entryLaw.bind fun index => (reference index).bind (physical index)).support →
    (fiberPosterior joint Prod.fst observed).map Prod.snd =
        ((fiberPosterior outer Prod.fst observed).map Prod.snd).bind
          (fun index => (reference index).map (Prod.mk index)) ∧
      ∀ index ∈ ((fiberPosterior outer Prod.fst observed).map Prod.snd).support,
        ∀ complete ∈ (reference index).support,
          later.entryView focal (complete.view focal) = sourceView index ∧
            complete ∈ ((earlier.append later).prefixLaw suffix
              (profile index) (sourceEntry index)).support := by
  classical
  intro reference exits stopped readout physical joint outer present
  let output := fun index => (reference index).bind (physical index)
  let kernel := fun index => bindPairLaw (output index) (fun _ => reference index)
  have factors (index : Entry) (supported : index ∈ entryLaw.support) :
      bindPairLaw (reference index) (physical index) =
        bindPairLaw (reference index) (fun _ => output index) := by
    have same (first second : SourceProgram.Config Player L Ξ) :
        physical index first = physical index second := by
      have channel := phaseTimingOwnerWordProfile_channel_eq setup mode runtime leaks bounds plan
        maximal horizon scheduler bound finite wellFormed target approximation n fallback
          (parts index) (earlier.append later) low (fun who => first.view who)
            (fun who => second.view who) slotWeight slotNonnegative slotBounded (control index)
              (entry index) (current index supported) (clear index supported) phase remaining
                (installed index supported) committing lower upper values capacity certificate
                  focal wanted (intervention index)
      exact channel
    apply bind_congr_on_support
    intro complete _
    apply congrArg (PMF.map (fun signal => (complete, signal)))
    symm
    calc
      output index = (reference index).bind (fun _ => physical index complete) :=
        bind_congr_on_support _ (fun other _ => same other complete)
      _ = _ := PMF.bind_const _ _
  have row (index : Entry) (supported : index ∈ entryLaw.support) :
      (reference index).bind (fun complete =>
        (physical index complete).map fun signal => (signal, complete)) = kernel index := by
    have tagged := congrArg (PMF.map Prod.swap) (factors index supported)
    rw [bindPairLaw_const_map_swap] at tagged
    simpa only [bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def,
      Prod.swap_prod_mk, kernel] using tagged
  have jointEq : joint = (bindPairLaw entryLaw kernel).map
      (fun pair => (pair.2.1, (pair.1, pair.2.2))) := by
    simp only [joint, bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support
    intro index supported
    have tagged := congrArg (PMF.map fun pair => (pair.1, (index, pair.2))) (row index supported)
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using tagged
  have kernelOutput (index : Entry) : (kernel index).map Prod.fst = output index :=
    bindPairLaw_map_fst _ _
  have outerEq : outer = entryLaw.bind fun index =>
      ((kernel index).map Prod.fst).map fun signal => (signal, index) := by
    simp only [outer, kernelOutput, output]
  have marginal : outer.map Prod.fst = entryLaw.bind output := by
    simp only [outer, PMF.map_bind, PMF.map_comp, output, Function.comp_def]
    apply congrArg (PMF.bind entryLaw)
    funext index
    apply congrArg (PMF.bind (reference index))
    funext complete
    exact PMF.map_id _
  have outerPresent : observed ∈ (outer.map Prod.fst).support := by
    rw [marginal]
    exact present
  constructor
  · rw [jointEq, outerEq]
    have tower := fiberPosterior_hierarchical_pair entryLaw kernel observed (by
      simpa only [kernelOutput] using present)
    dsimp only at tower
    rw [tower]
    apply bind_congr_on_support
    intro index _
    exact congrArg (PMF.map (Prod.mk index))
      (fiberPosterior_snd_bindPairLaw_const (output index) (reference index) observed)
  · intro index indexSupported complete supported
    obtain ⟨pair, pairSupported, equal⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp indexSupported
    have originalSupported := (mem_support_fiberPosterior outerPresent pairSupported).2
    obtain ⟨old, oldSupported, resultSupported⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ originalSupported)
    obtain ⟨signal, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp resultSupported
    have sameIndex : old = index := (congrArg Prod.snd same).trans equal
    subst old
    exact mem_support_fiberPosterior (sourcePresent index oldSupported) supported

end Vegas
