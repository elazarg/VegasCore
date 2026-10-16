/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanFilledPosterior
import Vegas.Source.CommitPrefixEntryKernel
import Interaction.ReactiveProfileMixture
import Interaction.ReactiveControlOccupation

/-! # Original entry and chronological words in actual timing-plan runs

The original entry and full timing plans remain tagged through the existing
physical runner. Owned word kernels use only owned entry views; entry mixing
is retained rather than replaced by independence across hidden entries.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial
    horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (fallback : (who : Player) →
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).Policy
      who)
  (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)

local notation "family" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded

/-- The actual complete physical run retains the original source entry, its
full timing plans and the original chronological source word. The behavioral
owner prior is computed from that owner's observable entry view. -/
theorem phaseTimingWordPlan_entry_run_joint
    {Entry : Type} (entryLaw : PMF Entry) (sourceEntry : Entry → SourceProgram.Config Player L Γ)
    (entryState : Entry → (app).State) (plans : Entry → Player → ((p : Pool) → Parts p))
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix)) (count : Nat) :
    let sourceEntries := entryLaw.map sourceEntry
    let prior := fun entry who => block.ownedEntryWordKernel suffix profile sourceEntries who
      ((sourceEntry entry).view who)
    let members := fun entry who => family (plans entry who) who
    let realized := fun entry who => ((app).policyMixture (prior entry who)
      (members entry who)).policy
    let factors := fun entry (execution : (app).Execution) => independentProduct fun who =>
      ((app).policyMixture (prior entry who) (members entry who)).posterior (execution.recall who)
    (entryLaw.bind fun entry => (block.prefixLaw suffix profile (sourceEntry entry)).bind
      fun final => ((app).runRounds scheduler (fun who => members entry who (final.view who)) count
        (ReactiveApplication.Execution.initial (app) (entryState entry))).map
          (fun execution => (entry, execution, fun who => final.view who))) =
      entryLaw.bind fun entry => ((app).runRounds scheduler (realized entry) count
        (ReactiveApplication.Execution.initial (app) (entryState entry))).bind fun execution =>
          (factors entry execution).map (fun words => (entry, execution, words)) := by
  intro sourceEntries prior members realized factors
  apply bind_congr_on_support _
  intro entry supported
  have sourceSupported : sourceEntry entry ∈ sourceEntries.support :=
    (PMF.mem_support_map_iff ..).mpr ⟨entry, supported, rfl⟩
  have kernels : independentProduct (prior entry) = independentProduct
      (fun who => (block.prefixLaw suffix profile (sourceEntry entry)).map
        (SourceProgram.Config.view who)) := by
    apply congrArg independentProduct
    funext who
    exact block.ownedEntryWordKernel_at_entry suffix profile sourceEntries (sourceEntry entry)
      sourceSupported who
  have wordLaw : (block.prefixLaw suffix profile (sourceEntry entry)).map
      (fun final who => final.view who) = independentProduct (prior entry) := by
    rw [kernels]
    exact block.prefixLaw_views_product suffix profile (sourceEntry entry)
  have rounds := (app).runRounds_policyMixtures_posterior_joint scheduler (prior entry)
    (members entry) count (ReactiveApplication.Execution.initial (app) (entryState entry))
  change (independentProduct (prior entry)).bind (fun words => _) = _ at rounds
  have tagged := congrArg (PMF.map fun pair => (entry, pair.1, pair.2)) rounds
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at tagged
  refine Eq.trans ?_ tagged
  rw [← wordLaw]
  simp only [PMF.bind_map, Function.comp_def]

/-- The same original tags survive the actual next scheduler command. Its
full sampled environment branch is retained; no command-atom or hidden-entry
likelihood equality is postulated. -/
theorem phaseTimingWordPlan_entry_command_joint
    {Entry : Type} (entryLaw : PMF Entry) (sourceEntry : Entry → SourceProgram.Config Player L Γ)
    (entryState : Entry → (app).State) (plans : Entry → Player → ((p : Pool) → Parts p))
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix)) (remaining count : Nat) :
    let sourceEntries := entryLaw.map sourceEntry
    let prior := fun entry who => block.ownedEntryWordKernel suffix profile sourceEntries who
      ((sourceEntry entry).view who)
    let members := fun entry who => family (plans entry who) who
    let realized := fun entry who => ((app).policyMixture (prior entry who)
      (members entry who)).policy
    let factors := fun entry (control : (app).ProtocolState) => independentProduct fun who =>
      ((app).policyMixture (prior entry who) (members entry who)).posterior
        (control.elim [] (fun current => current.execution.recall who))
    (entryLaw.bind fun entry => (block.prefixLaw suffix profile (sourceEntry entry)).bind
      fun final => ((app).commandControlLaw scheduler
        (fun who => members entry who (final.view who)) (PMF.pure (entryState entry))
          remaining count).map (fun control => ((entry, control), fun who => final.view who))) =
      entryLaw.bind fun entry => ((app).commandControlLaw scheduler (realized entry)
        (PMF.pure (entryState entry)) remaining count).bind fun control =>
          (factors entry control).map (fun words => ((entry, control), words)) := by
  intro sourceEntries prior members realized factors
  let continuation := fun point : Entry × (app).Execution × ((who : Player) → DecisionView who Δ) =>
    (scheduler point.2.1.environmentRecall (point.2.1.observeEnvironment (app))).bind fun command =>
      (point.2.1.environmentStep (app) command).map fun active =>
        ((point.1, some (⟨remaining, command.actor? (app), active⟩ : (app).Control)), point.2.2)
  have rounds := phaseTimingWordPlan_entry_run_joint setup mode runtime leaks bounds initial
    horizon scheduler bound fallback wellFormed source block low generation slotWeight
      slotNonnegative slotBounded entryLaw sourceEntry entryState plans suffix profile count
  have moved := congrArg (fun law => law.bind continuation) rounds
  simp only [continuation, PMF.bind_bind, PMF.bind_map, Function.comp_def] at moved
  simp only [ReactiveApplication.commandControlLaw, PMF.pure_bind, PMF.map_bind,
    PMF.bind_bind, PMF.map_comp, Function.comp_def]
  refine moved.trans ?_
  apply bind_congr_on_support _
  intro entry _
  apply bind_congr_on_support _
  intro before _
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro command _
  have disintegrated := ReactiveApplication.environmentStep_disintegrate_profile
    (fun who => (app).policyMixture (prior entry who) (members entry who)) before command
      (fun active words => PMF.pure
        ((entry, some (⟨remaining, command.actor? (app), active⟩ : (app).Control)), words))
  simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, factors,
    Option.elim_some, members, prior, sourceEntries] using disintegrated

end Vegas
