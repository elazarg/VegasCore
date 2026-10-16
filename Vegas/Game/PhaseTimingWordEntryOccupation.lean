/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordEntry

/-! # Mixed-entry conditioning at actual command occupations

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

/-- Uniformly selecting an actual command index preserves the complete
original entry, selected finite plans and chronological source words jointly.
Its marginal command law uses the real entry-conditioned behavioral policies. -/
theorem phaseTimingWordPlan_entry_occupation_joint [NeZero horizon]
    {Entry : Type} (entryLaw : PMF Entry) (sourceEntry : Entry → SourceProgram.Config Player L Γ)
    (entryState : Entry → (app).State)
    (plans : Entry → Player → ((p : Pool) → Parts p))
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix)) :
    let sourceEntries := entryLaw.map sourceEntry
    let prior := fun entry who => block.ownedEntryWordKernel suffix profile sourceEntries who
      ((sourceEntry entry).view who)
    let members := fun entry who => family (plans entry who) who
    let realized := fun entry who => ((app).policyMixture (prior entry who)
      (members entry who)).policy
    let factors := fun entry (control : (app).ProtocolState) => independentProduct fun who =>
      ((app).policyMixture (prior entry who) (members entry who)).posterior
        (control.elim [] (fun current => current.execution.recall who))
    let law := (PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
      ((app).commandControlLaw scheduler (realized entry) (PMF.pure (entryState entry))
        (horizon - time.val - 1) time.val).map (fun control => ((time, entry), control))
    ((PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
      (block.prefixLaw suffix profile (sourceEntry entry)).bind fun final =>
        ((app).commandControlLaw scheduler (fun who => members entry who (final.view who))
          (PMF.pure (entryState entry)) (horizon - time.val - 1) time.val).map
            (fun control => (((time, entry), control), fun who => final.view who))) =
      law.bind fun branch => (factors branch.1.2 branch.2).map (Prod.mk branch) := by
  intro sourceEntries prior members realized factors law
  simp only [law, PMF.bind_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro time _
  have command := phaseTimingWordPlan_entry_command_joint setup mode runtime leaks bounds initial
    horizon scheduler bound fallback wellFormed source block low generation slotWeight
      slotNonnegative slotBounded entryLaw sourceEntry entryState plans suffix profile
        (horizon - time.val - 1) time.val
  have tagged := congrArg (PMF.map fun pair =>
    (((time, pair.1.1), pair.1.2), pair.2)) command
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, members, realized, factors, prior,
    sourceEntries] using tagged

/-- Conditioning the actual source-word implementation on full focal
information retains the genuine reweighted entry/index/control law. Only the
private word factors are updated by their complete actual own recalls.
No source/native Bayes identification or entry independence is used. -/
theorem phaseTimingWordPlan_entry_occupation_posterior [NeZero horizon]
    {Entry : Type} (entryLaw : PMF Entry) (sourceEntry : Entry → SourceProgram.Config Player L Γ)
    (entryState : Entry → (app).State)
    (plans : Entry → Player → ((p : Pool) → Parts p))
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix)) (who : Player)
    (observed : Option (List (app).PlayerEntry × (app).PlayerView)) :
    let sourceEntries := entryLaw.map sourceEntry
    let prior := fun entry owner => block.ownedEntryWordKernel suffix profile sourceEntries owner
      ((sourceEntry entry).view owner)
    let members := fun entry owner => family (plans entry owner) owner
    let realized := fun entry owner => ((app).policyMixture (prior entry owner)
      (members entry owner)).policy
    let factors := fun entry (control : (app).ProtocolState) => independentProduct fun owner =>
      ((app).policyMixture (prior entry owner) (members entry owner)).posterior
        (control.elim [] (fun current => current.execution.recall owner))
    let law := (PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
      ((app).commandControlLaw scheduler (realized entry) (PMF.pure (entryState entry))
        (horizon - time.val - 1) time.val).map (fun control => ((time, entry), control))
    let original := (PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
      (block.prefixLaw suffix profile (sourceEntry entry)).bind fun final =>
        ((app).commandControlLaw scheduler (fun owner => members entry owner (final.view owner))
          (PMF.pure (entryState entry)) (horizon - time.val - 1) time.val).map
            (fun control => (((time, entry), control), fun owner => final.view owner))
    let information := fun branch : (Fin horizon × Entry) × (app).ProtocolState =>
      (app).observe who branch.2
    observed ∈ (law.map information).support →
      let conditioned := fiberPosterior original (fun point => information point.1) observed
      let occupied := fiberPosterior law information observed
      conditioned = occupied.bind (fun branch =>
          (factors branch.1.2 branch.2).map (Prod.mk branch)) ∧
        conditioned.map Prod.fst = occupied ∧
          ∀ point ∈ conditioned.support, point.1.1.2 ∈ entryLaw.support ∧
            ∃ final ∈ (block.prefixLaw suffix profile (sourceEntry point.1.1.2)).support,
              ∀ owner, final.view owner = point.2 owner := by
  intro sourceEntries prior members realized factors law original information present conditioned
    occupied
  have joint := phaseTimingWordPlan_entry_occupation_joint setup mode runtime leaks bounds initial
    horizon scheduler bound fallback wellFormed source block low generation slotWeight
      slotNonnegative slotBounded entryLaw sourceEntry entryState plans suffix profile
  change original = law.bind (fun branch =>
    (factors branch.1.2 branch.2).map (Prod.mk branch)) at joint
  have conditionedLaw := fiberPosterior_bind_of_observation law
    (fun branch => (factors branch.1.2 branch.2).map (Prod.mk branch)) information
      (fun point => information point.1) (by
        intro branch _ point supported
        obtain ⟨words, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
        rfl) observed present
  rw [← joint] at conditionedLaw
  have marginal : conditioned.map Prod.fst = occupied := by
    rw [show conditioned = occupied.bind (fun branch =>
      (factors branch.1.2 branch.2).map (Prod.mk branch)) from conditionedLaw]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (occupied.bind fun branch =>
      (factors branch.1.2 branch.2).map (Function.const _ branch)) = occupied
    simp only [PMF.map_const, PMF.bind_pure]
  have originalObservation : original.map (fun point => information point.1) =
      law.map information := by
    rw [joint]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (law.bind fun branch => (factors branch.1.2 branch.2).map
      (Function.const _ (information branch))) = law.map information
    simp only [PMF.map_const]
    rfl
  have originalPresent : observed ∈
      (original.map (fun point => information point.1)).support := by
    rw [originalObservation]
    exact present
  refine ⟨conditionedLaw, marginal, ?_⟩
  intro point possible
  have actual := (mem_support_fiberPosterior originalPresent possible).2
  obtain ⟨time, _timePossible, row⟩ := (PMF.mem_support_bind_iff ..).mp actual
  obtain ⟨entry, entryPossible, sourceRow⟩ := (PMF.mem_support_bind_iff ..).mp row
  obtain ⟨final, sourcePossible, controlRow⟩ := (PMF.mem_support_bind_iff ..).mp sourceRow
  obtain ⟨control, _controlPossible, equal⟩ := (PMF.mem_support_map_iff ..).mp controlRow
  have entryEq : entry = point.1.1.2 := congrArg (fun output => output.1.1.2) equal
  refine ⟨entryEq ▸ entryPossible, final, entryEq ▸ sourcePossible, ?_⟩
  intro owner
  exact congrFun (congrArg Prod.snd equal) owner

end Vegas
