/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordInterventionLaw

/-! # Original source-word priors under a literal focal-policy intervention -/

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

/-- With the focal policy fixed, EVERY latent complete word can change
without changing the actual stopped focal input law. The focal word is unused. -/
theorem phaseTimingWordInterventionLaw_eq
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (firstWords secondWords : (who : Player) → DecisionView who Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (app).Control) (entry : (E).History) (current : entry.state = some control)
    (clear : control.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : control.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (certificate : (E).WellFoundedHistories) (focal : Player)
    (wanted : (N).InfoState focal) (intervention : (N).BehavioralPolicy focal) :
    phaseTimingWordInterventionLaw setup mode runtime leaks bounds plan horizon scheduler bound
      fallback
      wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
        parts firstWords phase remaining certificate focal wanted intervention entry =
    phaseTimingWordInterventionLaw setup mode runtime leaks bounds plan horizon scheduler bound
      fallback
      wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
        parts secondWords phase remaining certificate focal wanted intervention entry := by
  classical
  let kernel := fun words => phaseTimingWordInterventionLaw setup mode runtime leaks bounds
    plan horizon
    scheduler bound fallback wellFormed (approximation.sequence n) block low 0 slotWeight
      slotNonnegative slotBounded parts words phase remaining certificate focal wanted
        intervention entry
  let mixed (changed : Finset Player) (who : Player) :=
    if who ∈ changed then secondWords who else firstWords who
  have patches : ∀ changed : Finset Player, focal ∉ changed → kernel (mixed changed) =
      kernel firstWords := by
    intro changed
    induction changed using Finset.induction_on with
    | empty =>
        intro _
        simp only [mixed, Finset.notMem_empty, ite_false]
    | @insert owner changed _fresh ih =>
        intro absent
        have ownerNe : focal ≠ owner := by
          intro same
          subst owner
          exact absent (Finset.mem_insert_self _ _)
        have restAbsent : focal ∉ changed := fun member =>
          absent (Finset.mem_insert_of_mem member)
        have update : mixed (insert owner changed) =
            Function.update (mixed changed) owner (secondWords owner) := by
          funext who
          by_cases same : who = owner
          · subst who
            simp only [mixed, Finset.mem_insert_self, ite_true, Function.update_self]
          · simp only [mixed, Finset.mem_insert, same, false_or, Function.update_of_ne same]
        rw [update]
        have step := phaseTimingWordInterventionLaw_update_foreign setup mode runtime leaks
          bounds plan
          maximal horizon scheduler bound finite wellFormed target approximation n fallback parts
            block low (mixed changed) owner (secondWords owner) slotWeight slotNonnegative
              slotBounded control entry current clear phase remaining installed committing lower
                upper values capacity certificate focal ownerNe wanted intervention
        exact step.symm.trans (ih restAbsent)
  have sameProfile : GameTheory.Profile.update (sig := (N).behavioralSignature)
      (phaseTimingWordPlanProfile setup mode runtime leaks bounds plan horizon scheduler bound
        fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
          slotBounded parts (mixed (Finset.univ.erase focal))) focal intervention =
      GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingWordPlanProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts secondWords) focal intervention := by
    funext who info
    by_cases same : who = focal
    · subst who
      simp only [GameTheory.Profile.update_same]
    · simp only [GameTheory.Profile.update, Function.update_of_ne same,
        phaseTimingWordPlanProfile, mixed]
      rw [ite_eq_left (Finset.mem_erase.mpr ⟨same, Finset.mem_univ who⟩)]
  let exits : (E).History → Prop := fun history => match history.state with
    | none => True
    | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
        actual.execution.application.phases ≠ phase :: remaining
  let stopped : (E).History → Prop := fun history => exits history ∨
    ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
  let readout := fun history : (E).History =>
    @ite _ (exits history) (Classical.propDecidable (exits history)) none
      ((N).infoOf focal history.trace)
  have total : kernel (mixed (Finset.univ.erase focal)) = kernel secondWords :=
    congrArg (fun profile => ((N).runBehavioralUntil certificate profile stopped entry).map
      readout) sameProfile
  have result := patches (Finset.univ.erase focal) (Finset.notMem_erase _ _)
  exact result.symm.trans total

/-- A fixed focal-policy intervention makes the actual stopped focal channel
independent of the ORIGINAL Config prior. The prior may already be conditioned
on an accepted own-word prefix; the physical runner and full entry are unchanged. -/
theorem phaseTimingWordInterventionLaw_joint
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (app).Control) (entry : (E).History) (current : entry.state = some control)
    (clear : control.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : control.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (certificate : (E).WellFoundedHistories) (focal : Player)
    (wanted : (N).InfoState focal)
    (intervention : (N).BehavioralPolicy focal)
    (original : PMF (SourceProgram.Config Player L Δ)) :
    let kernel := fun complete : SourceProgram.Config Player L Δ =>
      phaseTimingWordInterventionLaw setup mode runtime leaks bounds plan horizon scheduler bound
        fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
          slotBounded parts (fun who => complete.view who) phase remaining certificate focal wanted
            intervention entry
    bindPairLaw original kernel = bindPairLaw original (fun _ => original.bind kernel) := by
  intro kernel
  have same (first second : SourceProgram.Config Player L Δ) : kernel first = kernel second :=
    phaseTimingWordInterventionLaw_eq setup mode runtime leaks bounds plan maximal horizon scheduler
      bound finite wellFormed target approximation n fallback parts block low
        (fun who => first.view who) (fun who => second.view who) slotWeight slotNonnegative
          slotBounded control entry current clear phase remaining installed committing lower upper
            values capacity certificate focal wanted intervention
  apply bind_congr_on_support original
  intro complete _supported
  apply congrArg (PMF.map (fun observed => (complete, observed)))
  symm
  calc
    original.bind kernel = original.bind (fun _ => kernel complete) :=
      bind_congr_on_support original fun other _ => same other complete
    _ = kernel complete := PMF.bind_const _ _

end Vegas
