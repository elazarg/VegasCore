/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordInterventionLaw
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveRecallReplay
import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual word channels with separate original full plans for every owner -/

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

/-- Restrict the globally menu-legal member policies to the actual original
finite game. Every owner retains its separate original full timing plan and own word. -/
def phaseTimingOwnerWordProfile {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p) (words : (who : Player) → DecisionView who Δ) :
    (who : Player) → (N).BehavioralPolicy who := fun who =>
  (menu).restrictPolicy initial horizon scheduler who
    (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
      fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
        (parts who) who (words who))

include maximal

open Classical in
/-- Changing one foreign word preserves the genuine stopped full focal input
law with each owner's separate original full timing plan retained. -/
theorem phaseTimingOwnerWordProfile_update_foreign_channel
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : Player → (p : Pool) → Parts p) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (words : (who : Player) → DecisionView who Δ) (owner : Player)
    (replacement : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (app).Control) (entry : (E).History) (current : entry.state = some control)
    (clear : control.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : control.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (certificate : (E).WellFoundedHistories) (focal : Player) (different : focal ≠ owner)
    (wanted : (N).InfoState focal) (intervention : (N).BehavioralPolicy focal) :
    let exits : (E).History → Prop := fun history => match history.state with
      | none => True
      | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining
    let stopped : (E).History → Prop := fun history => exits history ∨
      ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
    let readout := fun history : (E).History =>
      @ite _ (exits history) (Classical.propDecidable (exits history)) none
        ((N).infoOf focal history.trace)
    let evaluate := fun words => ((N).runBehavioralUntil certificate
      (GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts words) focal intervention) stopped entry).map readout
    evaluate words = evaluate (Function.update words owner replacement) := by
  intro exits stopped readout evaluate
  classical
  let ordinary := phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler
    bound fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
      slotBounded parts words
  let profile := GameTheory.Profile.update (sig := (N).behavioralSignature)
    ordinary focal intervention
  have changedBase : GameTheory.Profile.update (sig := (N).behavioralSignature)
      ordinary owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded (parts owner) owner replacement)) =
      phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
        fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
          slotBounded parts (Function.update words owner replacement) := by
    funext who info
    by_cases same : who = owner
    · subst who
      simp only [GameTheory.Profile.update_same, phaseTimingOwnerWordProfile, Function.update_self]
    · simp only [GameTheory.Profile.update, Function.update_of_ne same, ordinary,
        phaseTimingOwnerWordProfile]
  have changed : GameTheory.Profile.update (sig := (N).behavioralSignature) profile owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded (parts owner) owner replacement)) =
      GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts (Function.update words owner replacement)) focal intervention := by
    change GameTheory.Profile.update (sig := (N).behavioralSignature)
      (GameTheory.Profile.update (sig := (N).behavioralSignature)
        ordinary focal intervention) owner _ = _
    rw [GameTheory.Profile.update_comm (sig := (N).behavioralSignature) ordinary different,
      changedBase]
  have sameOwner : profile owner =
      (menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded (parts owner) owner (words owner)) :=
    GameTheory.Profile.update_of_ne (sig := (N).behavioralSignature) ordinary intervention
      different.symm
  have original : GameTheory.Profile.update (sig := (N).behavioralSignature) profile owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded (parts owner) owner (words owner))) = profile := by
    rw [← sameOwner]
    exact GameTheory.Profile.update_eq_self _ _
  have channel := phase_timing_plan_word_channel_of_history setup mode runtime leaks bounds plan
    maximal horizon scheduler bound finite wellFormed target approximation n fallback (parts owner)
      profile
      owner block low (words owner) replacement slotWeight slotNonnegative slotBounded control entry
        current clear phase remaining installed committing lower upper values capacity certificate
          focal different wanted
  dsimp only at channel
  rw [original, changed] at channel
  have projected := congrArg
    (PMF.map (fun observed => observed.bind fun row => row.2.2.2.2.2)) channel
  simp only [PMF.map_comp, Function.comp_def] at projected
  have flatten (history : (E).History) :
      ((if (match history.state with
          | none => True
          | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
              actual.execution.application.phases ≠ phase :: remaining) then none else
        history.state.map fun actual : (app).Control =>
          (actual.remaining, actual.actor, phaseExternalObservation runtime leaks owner
            actual.execution,
            phaseOperationalView runtime leaks (actual.execution.observe app owner),
            (actual.execution.recall owner).map (fun record : (app).PlayerEntry =>
              (phaseOperationalView runtime leaks record.beforeView, record.emitted)),
            (N).infoOf focal history.trace)).bind fun row => row.2.2.2.2.2) =
        if (match history.state with
          | none => True
          | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
              actual.execution.application.phases ≠ phase :: remaining) then none else
          (N).infoOf focal history.trace := by
    by_cases exits : match history.state with
      | none => True
      | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining
    · simp only [exits, ite_true, Option.bind_none]
    · have nonempty : history.state ≠ none := by
        intro absent
        apply exits
        simp only [absent]
      obtain ⟨actual, state⟩ := Option.ne_none_iff_exists'.mp nonempty
      have notExit : ¬(actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining) := by
        simpa only [state] using exits
      simp only [state, notExit, ite_false, Option.map_some, Option.bind_some]
  exact (map_congr_on_support _ (fun history _ => flatten history)).symm.trans
    (projected.trans (map_congr_on_support _ (fun history _ => flatten history)))


open Classical in
/-- With the focal policy fixed, every complete word may vary without changing
the genuine stopped full focal input law. Separate full owner plans remain
fixed throughout; no random-carrier identification is used. -/
theorem phaseTimingOwnerWordProfile_channel_eq
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : Player → (p : Pool) → Parts p) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
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
    let exits : (E).History → Prop := fun history => match history.state with
      | none => True
      | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining
    let stopped : (E).History → Prop := fun history => exits history ∨
      ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
    let readout := fun history : (E).History =>
      @ite _ (exits history) (Classical.propDecidable (exits history)) none
        ((N).infoOf focal history.trace)
    let evaluate := fun words => ((N).runBehavioralUntil certificate
      (GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts words) focal intervention) stopped entry).map readout
    evaluate firstWords = evaluate secondWords := by
  intro exits stopped readout evaluate
  classical
  let kernel := evaluate
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
        have step := phaseTimingOwnerWordProfile_update_foreign_channel setup mode runtime leaks
          bounds plan
          maximal horizon scheduler bound finite wellFormed target approximation n fallback parts
            block low (mixed changed) owner (secondWords owner) slotWeight slotNonnegative
              slotBounded control entry current clear phase remaining installed committing lower
                upper values capacity certificate focal ownerNe wanted intervention
        exact step.symm.trans (ih restAbsent)
  have sameProfile : GameTheory.Profile.update (sig := (N).behavioralSignature)
      (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
        fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
          slotBounded parts (mixed (Finset.univ.erase focal))) focal intervention =
      GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts secondWords) focal intervention := by
    funext who info
    by_cases same : who = focal
    · subst who
      simp only [GameTheory.Profile.update_same]
    · simp only [GameTheory.Profile.update, Function.update_of_ne same,
        phaseTimingOwnerWordProfile, mixed]
      rw [ite_eq_left (Finset.mem_erase.mpr ⟨same, Finset.mem_univ who⟩)]
  have total : kernel (mixed (Finset.univ.erase focal)) = kernel secondWords :=
    congrArg (fun profile => ((N).runBehavioralUntil certificate profile stopped entry).map
      readout) sameProfile
  have result := patches (Finset.univ.erase focal) (Finset.notMem_erase _ _)
  exact result.symm.trans total


end Vegas
