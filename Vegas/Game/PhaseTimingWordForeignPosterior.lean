/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordFocalLaw

/-! # Original chronological source-word posterior through actual foreign channels -/

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

/-- Varying EVERY foreign complete word preserves the actual focal channel.
The full focal word stays fixed; no source likelihood or product premise is used. -/
theorem phaseTimingWordFocalLaw_eq_of_focal_word
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
    (sameFocal : firstWords focal = secondWords focal) (wanted : (N).InfoState focal) :
    phaseTimingWordFocalLaw setup mode runtime leaks bounds plan horizon scheduler bound fallback
      wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
        parts firstWords phase remaining certificate focal wanted entry =
    phaseTimingWordFocalLaw setup mode runtime leaks bounds plan horizon scheduler bound fallback
      wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
        parts secondWords phase remaining certificate focal wanted entry := by
  classical
  let kernel := fun words => phaseTimingWordFocalLaw setup mode runtime leaks bounds plan horizon
    scheduler bound fallback wellFormed (approximation.sequence n) block low 0 slotWeight
      slotNonnegative slotBounded parts words phase remaining certificate focal wanted entry
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
        have step := phaseTimingWordFocalLaw_update_foreign setup mode runtime leaks bounds plan
          maximal horizon scheduler bound finite wellFormed target approximation n fallback parts
            block low (mixed changed) owner (secondWords owner) slotWeight slotNonnegative
              slotBounded control entry current clear phase remaining installed committing lower
                upper values capacity certificate focal ownerNe wanted
        exact step.symm.trans (ih restAbsent)
  have total : mixed (Finset.univ.erase focal) = secondWords := by
    funext who
    by_cases same : who = focal
    · subst who
      simpa only [mixed, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false]
        using sameFocal
    · exact ite_eq_left (Finset.mem_erase.mpr ⟨same, Finset.mem_univ who⟩)
  have result := patches (Finset.univ.erase focal) (Finset.notMem_erase _ _)
  rw [total] at result
  exact result.symm

/-- The original source Config posterior, conditioned on the complete focal
word, is unchanged by the actual physical focal channel. The full chronological
Config prior is retained, including all failures and repeated-owner dependence. -/
theorem phaseTimingWordFocalLaw_source_posterior
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
    (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (sourceEntry : SourceProgram.Config Player L Γ) (observed : DecisionView focal Δ)
    (extra : (N).InfoState focal) :
    let original := block.prefixLaw suffix profile sourceEntry
    let kernel := fun complete : SourceProgram.Config Player L Δ =>
      phaseTimingWordFocalLaw setup mode runtime leaks bounds plan horizon scheduler bound fallback
        wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
          parts (fun who => complete.view who) phase remaining certificate focal wanted entry
    let joint := original.bind fun complete =>
      (kernel complete).map fun actualInput => (complete, actualInput)
    (∃ complete ∈ original.support, complete.view focal = observed ∧
      extra ∈ (kernel complete).support) →
    (fiberPosterior joint (fun point => (point.1.view focal, point.2)) (observed, extra)).map
      Prod.fst = fiberPosterior original (SourceProgram.Config.view focal) observed := by
  intro original kernel joint present
  apply conditional_kernel_of_fiber original (SourceProgram.Config.view focal) kernel
  · intro first _firstSupported second _secondSupported same
    exact phaseTimingWordFocalLaw_eq_of_focal_word setup mode runtime leaks bounds plan maximal
      horizon scheduler bound finite wellFormed target approximation n fallback parts block low
        (fun who => first.view who) (fun who => second.view who) slotWeight slotNonnegative
          slotBounded control entry current clear phase remaining installed committing lower upper
            values capacity certificate focal same wanted
  · exact present

end Vegas
