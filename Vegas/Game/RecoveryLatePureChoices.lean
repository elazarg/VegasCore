/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryLocalValueComparison
import Vegas.Game.OnePacketPrescribedCompletion

/-! # Pure wait and disclosure choices among recovery keyed components -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon NativeScheduler
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler

theorem keyedComponent_sourceNative [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (source : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (input : (application setup leaks).Info)
    (decision : (R).IsDecisionInfo who (liftInformation (runtime setup) leaks input))
    (option : LateOption slots) :
    (keyedComponent setup leaks bounds Initial horizon scheduler source scale nonnegative le_one
      ((R).agentAt ⟨liftInformation (runtime setup) leaks input, decision⟩) option).map
        (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input) =
      lateComponent setup leaks bounds (initialLaw setup) horizon NativeScheduler source scale
        nonnegative le_one who input option := by
  apply pmf_map_injective Subtype.val_injective
  rw [sourceNativeChoiceEquiv_map_val]
  have projected := keyedComponent_native setup leaks bounds horizon scheduler source scale
    nonnegative le_one ((R).agentAt ⟨liftInformation (runtime setup) leaks input, decision⟩)
    (clearInput_lift (runtime setup) leaks input) option
  rw [information_liftInformation] at projected
  exact projected

open Classical in
theorem keyed_main_value_sub_le [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) NativeScheduler]
    [∀ who, DecidableEq ((R).InfoState who)]
    (source : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (input : (application setup leaks).Info)
    (decision : (R).IsDecisionInfo who (liftInformation (runtime setup) leaks input))
    (option : LateOption slots) (choice : (N).Choice who input)
    (main : lateChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler source who
      input option = PMF.pure choice)
    (assessment : (R).BehavioralAssessment)
    {Outcome : Type*} (observe : (RP).History → Outcome) (utility : Outcome → Player → ℝ)
    {bound : ℝ} (bounded : ∀ final : (RP).History, |utility (observe final) who| ≤ bound) :
    let site : (R).InformationSite who :=
      ⟨liftInformation (runtime setup) leaks input, decision⟩
    |localValue (2 * horizon + 1) observe utility assessment site
        (PMF.pure ((sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input).symm
          choice)) -
      localValue (2 * horizon + 1) observe utility assessment site
        (keyedComponent setup leaks bounds Initial horizon scheduler source scale nonnegative le_one
          ((R).agentAt site) option)| ≤ 6 * scale * bound := by
  intro site
  let equivalent := sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input
  let value := fun found : (R).Choice who site.1 =>
    localValue (2 * horizon + 1) observe utility assessment site (PMF.pure found)
  have valueBounded : ∀ found, |value found| ≤ bound := by
    intro found
    dsimp only [value]
    rw [localValue_eq_expect_localRun]
    exact expect_abs_le_of_bounded
      (by obtain ⟨final, _⟩ := (localRun (2 * horizon + 1) assessment site
        (PMF.pure found)).support_nonempty
          exact (abs_nonneg _).trans (bounded final)) bounded
  have affine : ∀ law : PMF ((R).Choice who site.1),
      localValue (2 * horizon + 1) observe utility assessment site law = expect law value := by
    intro law
    have linear := localValue_bind (2 * horizon + 1) observe utility assessment site
      ((Recovery.onePacketMenu (runtime setup) leaks bounds).bounded Initial horizon scheduler)
      ((Recovery.onePacketMenu (runtime setup) leaks bounds).decisionRecall Initial horizon
        scheduler).actsOnceWhereItMatters law PMF.pure
    simpa only [PMF.bind_pure] using linear
  have projection : ∀ law : PMF ((R).Choice who site.1),
      expect (law.map equivalent) (fun found => value (equivalent.symm found)) =
        expect law value := by
    intro law
    rw [expect_map]
    congr 1
    funext found
    exact congrArg value (equivalent.symm_apply_apply found)
  have component := affine (keyedComponent setup leaks bounds Initial horizon scheduler source
    scale nonnegative le_one ((R).agentAt site) option)
  rw [← projection, keyedComponent_sourceNative] at component
  have pureBound := valueBounded (equivalent.symm choice)
  have mainValue : expect (lateChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler
      source who input option) (fun found => value (equivalent.symm found)) =
        value (equivalent.symm choice) := by rw [main, expect_pure]
  have near := abs_expect_slotTrembledChoice_sub_le nonnegative le_one who input
    (lateChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler source who input
      option) (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler
        who input)) (slotChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler
          source who input) (fun found => value (equivalent.symm found))
    (fun found => valueBounded _) pureBound mainValue
  rw [component, abs_sub_comm]
  exact near

open Classical in
theorem lateChoice_eq_pure_opening
    [(application setup leaks).FiniteNature (initialLaw setup) NativeScheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {who : Player} (site : (N).InformationSite who)
    (notFree : ¬ Vegas.FreeAgent setup leaks bounds horizon NativeScheduler ((N).agentAt site))
    (debtFree : SiteDebtFree setup leaks bounds horizon NativeScheduler site)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (choice : (N).Choice who site.1) {response : (application setup leaks).Action}
    (chosen : choice.1 = some response)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material)
    {handle : Handle (graph setup)} {raw : Raw L}
    (packet : material.call.packet = .opening event handle raw) (slot : Fin slots) :
    lateChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler source who site.1
      (some slot) = PMF.pure choice := by
  obtain ⟨native, seen, forced⟩ := forcedAgent_of_not_free setup leaks bounds horizon
    NativeScheduler notFree
  have owed := debtFree ⟨native, seen⟩
  obtain ⟨payload, binding, checks, outputEq, codeEq, node⟩ :=
    onePacket_opening_node member sends packet
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  obtain ⟨state, trace⟩ := native
  change (onePacketInformation setup leaks bounds horizon NativeScheduler).infoOf who trace =
    some (past, view) at seen
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    cases seen
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seen
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
  subst pastEq viewEq
  have turn := (pendingEvent_spec (setup := setup) pending).1
  have resolves := disclosureResolves_of_debtFree wellFormed trace who forced owed
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp
    (resolves _ pending who payload binding checks outputEq codeEq node)
  have responseEq := onePacket_opening_eq_disclosure trace who _ node disclosed sendsDisclosure
    response member material sends ((congrArg (Payload.event? (graph setup)) packet).trans rfl)
  have lateEq := lateChoice_reveal source trace who _ turn node slot
  have choiceEq : choice = responseChoice setup leaks bounds (initialLaw setup) horizon
      NativeScheduler who _ ((runtime setup).canonicalServiceDecision leaks who
        (execution.recall who) (execution.observe (application setup leaks) who) _
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) := by
    rw [← responseEq]
    apply Subtype.ext
    rw [chosen]
    simp only [responseChoice, member, ↓reduceDIte]
  rw [choiceEq]
  exact lateEq

end Vegas.RecoveryOnePacket
