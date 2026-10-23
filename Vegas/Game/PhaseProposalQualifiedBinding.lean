/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.Likelihood
import Vegas.Game.QualifiedBinding.StoppedPayoff
import Vegas.Game.AsyncDeviationForeign
import Vegas.Game.ServiceWithheldForfeit
import GameTheoryExtensions.Math.Probability.PresentConditional

/-! # Qualified binding transport at the original native information -/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)

variable (values : ∀ who (key : setup.ProposalRecoveryComponent who),
  PMF (setup.CommitRecoveryValueChoice who key.1))


open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

section NativeReconstruction

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

open Classical in
theorem qualified_annotation_pushforward
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site past view
      event payload cleanSite.binding)
    (pairLaw : ForeignPosteriorCutPair setup values implementation) :
    let sourceSite := source.site
    let encode := source.encode
    let anchor := source.anchor
    let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who anchor.trace))
    let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
      who anchor.trace).1
    let coefficient := mechanicalCoefficient setup implementation
      ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
    let sourceMass := ∑' h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1,
      if setup.proposalRecoveryForeignGood who h.val then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile h.val else 0
    0 < own ∧ own ≠ ⊤ ∧ 0 < classes ∧ classes ≠ ⊤ ∧
    0 < sourceMass ∧ sourceMass ≠ ⊤ ∧
    0 < ∑' index, coefficient index ∧ (∑' index, coefficient index) ≠ ⊤ ∧
    (∀ history : setup.proposalRecoveryProtocol.History,
      setup.proposalRecoveryForeignGood who history →
      setup.proposalRecoveryModel.infoOf who history.trace = sourceSite.1 →
      own = ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who history.trace)) ∧
      classes = (setup.proposalRecoveryForeignProducts values scale sourceBad scale
        who history.trace).1) ∧
    ∀ (index : MechanicalIndex setup implementation who) (value : L.Val payload)
      (cut completed : setup.proposalRecoveryProtocol.History),
      own * classes * annotatedForcedBlockWeight setup values implementation operational
        sourceProfile nativeProfile who site index event payload value cut completed =
      coefficient index *
        (if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
          if setup.proposalRecoveryForeignGood who cut then
            setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
              sourceForcedBlock setup values who cut (same.symm ▸ encode value) completed
          else 0
        else 0) := by
  intro sourceSite encode anchor own classes coefficient sourceMass
  have rectangle : ∀ (index : MechanicalIndex setup implementation who)
      (value : L.Val payload) (cut completed : setup.proposalRecoveryProtocol.History),
      own * classes * annotatedForcedBlockWeight setup values implementation operational
        sourceProfile nativeProfile who site index event payload value cut completed =
      coefficient index *
        (if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
          if setup.proposalRecoveryForeignGood who cut then
            setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
              sourceForcedBlock setup values who cut (same.symm ▸ encode value) completed
          else 0
        else 0) := by
    intro index value cut completed
    let density :=
      if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
        if setup.proposalRecoveryForeignGood who cut then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
            sourceForcedBlock setup values who cut (same.symm ▸ encode value) completed
        else 0
      else 0
    by_cases zero : density = 0
    · have vanished := annotated_forced_block_zero_of_source_zero setup values implementation
        operational scale sourceBad scalePositive scaleBelow sourceBadPositive sourceBadBelow
        fullValues sourceProfile nativeProfile sourcePrescribed who site past view siteEq event
        payload cleanSite source index value cut completed zero
      change own * classes * annotatedForcedBlockWeight setup values implementation operational
        sourceProfile nativeProfile who site index event payload value cut completed =
          coefficient index * density
      rw [vanished, zero, mul_zero, mul_zero]
    · by_cases noMechanics : coefficient index = 0
      · have vanished := annotated_forced_block_zero_of_coefficient_zero setup values implementation
          operational scale nativeBad scalePositive scaleBelow nativeBadPositive nativeBadBelow
            fullValues sourceProfile nativeProfile nativePrescribed who site index event payload
              value cut completed noMechanics
        change own * classes * annotatedForcedBlockWeight setup values implementation operational
          sourceProfile nativeProfile who site index event payload value cut completed =
            coefficient index * density
        rw [vanished, noMechanics, mul_zero, zero_mul]
      · obtain ⟨law, balanced⟩ :
            ∃ law : PMF ((nativeModel).InformationHistory who site.1),
              ∀ history : (nativeModel).InformationHistory who site.1,
                own * classes *
                  (if mechanicalWord setup implementation who history.val.trace = index.1.val then
                    ∑' entry : setup.proposalRecoveryProtocol.History,
                      ∑' word : SourceProgram.History Player L,
                        annotatedPrefixWeight setup values implementation operational sourceProfile
                            nativeProfile who history.val index.2 entry word *
                          (if bindingAdmissionBit setup implementation who event history.val index.2
                            then 1 else 0) *
                          sourceForcedBlockJoint setup values implementation who history.val event
                            payload entry word value (cut, completed)
                  else 0) = coefficient index * density * law history := by
          exact qualified_annotation_native_balance setup values implementation operational
            scale sourceBad nativeBad scalePositive scaleBelow sourceBadPositive sourceBadBelow
              nativeBadPositive nativeBadBelow fullValues sourceProfile nativeProfile
                sourcePrescribed nativePrescribed who site past view siteEq event payload cleanSite
                  qualified source pairLaw index value cut completed noMechanics zero
        exact qualified_annotation_rectangle_of_native_atoms setup values implementation operational
          scale sourceBad nativeBad sourceProfile nativeProfile who site past view event payload
            cleanSite.binding source index value cut completed law balanced
  obtain ⟨ownPositive, ownFinite, classesPositive, classesFinite, massPositive, massFinite,
      coefficientPositive, coefficientFinite, constant, _normalization⟩ :=
    qualified_annotation_normalization setup values implementation operational scale sourceBad
      nativeBad scalePositive scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile
      nativeProfile sourcePrescribed who site past view siteEq event payload cleanSite qualified
      source rectangle
  exact ⟨ownPositive, ownFinite, classesPositive, classesFinite, massPositive, massFinite,
    coefficientPositive, coefficientFinite, constant, rectangle⟩

open Classical in
theorem qualified_reconstruction
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event) :
    ∃ (sourceSite : setup.proposalRecoveryModel.InformationSite who)
      (encode : L.Val payload → setup.proposalRecoveryModel.Choice who sourceSite.1)
      (anchor : setup.proposalRecoveryProtocol.History),
      setup.proposalRecoveryModel.infoOf who anchor.trace = sourceSite.1 ∧
      setup.proposalRecoveryForeignGood who anchor ∧
      0 < setup.proposalRecoveryModel.historyReachWeight sourceProfile anchor ∧
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
          implementation.plan who event past view =
        some (setup.proposalRecoveryQuery who sourceSite.1) ∧
      (∀ value, phaseRecoveryBindingData setup .concurrent event who payload cleanSite.binding
        ((encode value).val.map (fun move => move.semantic)) = (.success value, false)) ∧
      sourceUnflaggedStrategy setup values who sourceSite.1 =
        (values who (setup.proposalRecoveryQuery who sourceSite.1)).map (fun sampled =>
          encode (phaseRecoveryDomainValue setup .concurrent event who payload cleanSite.binding
            sampled.val.val)) ∧
      let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who anchor.trace))
      let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
        who anchor.trace).1
      let coefficient := mechanicalCoefficient setup implementation
        ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
      let sourceMass := ∑' h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1,
        if setup.proposalRecoveryForeignGood who h.val then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile h.val else 0
      0 < own ∧ own ≠ ⊤ ∧ 0 < classes ∧ classes ≠ ⊤ ∧
      0 < sourceMass ∧ sourceMass ≠ ⊤ ∧
      0 < ∑' index, coefficient index ∧ (∑' index, coefficient index) ≠ ⊤ ∧
      (∀ history : setup.proposalRecoveryProtocol.History,
        setup.proposalRecoveryForeignGood who history →
        setup.proposalRecoveryModel.infoOf who history.trace = sourceSite.1 →
        own = ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
          (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who history.trace)) ∧
        classes = (setup.proposalRecoveryForeignProducts values scale sourceBad scale
          who history.trace).1) ∧
      ∀ (index : MechanicalIndex setup implementation who) (value : L.Val payload)
        (cut completed : setup.proposalRecoveryProtocol.History),
        own * classes * annotatedForcedBlockWeight setup values implementation operational
          sourceProfile nativeProfile who site index event payload value cut completed =
        coefficient index *
          (if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
            if setup.proposalRecoveryForeignGood who cut then
              setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
                sourceForcedBlock setup values who cut (same.symm ▸ encode value) completed
            else 0
          else 0) := by
  obtain ⟨source⟩ := qualified_source_site setup values implementation operational
      scale sourceBad nativeBad
      scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow
      fullValues sourceProfile nativeProfile sourcePrescribed nativePrescribed who site past view
      siteEq event payload cleanSite qualified
  refine ⟨source.site, source.encode, source.anchor, source.anchorInfo, source.anchorGood,
    source.anchorReach, source.query, source.encoded, source.ordinary, ?_⟩
  exact qualified_annotation_pushforward setup values implementation operational
      scale sourceBad nativeBad
      scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow
      fullValues sourceProfile nativeProfile sourcePrescribed nativePrescribed who site past view
      siteEq event payload cleanSite qualified source
    (foreign_posterior_cut_pair setup values implementation)

end NativeReconstruction

section QualifiedPayoffAttachment

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler
local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

open Classical in
/-- The actual qualified native payoff numerator equals
its full annotated source continuation numerator, including the unqualified complement. -/
theorem annotated_stopped_payoff
    (operational : implementation.Operational)
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (badPositive : 0 < sourceBad.val) (badBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (native : (nativeModel).BehavioralAssessment)
    (nativeMixed : native.IsFullyMixed)
    (nativeBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (nativeModel) native ((nativeMenu).decisionInformationAntichain nativeInitial
        implementation.horizon implementation.scheduler))
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView)
    (information : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (value : L.Val payload)
    (choice : (nativeModel).Choice who site.1)
    (proper : ∃ (serial : Nat)
        (material : WitnessedSubmission (serviceGraph setup .concurrent)),
      choice.1 = some ⟨some material⟩ ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (outcome : Option ℝ)
    (pairLaw : ForeignPosteriorCutPair setup values implementation) :
    let informationMass := (nativeModel).informationMass native.strategy who site
    let admittedMass := qualifiedPrefixMass setup implementation native.strategy who site event
    informationMass *
        qualifiedPayoff setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan implementation.prior values native
          who site choice utility excludedPayoff outcome =
      (∑' index : MechanicalIndex setup implementation who,
        ∑' cut : setup.proposalRecoveryProtocol.History,
          ∑' completed : setup.proposalRecoveryProtocol.History,
            annotatedForcedBlockWeight setup values implementation operational sourceProfile
              native.strategy who site index event payload value cut completed *
              ((setup.proposalRecoveryModel.runBehavioralTerminalFrom
                setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
                (sourceUnflaggedStrategy setup values) completed).map fun terminal =>
                  some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))
                outcome) +
      (informationMass - admittedMass) * (PMF.pure (none : Option ℝ)) outcome
 := by
  classical
  intro informationMass admittedMass
  let initializer := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initializer = nativeInitial := PMF.map_comp _ _ _
  dsimp only [initializer] at initialEq
  have literalInitialEq :
      (setup.initialLaw.map fun draw =>
        PhaseRuntimeState.initial implementation.plan (encodeInputs draw)) = nativeInitial := by
    simpa only [PMF.map_comp, Function.comp_def] using initialEq
  obtain ⟨serial, material, selectedChoice, packet, prepared⟩ := proper
  let reward := fun (_cut completed : setup.proposalRecoveryProtocol.History) =>
    ((setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (sourceUnflaggedStrategy setup values) completed).map
      (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal)))
        outcome
  let row := fun (history : (nativeModel).InformationHistory who site.1)
      (tape : ReservedEpoch.Tape Player implementation.tapeLength) =>
    ∑' cut : setup.proposalRecoveryProtocol.History,
      ∑' completed : setup.proposalRecoveryProtocol.History,
        ∑' target : setup.proposalRecoveryProtocol.History,
          ∑' word : SourceProgram.History Player L,
            annotatedPrefixWeight setup values implementation operational sourceProfile
              native.strategy
              who history.val tape target word *
            (if bindingAdmissionBit setup implementation who event history.val tape then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who history.val event payload target
              word value (cut, completed) * reward cut completed
  let guard := fun history : (nativeModel).InformationHistory who site.1 =>
    (∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner history.val) ∧
      history.val.state.elim True (fun control => who ∉
        control.execution.application.current.excluded)
  let failure := fun history : (nativeModel).InformationHistory who site.1 =>
    if guard history then
      ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
        prefixTapeLaw setup implementation history.val tape *
          if bindingAdmissionBit setup implementation who event history.val tape then 0 else 1
    else 1
  have massPositive : 0 < informationMass :=
    (nativeModel).informationMass_pos_of_fullSupport native.strategy nativeMixed who site
  have massFinite : informationMass ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((nativeModel).informationMass_le_one native.strategy who site
      ((nativeMenu).decisionInformationAntichain nativeInitial implementation.horizon
        implementation.scheduler who site))
  have annotation := annotated_continuation_sum setup values implementation operational
    sourceProfile
    native.strategy who site event payload value reward
  have complement := qualified_prefix_complement setup implementation native.strategy who site event
    massFinite
  have complement' : informationMass - admittedMass =
      ∑' history : (nativeModel).InformationHistory who site.1,
        (nativeModel).historyReachWeight native.strategy history.val * failure history := by
    simpa only [informationMass, admittedMass, failure, guard] using complement
  have genericPayoff := qualifiedPayoff_mul_informationMass setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
    implementation.prior values
  have payoffLaw := genericPayoff native nativeBayes who site massPositive choice utility
    excludedPayoff outcome
  refine payoffLaw.trans ?_
  rw [show (∑' index : MechanicalIndex setup implementation who,
      ∑' cut : setup.proposalRecoveryProtocol.History,
        ∑' completed : setup.proposalRecoveryProtocol.History,
          annotatedForcedBlockWeight setup values implementation operational sourceProfile
            native.strategy
            who site index event payload value cut completed * reward cut completed) =
      ∑' history : (nativeModel).InformationHistory who site.1,
        ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength, row history tape from
          annotation]
  rw [complement', ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro history
  change (nativeModel).InformationHistory who site.1 at history
  have observed : (nativeModel).infoOf who history.val.trace = some (past, view) :=
    history.property.trans information
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  cases state with
  | none =>
      have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
        implementation.scheduler who trace
      simp only [ReactiveApplication.observe] at observedInfo
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = some (past, view) at observed
      rw [observedInfo] at observed
      cases observed
  | some control =>
    have active : control.actor = some who := by
      by_contra inactive
      have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
        implementation.scheduler who trace
      simp only [ReactiveApplication.observe, inactive, ↓reduceIte] at observedInfo
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = some (past, view) at observed
      rw [observedInfo] at observed
      cases observed
    have actualInfo : (nativeModel).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = _
      have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
        implementation.scheduler who trace
      simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observedInfo
    have views := Option.some.inj (actualInfo.symm.trans observed)
    have pastEq := congrArg Prod.fst views
    have viewEq := congrArg Prod.snd views
    change control.execution.recall who = past at pastEq
    change control.execution.observe nativeApplication who = view at viewEq
    have clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
        (control.execution.observe nativeApplication who) event payload := by
      rw [pastEq, viewEq]
      exact cleanSite
    let actualHistory : (nativeProtocol).History := ⟨some control, trace⟩
    let actualChoice : (nativeModel).Choice who ((nativeModel).infoOf who trace) :=
      historyInfo.symm ▸ choice
    have selected : actualChoice.val = some ⟨some material⟩ := by
      exact transport_indexed
        (fun info (chosen : (nativeModel).Choice who info) =>
          chosen.val = some ⟨some material⟩)
        historyInfo choice selectedChoice
    have available : (⟨some material⟩ : (nativeApplication).Action) ∈
        (nativeMenu).actions who (control.execution.recall who)
          (control.execution.observe nativeApplication who) := by
      have offered := actualChoice.property
      change actualChoice.val ∈ (nativeModel).menu who ((nativeModel).infoOf who trace) at offered
      have offered' := (congrArg
        (fun info => actualChoice.val ∈ (nativeModel).menu who info) actualInfo).mp offered
      obtain ⟨response, permitted, equal⟩ := offered'
      have responseEq : response = ⟨some material⟩ := Option.some.inj (equal.symm.trans selected)
      exact responseEq ▸ permitted
    have reachPositive : (nativeModel).historyReachWeight native.strategy actualHistory ≠ 0 :=
      ((nativeModel).historyReachWeight_pos_of_fullSupport native.strategy nativeMixed
        actualHistory).ne'
    have canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
        (canonicalSource setup implementation operational actualHistory) ≠ 0 :=
      (prescribed_source_history_positive setup values scale sourceBad scalePositive scaleBelow
        badPositive badBelow fullValues sourceProfile sourcePrescribed _).ne'
    by_cases good : foreignGood setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan implementation.prior who actualHistory
    · have nativeForeign : ∀ owner, owner ≠ who →
          ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner actualHistory := by
        simpa only [foreignGood, ReservedConcurrentImplementation.initial,
          ReservedConcurrentImplementation.horizon,
          ReservedConcurrentImplementation.scheduler] using good
      obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational control trace
        who event payload clean nativeForeign
      have alive : who ∉ control.execution.application.current.excluded := clean.request.2.2.2.2
      have guarded : guard ⟨actualHistory, historyInfo⟩ := ⟨nativeForeign, alive⟩
      have physical := stoppedFinish_qualified_physical setup values implementation operational who
        actualHistory actualChoice control.remaining control.execution (by
          calc
            actualHistory.state = some {control with actor := control.actor} := rfl
            _ = some {control with actor := some who} :=
              congrArg (fun actor => some {control with actor := actor}) active
            _ = some ⟨control.remaining, some who, control.execution⟩ := rfl)
        ⟨some material⟩ selected entry.phase (Option.mem_def.mpr entry.installed) entry.commitment
        utility excludedPayoff
      have fiber (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
          (nativeModel).historyReachWeight native.strategy actualHistory *
            prefixTapeLaw setup implementation actualHistory tape *
            (((nativeApplication).runUntil
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape)
              (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values)
              (fun next => next.application.attempt ≠ control.execution.application.attempt)
              control.remaining (control.execution.respond nativeApplication who ⟨some
                material⟩)).bind
              fun ending => ((nativeApplication).finish nativeInitial implementation.horizon
                (ReservedEpoch.family implementation.runtime implementation.leaks
                  (ReservedEpoch.packetCapacity implementation.runtime) tape)
                (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan values)
                (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
                (fun terminal => if foreignGood setup .concurrent implementation.runtime
                    implementation.leaks implementation.bounds implementation.plan
                      implementation.prior
                    who actualHistory ∧ ending.application.attempt ≠
                      control.execution.application.attempt ∧
                    ending.application.current.excluded =
                      control.execution.application.entry.excluded
                  then some (phaseExclusionBase setup .concurrent implementation.runtime
                    implementation.leaks
                    utility excludedPayoff terminal who) else none)) outcome =
          row ⟨actualHistory, historyInfo⟩ tape +
            (nativeModel).historyReachWeight native.strategy actualHistory *
              (prefixTapeLaw setup implementation actualHistory tape *
                if bindingAdmissionBit setup implementation who event actualHistory tape then 0
                  else 1) *
                  (PMF.pure (none : Option ℝ)) outcome := by
        by_cases tapeZero : prefixTapeLaw setup implementation actualHistory tape = 0
        · simp only [tapeZero, mul_zero, zero_mul]
          symm
          simp [row, annotatedPrefixWeight, tapeZero]
        · have tapeSupported := (PMF.mem_support_iff _ _).mpr tapeZero
          have gate := fixed_tape_gate_law setup values implementation operational fullValues
            control
            trace who active tape tapeSupported event payload clean.binding value serial material
              available
            packet prepared entry.phase (Option.mem_def.mpr entry.installed) entry.commitment
              utility
            excludedPayoff
          by_cases admitted : bindingAdmissionBit setup implementation who event actualHistory
            tape = true
          · rw [show (bindingAdmissionBit setup implementation who event actualHistory tape) = true
              from admitted]
            have source := annotated_admitted_tape setup values implementation operational
              fullValues
              sourceProfile native.strategy who control trace active canonicalSupported
                reachPositive tape
              tapeZero event payload clean good admitted material available serial packet value
                prepared
              utility excludedPayoff outcome pairLaw
            rw [gate, ite_eq_left ⟨good, admitted⟩]
            simpa only [row, reward, actualHistory, admitted, ↓reduceIte, mul_one,
              mul_zero, zero_mul, add_zero] using source
          · have rejected : bindingAdmissionBit setup implementation who event actualHistory tape
            = false :=
              Bool.eq_false_of_not_eq_true admitted
            rw [gate, ite_eq_right (by exact fun both => admitted both.2)]
            simp [row, rejected]
      calc
        _ = ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
            (row ⟨actualHistory, historyInfo⟩ tape +
              (nativeModel).historyReachWeight native.strategy actualHistory *
                (prefixTapeLaw setup implementation actualHistory tape *
                  if bindingAdmissionBit setup implementation who event actualHistory tape then 0
                    else 1) *
                    (PMF.pure (none : Option ℝ)) outcome) := by
          rw [physical, PMF.bind_apply, ← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro tape
          dsimp only [actualHistory, ReservedConcurrentImplementation.initial,
            ReservedConcurrentImplementation.horizon,
            ReservedConcurrentImplementation.scheduler] at fiber ⊢
          simpa only [mul_assoc] using fiber tape
        _ = _ := by
          dsimp only [actualHistory] at guarded ⊢
          simp only [failure, guarded, ↓reduceIte, ENNReal.tsum_add,
            ENNReal.tsum_mul_left, mul_assoc]
          rw [← ENNReal.tsum_mul_right]
          simp only [mul_assoc]
    · have nativeBad : ¬ (∀ owner, owner ≠ who →
          ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner actualHistory) := by
        simpa only [foreignGood, ReservedConcurrentImplementation.initial,
          ReservedConcurrentImplementation.horizon,
          ReservedConcurrentImplementation.scheduler] using good
      have empty : ∀ tape, row ⟨actualHistory, historyInfo⟩ tape = 0 := by
        intro tape
        simp only [row, annotatedPrefixWeight, nativeBad, false_and, ↓reduceIte,
          mul_zero, zero_mul, tsum_zero]
      have failed : failure ⟨actualHistory, historyInfo⟩ = 1 := by
        simp only [failure, guard, nativeBad, false_and, ↓reduceIte]
      dsimp only [actualHistory] at good empty failed
      have mappedNone {α : Type} (law : PMF α) :
          (law.map fun _ => (none : Option ℝ)) = PMF.pure none := PMF.map_const law none
      simp only [good, false_and, ↓reduceIte, mappedNone, empty, tsum_zero,
        failed, zero_add, mul_one];
        dsimp only [ReservedConcurrentImplementation.initial,
          ReservedConcurrentImplementation.horizon,
          ReservedConcurrentImplementation.scheduler]

end QualifiedPayoffAttachment

omit mode runtime leaks bounds plan prior values in
/-- The original concurrent assessments satisfy exact qualified binding transport. -/
theorem qualified_binding_law (implementation : ReservedConcurrentImplementation setup) :
    QualifiedBindingLaw setup implementation := by
  classical
  intro operational scale sourceBad nativeBad scalePositive scaleBelow badPositive badBelow
    nativePositive nativeBelow values fullValues source native sourceMixed sourceBayes
    sourcePrescribed nativeMixed nativeBayes nativePrescribed who site past view information
    event payload binding request unsent noSaved noCurrent noForeignFailure
  dsimp only
  let model := (PhaseCount.onePacketMenu implementation.runtime implementation.leaks
    implementation.bounds).information implementation.initial implementation.horizon
      implementation.scheduler
  let cleanSite : CleanUnsentBinding setup implementation who past view event payload :=
    ⟨binding, request, unsent, noSaved, noCurrent, noForeignFailure⟩
  let proper := fun (value : L.Val payload) (choice : model.Choice who site.1) =>
    ∃ (serial : Nat) (material : WitnessedSubmission (serviceGraph setup .concurrent)),
      choice.1 = some ⟨some material⟩ ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      PhaseProposal.bindingPreparation material = some ⟨payload, value⟩
  let mass := fun choice => qualificationMass setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan implementation.prior
    values native who site choice
  let payoff := fun choice utility excludedPayoff => qualifiedPayoff setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
    implementation.prior values native who site choice utility excludedPayoff
  let nativeMass := model.informationMass native.strategy who site
  let admittedMass := qualifiedPrefixMass setup implementation native.strategy who site event
  have nativeMassPositive : 0 < nativeMass :=
    model.informationMass_pos_of_fullSupport native.strategy nativeMixed who site
  have nativeMassFinite : nativeMass ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (model.informationMass_le_one native.strategy who site
      ((PhaseCount.onePacketMenu implementation.runtime implementation.leaks
        implementation.bounds).decisionInformationAntichain implementation.initial
        implementation.horizon implementation.scheduler who site))
  have pairLaw := foreign_posterior_cut_pair setup values implementation
  have endpoint (value : L.Val payload) (choice : model.Choice who site.1)
      (offered : proper value choice) (utility : State L setup.program.terminalCtx → Player → ℝ)
      (excludedPayoff : Player → ℝ) (outcome : Option ℝ) :=
    annotated_stopped_payoff setup values implementation operational scale sourceBad
      scalePositive scaleBelow badPositive badBelow fullValues source.strategy sourcePrescribed
      native nativeMixed nativeBayes who site past view information event payload cleanSite
      value choice offered utility excludedPayoff outcome pairLaw
  by_cases offered : ∃ (value : L.Val payload) (choice : model.Choice who site.1),
      proper value choice
  · obtain ⟨referenceValue, referenceChoice, referenceProper⟩ := offered
    by_cases admittedZero : admittedMass = 0
    · left
      intro value choice properChoice
      have atNone := endpoint value choice properChoice (fun _ _ => 0) (fun _ => 0) none
      have noneOne : payoff choice (fun _ _ => 0) (fun _ => 0) none = 1 := by
        apply (ENNReal.mul_right_inj nativeMassPositive.ne' nativeMassFinite).mp
        simpa [admittedMass, nativeMass, admittedZero, PMF.map_apply] using atNone
      have pure : payoff choice (fun _ _ => 0) (fun _ => 0) = PMF.pure none := by
        apply pmf_eq_pure_of_support_subset_singleton
        exact ((PMF.apply_eq_one_iff _ _).mp noneOne).subset
      have zero : mass choice = 0 := by
        have observed := qualifiedPayoff_isSome setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan implementation.prior
          values native who site choice (fun _ _ => 0) (fun _ => 0)
        rw [show qualifiedPayoff setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan implementation.prior values native who site
          choice (fun _ _ => 0) (fun _ => 0) = PMF.pure none from pure] at observed
        have atTrue := congrArg (fun law : PMF Bool => law true) observed
        simpa only [mass, qualificationMass, PMF.pure_map, Option.isSome_none,
          PMF.pure_apply_of_ne false true (by decide : true ≠ false), ENNReal.toReal_zero]
            using congrArg ENNReal.toReal atTrue.symm
      exact ⟨zero, fun utility excludedPayoff => qualifiedPayoff_eq_pure_none setup .concurrent
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        implementation.prior values native who site choice zero utility excludedPayoff⟩
    · have admittedPositive : 0 < admittedMass := pos_iff_ne_zero.mpr admittedZero
      obtain ⟨sourceSite, encode, anchor, anchorInfo, anchorGood, anchorReach, query, encoded,
          ordinary, ownPositive, ownFinite, classesPositive, classesFinite, sourceMassPositive,
          sourceMassFinite, coefficientPositive, coefficientFinite, _constant, rectangle⟩ :=
        qualified_reconstruction setup values implementation operational scale sourceBad nativeBad
          scalePositive scaleBelow badPositive badBelow nativePositive nativeBelow fullValues
          source.strategy native.strategy sourcePrescribed nativePrescribed who site past view
          information event payload cleanSite admittedPositive
      let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (source.strategy who) (setup.proposalRecoveryModel.ownPlay who anchor.trace))
      let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
        who anchor.trace).1
      let factor := own * classes
      let coefficient := mechanicalCoefficient setup implementation
        ⟨nativeBad, scale, scale, scale⟩ native.strategy who site event
      let coefficientMass := ∑' index, coefficient index
      let good : Set (setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :=
        {h | setup.proposalRecoveryForeignGood who h.val}
      let sourceMass := ∑' h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1,
        if setup.proposalRecoveryForeignGood who h.val then
          setup.proposalRecoveryModel.historyReachWeight source.strategy h.val else 0
      let sourceInformationMass :=
        setup.proposalRecoveryModel.informationMass source.strategy who sourceSite
      have sourceInformationPositive : 0 < sourceInformationMass :=
        setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          source.strategy sourceMixed who sourceSite
      have sourceInformationFinite : sourceInformationMass ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (setup.proposalRecoveryModel.informationMass_le_one source.strategy who sourceSite
            (setup.proposalRecoveryModel_decisionAntichain who sourceSite))
      have beliefScale (h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :
          sourceInformationMass * source.belief who sourceSite h =
            setup.proposalRecoveryModel.historyReachWeight source.strategy h.val := by
        rw [sourceBayes who sourceSite sourceInformationPositive h, div_eq_mul_inv]
        calc
          _ = setup.proposalRecoveryModel.historyReachWeight source.strategy h.val *
              (sourceInformationMass * sourceInformationMass⁻¹) := by ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel sourceInformationPositive.ne'
            sourceInformationFinite, mul_one]
      have positive : ∃ h ∈ good, h ∈ (source.belief who sourceSite).support := by
        refine ⟨⟨anchor, anchorInfo⟩, anchorGood, ?_⟩
        apply (PMF.mem_support_iff _ _).mpr
        intro absent
        have contradiction := beliefScale ⟨anchor, anchorInfo⟩
        rw [absent, mul_zero] at contradiction
        exact anchorReach.ne' contradiction.symm
      let belief := (source.belief who sourceSite).filter good positive
      have sourceScale (h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :
          sourceMass * belief h =
            if setup.proposalRecoveryForeignGood who h.val then
              setup.proposalRecoveryModel.historyReachWeight source.strategy h.val else 0 := by
        have scaledIndicator (h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :
            sourceInformationMass * good.indicator (source.belief who sourceSite) h =
              if setup.proposalRecoveryForeignGood who h.val then
                setup.proposalRecoveryModel.historyReachWeight source.strategy h.val else 0 := by
          by_cases member : h ∈ good
          · rw [Set.indicator_of_mem member, beliefScale]
            change setup.proposalRecoveryForeignGood who h.val at member
            rw [ite_eq_left member]
          · rw [Set.indicator_of_notMem member, mul_zero]
            change ¬ setup.proposalRecoveryForeignGood who h.val at member
            rw [ite_eq_right member]
        have scaledMass : sourceMass = sourceInformationMass *
            ∑' h, good.indicator (source.belief who sourceSite) h := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun h => (scaledIndicator h).symm
        rw [scaledMass, mul_assoc, filter_mass_mul]
        exact scaledIndicator h
      have factorPositive : 0 < factor := ENNReal.mul_pos ownPositive.ne' classesPositive.ne'
      have factorFinite : factor ≠ ⊤ := ENNReal.mul_ne_top ownFinite classesFinite
      have denominatorPositive : 0 < factor * nativeMass :=
        ENNReal.mul_pos factorPositive.ne' nativeMassPositive.ne'
      have denominatorFinite : factor * nativeMass ≠ ⊤ :=
        ENNReal.mul_ne_top factorFinite nativeMassFinite
      let retainedMass := (factor * nativeMass)⁻¹ * (coefficientMass * sourceMass)
      let complement := nativeMass⁻¹ * (nativeMass - admittedMass)
      have retainedPositive : 0 < retainedMass := by
        exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr denominatorFinite)
          (mul_ne_zero coefficientPositive.ne' sourceMassPositive.ne')
      have retainedFinite : retainedMass ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr denominatorPositive.ne')
          (ENNReal.mul_ne_top coefficientFinite sourceMassFinite)
      have density (value : L.Val payload) (choice : model.Choice who site.1)
          (offered : proper value choice)
          (utility : State L setup.program.terminalCtx → Player → ℝ)
          (excludedPayoff : Player → ℝ) (outcome : Option ℝ) :
          payoff choice utility excludedPayoff outcome =
            retainedMass * sourceCausalPayoff setup values source who sourceSite
              (encode value) positive utility excludedPayoff outcome +
            complement * (PMF.pure (none : Option ℝ)) outcome := by
        let kernel := fun completed : setup.proposalRecoveryProtocol.History =>
          (setup.proposalRecoveryModel.runBehavioralTerminalFrom
            setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
            (sourceUnflaggedStrategy setup values) completed).map fun terminal =>
              some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal)
        let causal := sourceCausalPayoff setup values source who sourceSite
          (encode value) positive utility excludedPayoff
        let cutTerm := fun cut : setup.proposalRecoveryProtocol.History =>
          if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
            if setup.proposalRecoveryForeignGood who cut then
              setup.proposalRecoveryModel.historyReachWeight source.strategy cut *
                ((sourceForcedBlock setup values who cut (same.symm ▸ encode value)).bind
                  kernel) outcome
            else 0
          else 0
        have sourceSum : (∑' cut, cutTerm cut) = sourceMass * causal outcome := by
          have supported : Function.support cutTerm ⊆
              {cut | setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1} := by
            intro cut nonzero
            by_contra absent
            change setup.proposalRecoveryModel.infoOf who cut.trace ≠ sourceSite.1 at absent
            exact nonzero (by simp only [cutTerm, dite_eq_right absent])
          rw [← tsum_subtype_eq_of_support_subset supported]
          dsimp only [causal]
          rw [sourceCausalPayoff_block setup values source who sourceSite (encode value)
            positive utility excludedPayoff]
          simp only [PMF.map_bind, PMF.bind_apply]
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro h
          rw [← mul_assoc, sourceScale]
          have same : setup.proposalRecoveryModel.infoOf who h.val.trace = sourceSite.1 :=
            h.property
          by_cases active : setup.proposalRecoveryForeignGood who h.val
          · simp only [cutTerm, dite_eq_left same, ite_eq_left active, PMF.bind_apply, kernel]
          · simp only [cutTerm, dite_eq_left same, ite_eq_right active, zero_mul]
        have weighted : factor *
            (∑' index : MechanicalIndex setup implementation who,
              ∑' cut : setup.proposalRecoveryProtocol.History,
                ∑' completed : setup.proposalRecoveryProtocol.History,
                  annotatedForcedBlockWeight setup values implementation operational source.strategy
                    native.strategy who site index event payload value cut completed *
                    kernel completed outcome) =
              coefficientMass * sourceMass * causal outcome := by
          calc
            _ = ∑' index : MechanicalIndex setup implementation who,
                coefficient index * ∑' cut, cutTerm cut := by
              rw [← ENNReal.tsum_mul_left]
              apply tsum_congr
              intro index
              simp only [← ENNReal.tsum_mul_left]
              apply tsum_congr
              intro cut
              dsimp only [factor, own, classes]
              simp_rw [← mul_assoc, rectangle index value cut]
              by_cases same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1
              · by_cases active : setup.proposalRecoveryForeignGood who cut
                · simp only [cutTerm, dite_eq_left same, ite_eq_left active, PMF.bind_apply,
                    mul_assoc, ENNReal.tsum_mul_left, coefficient]
                · simp only [cutTerm, dite_eq_left same, ite_eq_right active, mul_zero,
                    zero_mul, tsum_zero]
              · simp only [cutTerm, dite_eq_right same, mul_zero, zero_mul, tsum_zero]
            _ = coefficientMass * sourceMass * causal outcome := by
              rw [sourceSum, ENNReal.tsum_mul_right]
              dsimp only [coefficientMass]
              ac_rfl
        have nativeEquation := endpoint value choice offered utility excludedPayoff outcome
        apply (ENNReal.mul_right_inj denominatorPositive.ne' denominatorFinite).mp
        calc
          _ = factor * (nativeMass * payoff choice utility excludedPayoff outcome) := by
            rw [mul_assoc]
          _ = coefficientMass * sourceMass * causal outcome +
              factor * ((nativeMass - admittedMass) * (PMF.pure (none : Option ℝ)) outcome) := by
            rw [nativeEquation, mul_add, weighted]
          _ = (factor * nativeMass) *
              (retainedMass * causal outcome +
                complement * (PMF.pure (none : Option ℝ)) outcome) := by
            have retainedCancel : (factor * nativeMass) * retainedMass =
                coefficientMass * sourceMass := by
              change (factor * nativeMass) *
                ((factor * nativeMass)⁻¹ * (coefficientMass * sourceMass)) = _
              rw [← mul_assoc,
                ENNReal.mul_inv_cancel denominatorPositive.ne' denominatorFinite, one_mul]
            have complementCancel : (factor * nativeMass) * complement =
                factor * (nativeMass - admittedMass) := by
              change (factor * nativeMass) *
                (nativeMass⁻¹ * (nativeMass - admittedMass)) = _
              calc
                _ = factor * ((nativeMass * nativeMass⁻¹) *
                    (nativeMass - admittedMass)) := by ac_rfl
                _ = _ := by rw [ENNReal.mul_inv_cancel nativeMassPositive.ne'
                  nativeMassFinite, one_mul]
            symm
            rw [mul_add, ← mul_assoc, retainedCancel, ← mul_assoc, complementCancel]
            ac_rfl
      have normalized : retainedMass + complement = 1 := by
        have summed := congrArg (fun f : Option ℝ → ℝ≥0∞ => ∑' outcome, f outcome)
          (funext (density referenceValue referenceChoice referenceProper
            (fun _ _ => 0) (fun _ => 0)))
        simpa only [PMF.tsum_coe, ENNReal.tsum_add, ENNReal.tsum_mul_left, mul_one]
          using summed.symm
      have retainedBound : retainedMass ≤ 1 := by
        rw [← normalized]
        exact le_add_of_nonneg_right zero_le
      have complementFinite : complement ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (by
          rw [← normalized]
          exact le_add_of_nonneg_left zero_le)
      let retained : Set.Ioc (0 : ℝ) 1 :=
        ⟨retainedMass.toReal, ENNReal.toReal_pos retainedPositive.ne' retainedFinite,
          by
            simpa only [ENNReal.toReal_one] using
              (ENNReal.toReal_mono ENNReal.one_ne_top retainedBound)⟩
      have complementReal : ENNReal.ofReal (1 - retained.val) = complement := by
        have realSum := congrArg ENNReal.toReal normalized
        rw [ENNReal.toReal_add retainedFinite complementFinite, ENNReal.toReal_one] at realSum
        have difference : 1 - retained.val = complement.toReal := by
          change 1 - retainedMass.toReal = complement.toReal
          linarith
        rw [difference, ENNReal.ofReal_toReal complementFinite]
      have mixture (value : L.Val payload) (choice : model.Choice who site.1)
          (offered : proper value choice)
          (utility : State L setup.program.terminalCtx → Player → ℝ)
          (excludedPayoff : Player → ℝ) :
          payoff choice utility excludedPayoff =
            mix retained.val retained.property.1.le retained.property.2
              (sourceCausalPayoff setup values source who sourceSite (encode value) positive
                utility excludedPayoff) (PMF.pure none) := by
        ext outcome
        rw [density value choice offered, mix_apply, complementReal]
        rw [show ENNReal.ofReal retained.val = retainedMass from
          ENNReal.ofReal_toReal retainedFinite]
      refine Or.inr ⟨sourceSite, retained, encode, positive, query, encoded, ordinary, ?_⟩
      intro value choice properChoice
      refine ⟨?_, mixture value choice properChoice⟩
      have readout : (sourceCausalPayoff setup values source who sourceSite (encode value)
          positive (fun _ _ => 0) (fun _ => 0)).map Option.isSome = PMF.pure true := by
        simp only [sourceCausalPayoff, PMF.map_bind, PMF.map_comp, Function.comp_def]
        dsimp only [Option.isSome]
        simp only [PMF.map, Function.comp_def, PMF.bind_const]
      have observed := qualifiedPayoff_isSome setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan implementation.prior
        values native who site choice (fun _ _ => 0) (fun _ => 0)
      have projected := congrArg (PMF.map Option.isSome)
        (mixture value choice properChoice (fun _ _ => 0) (fun _ => 0))
      rw [observed, mix_map, readout, PMF.pure_map] at projected
      have atTrue := congrArg (fun law : PMF Bool => law true) projected
      simp only [mix_apply, Option.isSome, PMF.pure_apply_self,
        PMF.pure_apply_of_ne false true (by decide : true ≠ false), mul_one, mul_zero,
        add_zero] at atTrue
      change (qualificationLaw setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan implementation.prior values native who site
        choice true).toReal = retained.val
      rw [atTrue, ENNReal.toReal_ofReal retained.property.1.le]
  · left
    intro value choice properChoice
    exact False.elim (offered ⟨value, choice, properChoice⟩)

end Vegas.PhaseProposalQualifiedBinding
