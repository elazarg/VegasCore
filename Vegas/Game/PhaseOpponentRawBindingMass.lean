/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingFiberGeometry

/-! # Opponent raw-send contributions over an actual complete information fiber -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

def phaseOwnRecordAt (owner : Player) (history : (E).History) (index : Nat) :
    (N).InfoState owner × (E).Action owner :=
  (((N).ownPlay owner history.trace).drop index).headD (none, ⟨none⟩)

open Classical in
/-- One actual own-record position contributes only its RAW-mixture binding
send component. Opening WAIT and every source/slot component remain unmarked. -/
def phaseRawBindingPositionWeight (noise : ℝ) (owner : Player)
    (profile : ∀ player, (N).BehavioralPolicy player) (history : (E).History) (index : Nat) : ℝ :=
  if phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
      (phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history index)
  then phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler noise owner
    profile history (((N).ownPlay owner history.trace).take index)
      (phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history index)
      (((N).ownPlay owner history.trace).drop index).tail
  else 0

private theorem not_phaseRawBindingRecord_silence (owner : Player) :
    ¬phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
      (none, ⟨none⟩) := by
  rintro ⟨_event, _serial, _preparation, _evidence, same⟩
  cases congrArg (fun response : (phaseApplication runtime leaks).Action => response.transmission)
    same

/-- EVERY actually recorded binding send has the prepared-slot syntax used
by the marked component. This follows from the real counted local menu and
retains arbitrary preparation and evidence requests. -/
theorem phaseRawBindingRecord_of_ownPlay (owner : Player) (history : (E).History)
    (record : (N).InfoState owner × (E).Action owner)
    (member : record ∈ (N).ownPlay owner history.trace)
    (material : (phaseApplication runtime leaks).Submission)
    (sent : record.2.transmission = some material)
    (event : (serviceGraph setup mode).EventId) (candidate : Handle (serviceGraph setup mode))
    (call : material.call.packet = .commitment event candidate) :
    phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner record := by
  rcases record with ⟨observed, action⟩
  have legal := (N).ownPlay_mem_menu owner history.trace member
  have actionEq : action = ⟨some material⟩ := by
    cases action
    cases sent
    rfl
  cases actionEq
  cases observed with
  | none =>
      change some (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈ {none} at legal
      simp at legal
  | some data =>
      change ∃ response ∈ PhaseCount.onePacketActions runtime leaks bounds owner data.1 data.2,
        some (⟨some material⟩ : (phaseApplication runtime leaks).Action) = some response at legal
      obtain ⟨response, offered, same⟩ := legal
      cases Option.some.inj same
      have permitted : PhaseCount.permits ((phaseApplication runtime leaks).outputs data.1)
          (PhaseCount.localEnvelope runtime leaks owner data.1 data.2 material) = true := by
        rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp offered).2
          with impossible | ⟨supplied, same, allowed⟩
        · cases impossible
        · cases Option.some.inj same
          exact allowed
      have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
      have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks owner
          data.1 data.2 material)).payload.call = material.call.packet :=
        PhaseCount.maskPacket_call _ _
      unfold CountCallCorrect at correct
      rw [actualCall, call] at correct
      obtain ⟨_, _, ownerEq, ⟨serial, prepared⟩, _⟩ := correct
      change candidate.1 = owner at ownerEq
      rcases candidate with ⟨signer, slot⟩
      change signer = owner at ownerEq
      subst signer
      change slot = .prepared serial at prepared
      subst slot
      rcases material with ⟨⟨packet, preparation⟩, evidence⟩
      change packet = .commitment event (owner, .prepared serial) at call
      cases call
      exact ⟨event, serial, preparation, evidence, rfl⟩

theorem phase_position_records (owner : Player) (history : (E).History) (index : Nat)
    (raw : phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
      (phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history
        index)) :
    (N).ownPlay owner history.trace = ((N).ownPlay owner history.trace).take index ++
      phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history index ::
        (((N).ownPlay owner history.trace).drop index).tail := by
  cases dropped : ((N).ownPlay owner history.trace).drop index with
  | nil =>
      simp only [phaseOwnRecordAt, dropped, List.headD_nil] at raw
      exact (not_phaseRawBindingRecord_silence setup mode runtime leaks bounds plan horizon
        scheduler owner raw).elim
  | cons record rest =>
      have split := (List.take_append_drop index ((N).ownPlay owner history.trace)).symm
      simpa only [phaseOwnRecordAt, dropped, List.headD_cons, List.tail_cons] using split

/-- The fixed protocol clock bounds ALL own-record positions, including WAIT
and inert callbacks; this bound contains no strategy parameter. -/
theorem phase_ownPlay_length_le (owner : Player) (history : (E).History) :
    ((N).ownPlay owner history.trace).length ≤ 2 * horizon + 1 := by
  have ownLength : ∀ {state} (trace : (E).Trace state),
      ((N).ownPlay owner trace).length ≤ trace.length := by
    intro state trace
    induction trace with
    | start => simp [InfoSignals.ownPlay, Trace.length]
    | extend prior joint legal realized ih =>
        rw [InfoSignals.ownPlay_extend]
        cases joint owner <;> simp_all only [Trace.length, List.length_cons] <;> omega
  have bound := (phaseApplication runtime leaks).trace_bound initial horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
      history.trace)
  rw [ReactiveApplication.ResponseMenu.toRawTrace_length] at bound
  have own := ownLength history.trace
  omega

/-- No raw-binding contribution is omitted beyond the fixed position range. -/
theorem phaseRawBindingPositionWeight_eq_zero_of_ge (noise : ℝ) (owner : Player)
    (profile : ∀ player, (N).BehavioralPolicy player) (history : (E).History)
    (index : Nat) (beyond : 2 * horizon + 1 ≤ index) :
    phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
      owner profile history index = 0 := by
  have bound := phase_ownPlay_length_le setup mode runtime leaks bounds plan horizon scheduler
    owner history
  have empty : ((N).ownPlay owner history.trace).drop index = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [List.length_drop]
    omega
  have noRaw : ¬phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
      (phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history
        index) := by
    rw [phaseOwnRecordAt, empty, List.headD_nil]
    exact not_phaseRawBindingRecord_silence setup mode runtime leaks bounds plan horizon scheduler
      owner
  simp only [phaseRawBindingPositionWeight, ite_eq_right noRaw]

theorem phaseRawBindingPositionWeight_nonneg (noise : ℝ) (nonnegative : 0 ≤ noise)
    (owner : Player) (profile : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History) (index : Nat) :
    0 ≤ phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler
      noise owner profile history index := by
  unfold phaseRawBindingPositionWeight
  split_ifs
  · have beforeNonnegative := (N).ownPlayReachProbability_nonneg (profile owner)
      (((N).ownPlay owner history.trace).take index)
    have afterNonnegative := (N).ownPlayReachProbability_nonneg (profile owner)
      (((N).ownPlay owner history.trace).drop index).tail
    have otherNonnegative := (N).counterfactualReachProbability_nonneg profile owner history.trace
    dsimp only [phaseMarkedHistoryWeight, phaseRawMixtureOwnPlayWeight, phaseRawMixtureAtom]
    positivity
  · exact le_rfl

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))) scheduler]

local instance : Finite (E).History := @ReactiveApplication.ResponseMenu.finite_history
  Player inferInstance (phaseApplication runtime leaks)
    (PhaseCount.onePacketMenu runtime leaks bounds)
    initial horizon scheduler inferInstance nature

local instance : Fintype (E).History := Fintype.ofFinite _

local instance (focal : Player) (site : (N).InformationSite focal) :
    Fintype ((N).InformationHistory focal site.1) := Fintype.ofFinite _

/-- The finite sum of all opponent RAW binding-send contributions. This is a
union bound over marked components of the existing execution law, not a new
latent execution protocol. Repeated marked draws may be counted more than once. -/
def phaseOpponentRawBindingMass (noise : ℝ) (focal : Player)
    (profile : ∀ player, (N).BehavioralPolicy player) (site : (N).InformationSite focal) : ℝ :=
  ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
    ∑ history : (N).InformationHistory focal site.1,
      phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
        owner profile history.1 index

/-- Normalize the selected opponent contributions by the actual information
mass. The raw branch is never inferred from the syntax of an observed action. -/
def phaseOpponentRawBindingShare (noise : ℝ) (focal : Player)
    (profile : ∀ player, (N).BehavioralPolicy player) (site : (N).InformationSite focal) : ℝ :=
  phaseOpponentRawBindingMass setup mode runtime leaks bounds plan horizon scheduler noise focal
    profile site / ((N).informationMass profile focal site).toReal

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

variable (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
  (floor : ℝ) (positive : 0 < floor)
  (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
    (choice : setup.commitRecoveryModel.Choice player site.1),
    floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
  (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
  (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)

local notation "strategy" => phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial
  horizon scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
    slotWeight slotPositive.le slotBounded

include maximal capacity positive floored in
open Classical in
private theorem phase_raw_position_fiber_mass_le
    (covered : bounds.CoversOutputValues) (owner focal : Player) (different : focal ≠ owner)
    (site : (N).InformationSite focal) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (genuine : ∀ history : (N).InformationHistory focal site.1,
      ∃ control : (phaseApplication runtime leaks).Control,
        history.1.state = some control ∧ control.actor = some focal ∧
          control.execution.application.current.excluded = ∅ ∧
          control.execution.application.SeedRequest focal
            ⟨control.execution.application.attempt, event⟩) (index : Nat) :
    (∑ history : (N).InformationHistory focal site.1,
      phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
        owner strategy history.1 index) ≤
      (Nat.card (E).History : ℝ) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1) * (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) *
            ((N).informationMass strategy focal site).toReal := by
  let before := fun history : (N).InformationHistory focal site.1 =>
    ((N).ownPlay owner history.1.trace).take index
  let marked := fun history : (N).InformationHistory focal site.1 =>
    phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history.1 index
  let after := fun history : (N).InformationHistory focal site.1 =>
    (((N).ownPlay owner history.1.trace).drop index).tail
  let histories := Finset.univ.filter fun history : (N).InformationHistory focal site.1 =>
    phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
      (marked history)
  obtain ⟨repair, bound⟩ := phase_raw_binding_fiber_mass_le setup mode runtime leaks bounds plan
    horizon scheduler finite wellFormed target approximation maximal n capacity floor positive
      floored
      noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded covered owner focal
        different site event payload output histories (fun history _ => genuine history)
          before after marked (fun history member =>
            phase_position_records setup mode runtime leaks bounds plan horizon scheduler owner
              history.1 index (Finset.mem_filter.mp member).2)
          (fun _ member => (Finset.mem_filter.mp member).2)
  have targetLe : InformationModel.finiteHistoryReach (M := N) strategy focal site
      (histories.image repair) ≤ ((N).informationMass strategy focal site).toReal := by
    rw [InformationModel.informationMass_toReal_eq_sum]
    unfold InformationModel.finiteHistoryReach
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => ENNReal.toReal_nonneg)
  have scaled := bound.trans (mul_le_mul_of_nonneg_left targetLe (by positivity))
  dsimp only [histories] at scaled
  rw [Finset.sum_filter] at scaled
  simpa only [phaseRawBindingPositionWeight, before, after, marked] using scaled

include maximal capacity positive floored in
/-- Summing every opponent and EVERY possible own-record position gives a
fixed finite multiplicity. The same information mass multiplies the bound,
even when that mass tends to zero along the assessment sequence. -/
theorem phase_opponent_raw_binding_mass_le
    (covered : bounds.CoversOutputValues) (focal : Player) (site : (N).InformationSite focal)
    (original : (phaseApplication runtime leaks).Control)
    (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf focal originalTrace = site.1) (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    phaseOpponentRawBindingMass setup mode runtime leaks bounds plan horizon scheduler noise focal
        strategy site ≤
      ((Fintype.card Player : ℝ) * (2 * horizon + 1) * Nat.card (E).History) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1) * (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) *
            ((N).informationMass strategy focal site).toReal := by
  classical
  have genuine := phase_binding_fiber_genuine setup mode runtime leaks bounds plan horizon scheduler
    focal site original originalTrace atSite active event clear request
  let common := (Nat.card (E).History : ℝ) *
    (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
      (2 * horizon + 1) * (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) *
        ((N).informationMass strategy focal site).toReal
  unfold phaseOpponentRawBindingMass
  calc (∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        ∑ history : (N).InformationHistory focal site.1,
          phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
            owner strategy history.1 index)
      ≤ ∑ _owner ∈ Finset.univ.erase focal, ∑ _index ∈ Finset.range (2 * horizon + 1),
          common := by
        apply Finset.sum_le_sum
        intro owner member
        apply Finset.sum_le_sum
        intro index _inside
        exact phase_raw_position_fiber_mass_le setup mode runtime leaks bounds plan horizon
          scheduler finite wellFormed target approximation maximal n capacity floor positive
            floored
            noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded covered owner
              focal
              (Ne.symm (Finset.mem_erase.mp member).1) site event payload output genuine index
    _ = ((Finset.univ.erase focal).card : ℝ) * ((2 * horizon + 1) * common) := by simp
    _ ≤ (Fintype.card Player : ℝ) * ((2 * horizon + 1) * common) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp only [common]; positivity)
      exact_mod_cast Finset.card_le_univ (Finset.univ.erase focal)
    _ = _ := by dsimp only [common]; ring

omit nature in
/-- Positive raw noise gives full support at every actual finite choice, so
EVERY played native information site has positive real information mass. -/
theorem phase_perturbed_informationMass_pos (noisePositive : 0 < noise)
    (focal : Player) (site : (N).InformationSite focal) :
    0 < ((N).informationMass strategy focal site).toReal := by
  have full (player : Player) (decision : (N).InformationSite player)
      (choice : (N).Choice player decision.1) : choice ∈ (strategy player decision.1).support :=
    phaseSourcePerturbedStrategy_fullSupport setup mode runtime leaks bounds initial horizon
      scheduler
      wellFormed (approximation.sequence n) noise noisePositive noiseSmall.le slotWeight
        slotPositive.le slotBounded player decision.1 choice
  have massPositive := (N).informationMass_pos_of_fullSupport strategy full focal site
  have massFinite := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((N).informationMass_le_one strategy focal site
      ((PhaseCount.onePacketMenu runtime leaks bounds).decisionInformationAntichain
        initial horizon scheduler focal site))
  exact ENNReal.toReal_pos massPositive.ne' massFinite

include maximal capacity positive floored in
/-- The actual normalized sum of all opponent RAW binding-send contributions
is small uniformly across complete ready-binding information fibers. No
opening-WAIT or canonical-source component has been removed. -/
theorem phase_opponent_raw_binding_share_le (noisePositive : 0 < noise)
    (covered : bounds.CoversOutputValues) (focal : Player) (site : (N).InformationSite focal)
    (original : (phaseApplication runtime leaks).Control)
    (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf focal originalTrace = site.1) (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    0 ≤ phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler noise
        focal strategy site ∧
      phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler noise
        focal strategy site ≤
      ((Fintype.card Player : ℝ) * (2 * horizon + 1) * Nat.card (E).History) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1) * (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) := by
  have massPositive := phase_perturbed_informationMass_pos setup mode runtime leaks bounds plan
    horizon scheduler finite wellFormed target approximation n noise noiseNonnegative noiseSmall
      slotWeight slotPositive slotBounded noisePositive focal site
  constructor
  · unfold phaseOpponentRawBindingShare phaseOpponentRawBindingMass
    apply div_nonneg _ massPositive.le
    apply Finset.sum_nonneg
    intro owner _member
    apply Finset.sum_nonneg
    intro index _inside
    apply Finset.sum_nonneg
    intro history _member
    exact phaseRawBindingPositionWeight_nonneg setup mode runtime leaks bounds plan horizon
      scheduler
      noise noiseNonnegative owner strategy history.1 index
  · unfold phaseOpponentRawBindingShare
    rw [div_le_iff₀ massPositive]
    exact phase_opponent_raw_binding_mass_le setup mode runtime leaks bounds plan horizon scheduler
      finite wellFormed target approximation maximal n capacity floor positive floored noise
        noiseNonnegative noiseSmall slotWeight slotPositive slotBounded covered focal site original
          originalTrace atSite active event payload output clear request

end Vegas
