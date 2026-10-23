/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPairedWeight
import Vegas.Game.OnePacketPairedRecord
import Vegas.Game.OnePacketPairedCompletionMass
import Vegas.Game.OnePacketPairedResponseWeight

/-! # Source likelihoods of paired actual histories -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    profiles who}

private theorem regularTrace_of_prefix (assessment : setup.intendedModel.BehavioralAssessment)
    {first final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix prior top)
    (regular : RegularTrace setup leaks bounds horizon scheduler assessment who top) :
    RegularTrace setup leaks bounds horizon scheduler assessment who prior := by
  induction isPrefix with
  | refl => exact regular
  | extend _ _ _ _ ih => exact ih regular.1

private theorem operationalState_eq_of_record_eq
    {first second : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (left : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first)
    (right : (onePacketProtocol setup leaks bounds horizon scheduler).Trace second)
    (records : operationalRecord setup leaks bounds horizon scheduler left =
      operationalRecord setup leaks bounds horizon scheduler right) :
    operationalState setup leaks first = operationalState setup leaks second := by
  obtain ⟨rest, firstEq⟩ := operationalRecord_head left
  obtain ⟨otherRest, secondEq⟩ := operationalRecord_head right
  rw [firstEq, secondEq] at records
  exact (List.cons.inj records).1

/-- Actual paired histories with the same complete operational record admit
source-weight bounds from initial and content floors and response likelihood
ratios. Chance probabilities agree because public draws are value blind. -/
theorem upperSourceWeight_le_of_paired_responses
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (positive : ∀ n {before after : (application setup leaks).ProtocolState}
      (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
      (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup leaks).Control),
      before = some control → after = some next →
      ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
      0 < responseMass setup leaks bounds horizon scheduler (profiles n) control joint →
      0 < steps.mass n (operationalState setup leaks before) (operationalState setup leaks after))
    (n : ℕ) {ι K₁ ε : ℝ} (ιPos : 0 < ι)
    (initialFloored : ∀ state ∈ (initialLaw setup).support, ι ≤ (initialLaw setup state).toReal)
    (K₁Nonneg : 0 ≤ K₁) (εNonneg : 0 ≤ ε)
    {final imageFinal : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final)
    (imageTop : (onePacketProtocol setup leaks bounds horizon scheduler).Trace imageFinal)
    (records : operationalRecord setup leaks bounds horizon scheduler top =
      operationalRecord setup leaks bounds horizon scheduler imageTop)
    (imageRegular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who imageTop)
    (responseBound : ∀ {control next imageControl imageNext : (application setup leaks).Control}
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some control) joint)
      (realized : some next ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
        (some control) ⟨joint, legal⟩).support)
      (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
        (some imageControl)) imageJoint
      (imageLegal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
        (some imageControl) imageJoint)
      (imageRealized : some imageNext ∈ ((onePacketProtocol setup leaks bounds horizon
        scheduler).step (some imageControl) ⟨imageJoint, imageLegal⟩).support),
      TracePrefix (prior.extend joint legal realized) top →
      TracePrefix (imagePrior.extend imageJoint imageLegal imageRealized) imageTop →
      prior.length = imagePrior.length → ∀ actor, control.actor = some actor → actor ≠ who →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who (some imageControl)
        imageJoint (some imageNext) →
      responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
        K₁ * responseMass setup leaks bounds horizon scheduler (profiles n) imageControl imageJoint)
    (firstBound : ∀ {control next imageControl imageNext : (application setup leaks).Control}
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some control) joint)
      (realized : some next ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
        (some control) ⟨joint, legal⟩).support)
      (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
        (some imageControl)) imageJoint
      (imageLegal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
        (some imageControl) imageJoint)
      (imageRealized : some imageNext ∈ ((onePacketProtocol setup leaks bounds horizon
        scheduler).step (some imageControl) ⟨imageJoint, imageLegal⟩).support),
      TracePrefix (prior.extend joint legal realized) top →
      TracePrefix (imagePrior.extend imageJoint imageLegal imageRealized) imageTop →
      prior.length = imagePrior.length → ∀ actor, control.actor = some actor → actor ≠ who →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who (some imageControl)
        imageJoint (some imageNext) →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who prior →
      ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who (some control) joint
        (some next) →
      responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
        ε * responseMass setup leaks bounds horizon scheduler (profiles n) imageControl imageJoint)
    :
    let K := max 1 (max (max (1 / ι) (1 / contentFloor setup leaks bounds horizon scheduler
      (sequence n))) (K₁ * (1 + steps.error n)))
    upperSourceWeight (IrregularStepBound.ofResponseMass steps positive) n top ≤
        K ^ top.length * othersSourceWeight setup leaks bounds horizon scheduler (sequence n)
          who imageTop ∧
      (¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who top →
        upperSourceWeight (IrregularStepBound.ofResponseMass steps positive) n top ≤
          ε * (1 + steps.error n) * K ^ top.length *
            othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who imageTop) := by
  let K := max 1 (max (max (1 / ι) (1 / contentFloor setup leaks bounds horizon scheduler
    (sequence n))) (K₁ * (1 + steps.error n)))
  have one_le : 1 ≤ K := le_max_left _ _
  have inverseInitial : 1 / ι ≤ K :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have inverseFloor : 1 / contentFloor setup leaks bounds horizon scheduler (sequence n) ≤ K :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have responseFactor : K₁ * (1 + steps.error n) ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  have floorPos := contentFloor_pos setup leaks bounds horizon scheduler (sequence n)
  have sameLength : top.length = imageTop.length := by
    have counted := congrArg List.length records
    rw [operationalRecord_length, operationalRecord_length] at counted
    omega
  refine upperSourceWeight_le_of_paired_steps (IrregularStepBound.ofResponseMass steps positive)
    n one_le (mul_nonneg εNonneg (by linarith [steps.error_nonneg n])) top imageTop sameLength
    ?_ ?_
  · intro before after imageBefore imageAfter prior joint legal realized imagePrior imageJoint
      imageLegal imageRealized isPrefix imagePrefix lengths
    have endpoints := operationalRecord_eq_of_paired_prefixes isPrefix imagePrefix records
      (show (prior.extend joint legal realized).length =
        (imagePrior.extend imageJoint imageLegal imageRealized).length from
        congrArg Nat.succ lengths)
    have afterEq := (List.cons.inj endpoints).1
    have beforeEq := operationalState_eq_of_record_eq prior imagePrior
      (List.cons.inj endpoints).2
    have imageStep := (regularTrace_of_prefix (sequence n) imagePrefix imageRegular).2
    cases before with
    | none =>
        cases imageBefore with
        | some imageControl => cases beforeEq
        | none =>
            cases after with
            | none =>
                cases imageAfter with
                | some imageNext => cases afterEq
                | none =>
                    unfold upperSourceFactor
                    simp only [show RegularStep setup leaks bounds horizon scheduler (sequence n)
                      who none joint none from trivial, ↓reduceIte]
                    change (1 : ℝ) ≤ K * 1
                    linarith
            | some first =>
                cases imageAfter with
                | none => cases afterEq
                | some imageFirst =>
                    change some imageFirst ∈ ((initialLaw setup).map fun state => some
                      (⟨horizon, none, ReactiveApplication.Execution.initial
                        (application setup leaks) state⟩ :
                          (application setup leaks).Control)).support at imageRealized
                    obtain ⟨drawn, drawnMember, drawnEq⟩ := PMF.support_map .. ▸ imageRealized
                    have applicationEq : imageFirst.execution.application = drawn := by
                      rw [← Option.some.inj drawnEq]
                      rfl
                    unfold upperSourceFactor
                    simp only [show RegularStep setup leaks bounds horizon scheduler (sequence n)
                      who none joint (some first) from trivial, ↓reduceIte]
                    change (initialLaw setup first.execution.application).toReal ≤
                      K * (initialLaw setup imageFirst.execution.application).toReal
                    rw [applicationEq]
                    calc (initialLaw setup first.execution.application).toReal ≤ 1 :=
                          ENNReal.toReal_le_of_le_ofReal zero_le_one
                            (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)
                      _ ≤ 1 / ι * (initialLaw setup drawn).toReal := by
                          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ιPos, one_mul]
                          exact initialFloored drawn drawnMember
                      _ ≤ K * (initialLaw setup drawn).toReal :=
                          mul_le_mul_of_nonneg_right inverseInitial ENNReal.toReal_nonneg
    | some control =>
        cases imageBefore with
        | none => cases beforeEq
        | some imageControl =>
            have actors : control.actor = imageControl.actor :=
              congrArg (OperationalState.actor) (Option.some.inj beforeEq)
            cases after with
            | none =>
                cases imageAfter with
                | some imageNext => cases afterEq
                | none =>
                    unfold upperSourceFactor
                    simp only [show RegularStep setup leaks bounds horizon scheduler (sequence n)
                      who (some control) joint none from trivial, ↓reduceIte]
                    change (1 : ℝ) ≤ K * 1
                    linarith
            | some next =>
                cases imageAfter with
                | none => cases afterEq
                | some imageNext =>
                    cases acting : control.actor with
                    | none =>
                        have imageActing : imageControl.actor = none := actors.symm.trans acting
                        have regular : RegularStep setup leaks bounds horizon scheduler
                            (sequence n) who (some control) joint (some next) :=
                          fun actor acted => by rw [acting] at acted; cases acted
                        unfold upperSourceFactor
                        simp only [regular, ↓reduceIte, transitionSourceFactor, acting, imageActing]
                        have chance := completionMass_eq_of_operational_transitions
                          (horizon := horizon) joint imageJoint realized imageRealized
                          beforeEq afterEq
                        rw [chance]
                        exact le_mul_of_one_le_left
                          (completionMass_nonneg (setup := setup) imageControl.execution.application
                            imageNext.execution.application) one_le
                    | some actor =>
                        have imageActing : imageControl.actor = some actor :=
                          actors.symm.trans acting
                        by_cases same : actor = who
                        · have regular : RegularStep setup leaks bounds horizon scheduler
                              (sequence n) who (some control) joint (some next) := by
                            intro other acted different
                            exact (different ((Option.some.inj (acting.symm.trans acted)).symm.trans
                              same)).elim
                          unfold upperSourceFactor
                          simp only [regular, ↓reduceIte, transitionSourceFactor, acting,
                            imageActing, same, ↓reduceIte]
                          linarith
                        · by_cases regular : RegularStep setup leaks bounds horizon scheduler
                              (sequence n) who (some control) joint (some next)
                          · obtain ⟨⟨_, _⟩, imagePositive⟩ := imageStep actor imageActing same
                            have imageFloor := contentFloor_le_of_step (sequence n) imagePrior
                              imageJoint imageLegal imageRealized imageControl imageNext rfl rfl
                              actor imagePositive
                            unfold upperSourceFactor
                            simp only [regular, ↓reduceIte, transitionSourceFactor, acting,
                              imageActing, same, ↓reduceIte]
                            calc contentFactor setup leaks (sequence n) actor control.execution
                                  next.execution ((joint actor).getD ⟨none⟩) ≤ 1 :=
                                  contentFactor_le_one setup leaks (sequence n) actor
                                    control.execution next.execution ((joint actor).getD ⟨none⟩)
                              _ ≤ 1 / contentFloor setup leaks bounds horizon scheduler
                                  (sequence n) * contentFactor setup leaks (sequence n) actor
                                    imageControl.execution imageNext.execution
                                      ((imageJoint actor).getD ⟨none⟩) := by
                                  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ floorPos, one_mul]
                                  exact imageFloor
                              _ ≤ _ := mul_le_mul_of_nonneg_right inverseFloor imagePositive.le
                          · have ratio := responseBound prior joint legal realized imagePrior
                              imageJoint imageLegal imageRealized isPrefix imagePrefix lengths
                              actor acting same imageStep
                            exact (irregularSourceFactor_le_of_paired_response positive n imagePrior
                              joint imageJoint imageLegal imageRealized imageActing same regular
                              imageStep beforeEq.symm afterEq.symm K₁Nonneg ratio).trans
                              (mul_le_mul_of_nonneg_right responseFactor
                                (transitionSourceFactor_nonneg (sequence n) who _ _ _))
  · intro before after imageBefore imageAfter prior joint legal realized imagePrior imageJoint
      imageLegal imageRealized isPrefix imagePrefix lengths
    have endpoints := operationalRecord_eq_of_paired_prefixes isPrefix imagePrefix records
      (show (prior.extend joint legal realized).length =
        (imagePrior.extend imageJoint imageLegal imageRealized).length from
        congrArg Nat.succ lengths)
    have afterEq := (List.cons.inj endpoints).1
    have beforeEq := operationalState_eq_of_record_eq prior imagePrior
      (List.cons.inj endpoints).2
    have imageStep := (regularTrace_of_prefix (sequence n) imagePrefix imageRegular).2
    intro regularPrior irregularStep
    cases before with
    | none => exact (irregularStep trivial).elim
    | some control =>
        cases after with
        | none => exact (irregularStep trivial).elim
        | some next =>
            cases imageBefore with
            | none => cases beforeEq
            | some imageControl =>
                cases imageAfter with
                | none => cases afterEq
                | some imageNext =>
                    have actors : control.actor = imageControl.actor :=
                      congrArg (OperationalState.actor) (Option.some.inj beforeEq)
                    cases acting : control.actor with
                    | none =>
                        exact (irregularStep fun actor acted => by
                          rw [acting] at acted; cases acted).elim
                    | some actor =>
                        by_cases same : actor = who
                        · apply (irregularStep ?_).elim
                          intro other acted different
                          exact (different ((Option.some.inj (acting.symm.trans acted)).symm.trans
                            same)).elim
                        · have imageActing : imageControl.actor = some actor :=
                            actors.symm.trans acting
                          have ratio := firstBound prior joint legal realized imagePrior imageJoint
                            imageLegal imageRealized isPrefix imagePrefix lengths actor acting same
                            imageStep regularPrior irregularStep
                          exact irregularSourceFactor_le_of_paired_response positive n imagePrior
                            joint imageJoint imageLegal imageRealized imageActing same irregularStep
                            imageStep beforeEq.symm afterEq.symm εNonneg ratio

end Vegas
