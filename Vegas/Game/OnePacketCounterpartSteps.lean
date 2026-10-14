/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartWeight
import Vegas.Game.OnePacketSwapRecord
import Vegas.Game.OnePacketIrregularBound
import Vegas.Game.OnePacketContentFloor

/-! # Step factors of a history and its swap image

A hidden swap fixes every chance draw, so the chance mass of a completion is
that of its swap (`Vegas.completionMass_swap`). Comparing a native history with
its image under the swap symmetry, step by step, when the image is regular:

* a chance or scheduler step, and a response of the observer, has the same
  source factor as its image;
* the initial draw has source factor at most one, while its image's is at
  least the initial floor;
* a regular response of another player has content factor at most one, while
  its image's is at least the content floor;
* an irregular response has upper factor its response mass divided by the
  operational mass, which the image's factorization bounds by the response
  mass of the image's response divided by its content factor.

So under a bound `K₁` on the ratio of the response masses of a response and its
image, and a bound `ε` at the first irregular response, the upper source weight
of an irregular history is at most `ε (1 + error)` times `K` to its length
times the source weight of its image, with `K` the largest of the inverse
floors and `K₁ (1 + error)` (`Vegas.upperSourceWeight_le_swap`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **A hidden swap fixes chance masses.** -/
theorem completionMass_swap (swap : HiddenSwap (graph setup))
    (before after : EventGraphRuntime.State (graph setup)) :
    completionMass setup (before.swap swap) (after.swap swap) =
      completionMass setup before after := by
  unfold completionMass
  simp only [State.swap_config, EventGraph.Config.swap_history, List.length_map]
  rw [← List.map_drop]
  generalize after.config.history.drop before.config.history.length = completed
  rcases completed with _ | ⟨⟨event, action⟩, _ | ⟨_, _⟩⟩
  · rfl
  · change (match (graph setup).actor? event with
        | none =>
            if ready : (before.config.swap swap.values).cut.Ready event then
              ((before.config.swap swap.values).step event ready
                (swap.values.action event action) (after.config.swap swap.values)).toReal
            else 0
        | some _ => 1) = (match (graph setup).actor? event with
        | none =>
            if ready : before.config.cut.Ready event then
              (before.config.step event ready action after.config).toReal
            else 0
        | some _ => 1)
    cases acts : (graph setup).actor? event with
    | some _ => rfl
    | none =>
        simp only [EventGraph.Config.swap_cut]
        split_ifs with ready
        · have fixed : EventGraph.ResolutionFixed swap.values event := by
            unfold EventGraph.ResolutionFixed
            cases view : nodeView (graph setup) event with
            | bind owner payload outputEq codeEq =>
                rw [nodeView_bind_actor outputEq codeEq] at acts
                cases acts
            | resolve owner payload binding checks outputEq codeEq =>
                rw [nodeView_resolve_actor outputEq codeEq] at acts
                cases acts
            | sample => trivial
          rw [EventGraph.Config.step_swap swap.values before.config event ready action fixed,
            pmf_map_apply_of_injective _ (EventGraph.Config.swap_involutive swap.values).injective]
        · rfl
  · rfl

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    profiles who}
  {allowed : Set (graph setup).Inputs}

/-- **Upper source weights against a swap image.** For a hidden swap acting as
a state symmetry of the one-packet game, an irregular history whose image is
regular has upper source weight, under the response-mass irregular bound, at
most `ε (1 + error)` times `K` to its length times the source weight of its
image, where the initial draws have mass at least `ι`, the response masses of
the history are at most `K₁` times those of the image, and at most `ε` times
at the first irregular response. -/
theorem upperSourceWeight_le_swap [Finite (onePacketProtocol setup leaks bounds horizon
      scheduler).History]
    (positive : ∀ n {before after : (application setup leaks).ProtocolState}
      (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
      (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup leaks).Control),
      before = some control → after = some next →
      ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
      0 < responseMass setup leaks bounds horizon scheduler (profiles n) control joint →
      0 < steps.mass n (operationalState setup leaks before) (operationalState setup leaks after))
    (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (n : ℕ) {ι K₁ ε : ℝ} (ιPos : 0 < ι)
    (initialFloored : ∀ state ∈ (initialLaw setup).support, ι ≤ (initialLaw setup state).toReal)
    (K₁Nonneg : 0 ≤ K₁) (εNonneg : 0 ≤ ε)
    {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (guarded : SwapGuardState setup swap allowed state)
    (responseBound : ∀ {before after} (prior : (onePacketProtocol setup leaks bounds horizon
        scheduler).Trace before) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
      (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support), TracePrefix (prior.extend joint legal realized) trace →
      SwapGuardState setup swap allowed after →
      ∀ (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
        (swap.protocolState before))
      (imageLegal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
        (swap.protocolState before) (swap.joint joint)),
      swap.protocolState after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
        (swap.protocolState before) ⟨swap.joint joint, imageLegal⟩).support →
      ∀ (control next : (application setup leaks).Control) (actor : Player),
      before = some control → after = some next → control.actor = some actor → actor ≠ who →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who
        (swap.protocolState before) (swap.joint joint) (swap.protocolState after) →
      responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
        K₁ * responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
          (swap.joint joint))
    (firstBound : ∀ {before after} (prior : (onePacketProtocol setup leaks bounds horizon
        scheduler).Trace before) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
      (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support), TracePrefix (prior.extend joint legal realized) trace →
      SwapGuardState setup swap allowed after →
      ∀ (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
        (swap.protocolState before))
      (imageLegal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
        (swap.protocolState before) (swap.joint joint)),
      swap.protocolState after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
        (swap.protocolState before) ⟨swap.joint joint, imageLegal⟩).support →
      ∀ (control next : (application setup leaks).Control) (actor : Player),
      before = some control → after = some next → control.actor = some actor → actor ≠ who →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who
        (swap.protocolState before) (swap.joint joint) (swap.protocolState after) →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who prior →
      ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
      responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
        ε * responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
          (swap.joint joint))
    (imageRegular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
        bounded).mapTrace trace guarded))
    (irregularTrace : ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who trace) :
    upperSourceWeight (IrregularStepBound.ofResponseMass steps positive) n trace ≤
      ε * (1 + steps.error n) *
        max 1 (max (max (1 / ι) (1 / contentFloor setup leaks bounds horizon scheduler
          (sequence n))) (K₁ * (1 + steps.error n))) ^ trace.length *
        othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who
          ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
            bounded).mapTrace trace guarded) := by
  set symmetry := onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
    initialClosed bounded with symmetryEq
  set K := max 1 (max (max (1 / ι) (1 / contentFloor setup leaks bounds horizon scheduler
    (sequence n))) (K₁ * (1 + steps.error n))) with KEq
  have errorNonneg := steps.error_nonneg n
  have floorPos := contentFloor_pos setup leaks bounds horizon scheduler (sequence n)
  have one_le : 1 ≤ K := le_max_left _ _
  have inverseInitial : 1 / ι ≤ K :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have inverseFloor : 1 / contentFloor setup leaks bounds horizon scheduler (sequence n) ≤ K :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have responseFactor : K₁ * (1 + steps.error n) ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  -- The image's response mass is at most its content factor times the operational mass.
  have imageResponse : ∀ {before after} (prior : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace before) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
      (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (guardAfter : SwapGuardState setup swap allowed after)
      (control next : (application setup leaks).Control) (actor : Player),
      before = some control → after = some next →
      control.actor = some actor → actor ≠ who →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who (symmetry.map before)
        (symmetry.act before joint) (symmetry.map after) →
      responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
          (swap.joint joint) ≤
        (1 + steps.error n) * (contentFactor setup leaks (sequence n) actor
          (swap.control control).execution (swap.control next).execution
          ((swap.joint joint actor).getD ⟨none⟩) *
          steps.mass n (operationalState setup leaks before)
            (operationalState setup leaks after)) := by
    intro before after prior joint legal realized guardAfter control next actor beforeEq
      afterEq acting other imageStep
    have guardBefore := symmetry.guard_source prior legal realized guardAfter
    have imageLegal := symmetry.legal prior legal realized guardAfter
    have imageRealized := symmetry.realized prior legal realized guardAfter
    have imagePrior := symmetry.mapTrace prior guardBefore
    subst beforeEq afterEq
    obtain ⟨⟨forcedActor, forcedWho⟩, imagePositive⟩ := imageStep actor acting other
    have component := steps.component n imagePrior (swap.joint joint) imageLegal imageRealized
      (swap.control control) (swap.control next) actor rfl rfl acting other forcedActor
      forcedWho imagePositive
    rw [stepProb_eq_responseMass (profiles n) imagePrior (swap.joint joint) imageLegal
      imageRealized (swap.control control) rfl acting] at component
    have guardBeforeSwap : SwapGuardState setup swap allowed (some control) := guardBefore
    rw [show operationalState setup leaks (symmetry.map (some control)) =
        operationalState setup leaks (some control) from
          operationalState_swap swap _ guardBeforeSwap,
      show operationalState setup leaks (symmetry.map (some next)) =
        operationalState setup leaks (some next) from
          operationalState_swap swap _ guardAfter] at component
    have upper := (abs_le.mp component).2
    linarith
  refine (upperSourceWeight_le_mapTrace (IrregularStepBound.ofResponseMass steps positive) n
    symmetry one_le (mul_nonneg εNonneg (by linarith)) trace ?_ ?_ trace guarded .refl
    imageRegular).2
    irregularTrace
  · intro before after prior joint legal realized isPrefix guardAfter imageStep
    cases before with
    | none =>
        cases after with
        | none =>
            unfold upperSourceFactor
            simp only [show RegularStep setup leaks bounds horizon scheduler (sequence n) who none
              joint none from trivial, ↓reduceIte]
            change (1 : ℝ) ≤ K * 1
            linarith
        | some first =>
            have imageRealized := symmetry.realized prior legal realized guardAfter
            change some (swap.control first) ∈ ((initialLaw setup).map fun state => some
              (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
                state⟩ : (application setup leaks).Control)).support at imageRealized
            obtain ⟨drawn, drawnMember, drawnEq⟩ := PMF.support_map .. ▸ imageRealized
            have drawnFloor := initialFloored drawn drawnMember
            have applicationEq : (swap.control first).execution.application = drawn := by
              rw [← Option.some.inj drawnEq]
              rfl
            unfold upperSourceFactor
            simp only [show RegularStep setup leaks bounds horizon scheduler (sequence n) who none
              joint (some first) from trivial, ↓reduceIte]
            change (initialLaw setup first.execution.application).toReal ≤
              K * (initialLaw setup (swap.control first).execution.application).toReal
            rw [applicationEq]
            have massLe : (initialLaw setup first.execution.application).toReal ≤ 1 :=
              ENNReal.toReal_le_of_le_ofReal zero_le_one
                (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)
            calc (initialLaw setup first.execution.application).toReal ≤ 1 := massLe
              _ ≤ 1 / ι * (initialLaw setup drawn).toReal := by
                rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ιPos, one_mul]
                exact drawnFloor
              _ ≤ K * (initialLaw setup drawn).toReal :=
                mul_le_mul_of_nonneg_right inverseInitial ENNReal.toReal_nonneg
    | some control =>
        cases after with
        | none =>
            unfold upperSourceFactor
            simp only [show RegularStep setup leaks bounds horizon scheduler (sequence n) who
              (some control) joint none from trivial, ↓reduceIte]
            change (1 : ℝ) ≤ K * 1
            linarith
        | some next =>
            cases acting : control.actor with
            | none =>
                have regular : RegularStep setup leaks bounds horizon scheduler (sequence n) who
                    (some control) joint (some next) := fun actor acted => by
                  rw [acting] at acted
                  cases acted
                unfold upperSourceFactor
                simp only [regular, ↓reduceIte]
                change transitionSourceFactor setup leaks (sequence n) who (some control) joint
                  (some next) ≤ K * transitionSourceFactor setup leaks (sequence n) who
                    (some (swap.control control)) (swap.joint joint) (some (swap.control next))
                unfold transitionSourceFactor
                have imageActing : (swap.control control).actor = none := acting
                simp only [acting, imageActing]
                change completionMass setup control.execution.application
                    next.execution.application ≤ K * completionMass setup
                      (control.execution.application.swap swap)
                      (next.execution.application.swap swap)
                rw [completionMass_swap]
                nlinarith [completionMass_nonneg (setup := setup) control.execution.application
                  next.execution.application]
            | some actor =>
                by_cases same : actor = who
                · subst same
                  have regular : RegularStep setup leaks bounds horizon scheduler (sequence n)
                      actor (some control) joint (some next) := fun _ acted different => by
                    rw [acting] at acted
                    exact (different (Option.some.inj acted).symm).elim
                  unfold upperSourceFactor
                  simp only [regular, ↓reduceIte]
                  change transitionSourceFactor setup leaks (sequence n) actor (some control) joint
                    (some next) ≤ K * transitionSourceFactor setup leaks (sequence n) actor
                      (some (swap.control control)) (swap.joint joint) (some (swap.control next))
                  unfold transitionSourceFactor
                  have imageActing : (swap.control control).actor = some actor := acting
                  simp only [acting, imageActing, ↓reduceIte]
                  linarith
                · have imageFactor : transitionSourceFactor setup leaks (sequence n) who
                      (some (swap.control control)) (swap.joint joint) (some (swap.control next)) =
                      contentFactor setup leaks (sequence n) actor (swap.control control).execution
                        (swap.control next).execution ((swap.joint joint actor).getD ⟨none⟩) := by
                    unfold transitionSourceFactor
                    have imageActing : (swap.control control).actor = some actor := acting
                    simp only [imageActing, same, ↓reduceIte]
                  change upperSourceFactor (IrregularStepBound.ofResponseMass steps positive) n
                    (some control) joint (some next) ≤ K * transitionSourceFactor setup leaks
                      (sequence n) who (some (swap.control control)) (swap.joint joint)
                      (some (swap.control next))
                  rw [imageFactor]
                  obtain ⟨⟨_, _⟩, imagePositive⟩ := imageStep actor acting same
                  have imageFloor := contentFloor_le_of_step (sequence n)
                    (symmetry.mapTrace prior
                      (symmetry.guard_source prior legal realized guardAfter))
                    (swap.joint joint) (symmetry.legal prior legal realized guardAfter)
                    (symmetry.realized prior legal realized guardAfter) (swap.control control)
                    (swap.control next) rfl rfl actor imagePositive
                  by_cases regular : RegularStep setup leaks bounds horizon scheduler (sequence n)
                      who (some control) joint (some next)
                  · unfold upperSourceFactor
                    simp only [regular, ↓reduceIte]
                    unfold transitionSourceFactor
                    simp only [acting, same, ↓reduceIte]
                    have contentLe := contentFactor_le_one setup leaks (sequence n) actor
                      control.execution next.execution ((joint actor).getD ⟨none⟩)
                    calc contentFactor setup leaks (sequence n) actor control.execution
                          next.execution ((joint actor).getD ⟨none⟩) ≤ 1 := contentLe
                      _ ≤ 1 / contentFloor setup leaks bounds horizon scheduler (sequence n) *
                          contentFactor setup leaks (sequence n) actor
                            (swap.control control).execution (swap.control next).execution
                            ((swap.joint joint actor).getD ⟨none⟩) := by
                        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ floorPos, one_mul]
                        exact imageFloor
                      _ ≤ _ := mul_le_mul_of_nonneg_right inverseFloor imagePositive.le
                  · unfold upperSourceFactor
                    simp only [regular, ↓reduceIte]
                    change responseMass setup leaks bounds horizon scheduler (profiles n) control
                        joint / steps.mass n (operationalState setup leaks (some control))
                          (operationalState setup leaks (some next)) ≤ _
                    have imageBound := imageResponse prior joint legal realized guardAfter control
                      next actor rfl rfl acting same imageStep
                    have guardBefore := symmetry.guard_source prior legal realized guardAfter
                    have ratio := responseBound prior joint legal realized isPrefix guardAfter
                      (symmetry.mapTrace prior guardBefore) (symmetry.legal prior legal realized
                        guardAfter) (symmetry.realized prior legal realized guardAfter)
                      control next actor rfl rfl acting same imageStep
                    set mass := steps.mass n (operationalState setup leaks (some control))
                      (operationalState setup leaks (some next))
                    set content := contentFactor setup leaks (sequence n) actor
                      (swap.control control).execution (swap.control next).execution
                      ((swap.joint joint actor).getD ⟨none⟩)
                    have massNonneg : 0 ≤ mass := steps.mass_nonneg _ _ _
                    rcases massNonneg.lt_or_eq with massPos | massZero
                    · rw [div_le_iff₀ massPos]
                      calc responseMass setup leaks bounds horizon scheduler (profiles n) control
                            joint ≤ K₁ * ((1 + steps.error n) * (content * mass)) :=
                          ratio.trans (mul_le_mul_of_nonneg_left imageBound K₁Nonneg)
                        _ = K₁ * (1 + steps.error n) * content * mass := by ring
                        _ ≤ K * content * mass := by
                          apply mul_le_mul_of_nonneg_right _ massNonneg
                          exact mul_le_mul_of_nonneg_right responseFactor imagePositive.le
                    · rw [← massZero, div_zero]
                      exact mul_nonneg (by linarith) imagePositive.le
  · intro before after prior joint legal realized isPrefix guardAfter imageStep regularPrior
      irregularStep
    cases before with
    | none => exact (irregularStep trivial).elim
    | some control =>
        cases after with
        | none => exact (irregularStep trivial).elim
        | some next =>
            cases acting : control.actor with
            | none =>
                exact (irregularStep fun actor acted => by rw [acting] at acted; cases acted).elim
            | some actor =>
                by_cases same : actor = who
                · subst same
                  exact (irregularStep fun _ acted different => by
                    rw [acting] at acted
                    exact (different (Option.some.inj acted).symm).elim).elim
                · have imageFactor : transitionSourceFactor setup leaks (sequence n) who
                      (some (swap.control control)) (swap.joint joint) (some (swap.control next)) =
                      contentFactor setup leaks (sequence n) actor (swap.control control).execution
                        (swap.control next).execution ((swap.joint joint actor).getD ⟨none⟩) := by
                    unfold transitionSourceFactor
                    have imageActing : (swap.control control).actor = some actor := acting
                    simp only [imageActing, same, ↓reduceIte]
                  change upperSourceFactor (IrregularStepBound.ofResponseMass steps positive) n
                    (some control) joint (some next) ≤ ε * (1 + steps.error n) *
                      transitionSourceFactor setup leaks (sequence n) who
                        (some (swap.control control)) (swap.joint joint) (some (swap.control next))
                  rw [imageFactor]
                  obtain ⟨⟨_, _⟩, imagePositive⟩ := imageStep actor acting same
                  unfold upperSourceFactor
                  simp only [irregularStep, ↓reduceIte]
                  change responseMass setup leaks bounds horizon scheduler (profiles n) control
                      joint / steps.mass n (operationalState setup leaks (some control))
                        (operationalState setup leaks (some next)) ≤ _
                  have imageBound := imageResponse prior joint legal realized guardAfter control
                    next actor rfl rfl acting same imageStep
                  have ratio := firstBound prior joint legal realized isPrefix guardAfter
                    (symmetry.mapTrace prior
                      (symmetry.guard_source prior legal realized guardAfter))
                    (symmetry.legal prior legal realized guardAfter)
                    (symmetry.realized prior legal realized guardAfter) control next actor rfl rfl
                    acting same imageStep regularPrior irregularStep
                  set mass := steps.mass n (operationalState setup leaks (some control))
                    (operationalState setup leaks (some next))
                  set content := contentFactor setup leaks (sequence n) actor
                    (swap.control control).execution (swap.control next).execution
                    ((swap.joint joint actor).getD ⟨none⟩)
                  have massNonneg : 0 ≤ mass := steps.mass_nonneg _ _ _
                  rcases massNonneg.lt_or_eq with massPos | massZero
                  · rw [div_le_iff₀ massPos]
                    calc responseMass setup leaks bounds horizon scheduler (profiles n) control
                          joint ≤ ε * ((1 + steps.error n) * (content * mass)) :=
                        ratio.trans (mul_le_mul_of_nonneg_left imageBound εNonneg)
                      _ = ε * (1 + steps.error n) * content * mass := by ring
                  · rw [← massZero, div_zero]
                    exact mul_nonneg (mul_nonneg εNonneg (by linarith)) imagePositive.le

end Vegas
