/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketForcedRegular

/-! # Honest counterparts dominate through the operational factorization

**Irregular steps.** A response of another player that is not regular, such as
a native-only bad binding, is bounded by a given *irregular bound* times the
operational mass of its transition (`Vegas.IrregularStepBound`); under
slot-trembled components such a response is in the full-menu tier, of mass at
most the cube of the scale.

**The upper source weight** of a native history multiplies the source factor
at every regular transition and the irregular bound at every irregular
response (`Vegas.upperSourceWeight`). Under operational steps and an irregular
step bound, the reach of every history is at most its upper source weight
times the operational weight of its record times the owner mass of the
observer's recall, up to the factorization error
(`Vegas.reach_le_upperWeight`).

**Counterparts.** A regular history with the same operational record and the
same recall of the observer has reach at least its source weight times the same
two factors, up to the same error. So if the upper source weight of a history
is at most `ratio` times the source weight of such a counterpart, the reach of
the history is at most `(1 + error) / (1 - error)` times `ratio` times the
reach of the counterpart (`Vegas.reach_le_of_counterpart`). No hypothesis on
the scheduler enters: the operational masses of the two histories are equal,
whatever they are. This yields the counterpart inputs of forced beliefs
(`Vegas.counterpart_fields_of_domination`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

variable (setup leaks bounds horizon scheduler) in
/-- **An irregular step bound.** At every irregular response of another
player, the response mass is at most a nonnegative bound times the operational
mass of its transition. -/
structure IrregularStepBound {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who) where
  /-- The bound of an irregular response. -/
  bound : ℕ → (application setup leaks).Control →
    (Player → Option (application setup leaks).Action) → (application setup leaks).Control → ℝ
  bound_nonneg : ∀ n before joint after, 0 ≤ bound n before joint after
  step_le : ∀ n {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control next : (application setup leaks).Control),
    before = some control → after = some next →
    ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
    InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
        (profiles n) prior ⟨joint, legal⟩ after ≤
      bound n control joint next *
        steps.mass n (operationalState setup leaks before) (operationalState setup leaks after)

section Weights

variable {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    profiles who}

open Classical in
/-- The upper source factor of a transition: the source factor at a regular
transition, and the irregular bound at an irregular response. -/
def upperSourceFactor (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps)
    (n : ℕ) (before : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (after : (application setup leaks).ProtocolState) : ℝ :=
  if RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after then
    transitionSourceFactor setup leaks (sequence n) who before joint after
  else
    match before, after with
    | some control, some next => irregular.bound n control joint next
    | _, _ => transitionSourceFactor setup leaks (sequence n) who before joint after

/-- **The upper source weight** of a native history. -/
def upperSourceWeight (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps)
    (n : ℕ) : ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → ℝ
  | _, .start => 1
  | _, .extend (source := before) (target := after) prior joint _ _ =>
      upperSourceWeight irregular n prior * upperSourceFactor irregular n before joint after

theorem upperSourceFactor_nonneg
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ)
    (before : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (after : (application setup leaks).ProtocolState) :
    0 ≤ upperSourceFactor irregular n before joint after := by
  unfold upperSourceFactor
  split_ifs
  · exact transitionSourceFactor_nonneg _ _ _ _ _
  · split
    · exact irregular.bound_nonneg _ _ _ _
    · exact transitionSourceFactor_nonneg _ _ _ _ _

theorem upperSourceWeight_nonneg
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
      0 ≤ upperSourceWeight irregular n trace
  | _, .start => zero_le_one
  | _, .extend prior _ _ _ =>
      mul_nonneg (upperSourceWeight_nonneg irregular n prior)
        (upperSourceFactor_nonneg irregular n _ _ _)

/-- The upper weight of a native history: its upper source weight times the
operational weight of its record times the owner mass of the observer's
recall. -/
def upperWeight (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps)
    (n : ℕ) {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) : ℝ :=
  upperSourceWeight irregular n trace *
    operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler trace) *
    ownerMass setup leaks bounds horizon scheduler (profiles n who)
      (ownerRecall setup leaks who state)

theorem upperWeight_nonneg
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ)
    {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    0 ≤ upperWeight irregular n trace :=
  mul_nonneg (mul_nonneg (upperSourceWeight_nonneg irregular n trace)
    (operationalWeight_nonneg setup leaks (steps.mass_nonneg n) _))
    (ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _)

/-- **Reach is at most the upper weight**, up to the factorization error of
each step. -/
theorem reach_le_upperWeight
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
      ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) ⟨state, trace⟩).toReal ≤
        (1 + steps.error n) ^ trace.length * upperWeight irregular n trace
  | _, .start => by
      have reach := (onePacketInformation setup leaks bounds horizon
        scheduler).historyReachWeight_initHistory (profiles n)
      change ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
        (profiles n) (onePacketProtocol setup leaks bounds horizon scheduler).initHistory).toReal
          ≤ _
      have weight : upperWeight irregular n
          (Trace.start : (onePacketProtocol setup leaks bounds horizon scheduler).Trace _) = 1 := by
        change 1 * 1 * ownerMassFrom setup leaks bounds horizon scheduler (profiles n who) [] [] = 1
        simp [ownerMassFrom]
      rw [reach, weight]
      simp [ExecutionProtocol.Trace.length]
  | _, .extend (source := before) (target := after) prior joint legal realized => by
      have previous := reach_le_upperWeight irregular n prior
      rw [InformationModel.historyReachProbability_extend]
      obtain ⟨rest, record⟩ := operationalRecord_head prior
      have stepNonneg : 0 ≤ InformationModel.stepProb
          (onePacketInformation setup leaks bounds horizon scheduler) (profiles n) prior
          ⟨joint, legal⟩ after := by
        unfold InformationModel.stepProb
        exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have reachNonneg := ENNReal.toReal_nonneg (a :=
        (onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) ⟨before, prior⟩)
      have errorNonneg := steps.error_nonneg n
      have powerNonneg : 0 ≤ (1 + steps.error n) ^ prior.length := by positivity
      -- Bound the step by a factor with the upper weight equation.
      obtain ⟨factor, factorNonneg, stepLe, equation⟩ : ∃ factor, 0 ≤ factor ∧
          InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
            (profiles n) prior ⟨joint, legal⟩ after ≤ (1 + steps.error n) * factor ∧
          upperSourceFactor irregular n before joint after *
              operationalFactor setup leaks who (steps.mass n)
                (operationalState setup leaks before) (operationalState setup leaks after) *
              ownerMass setup leaks bounds horizon scheduler (profiles n who)
                (ownerRecall setup leaks who after) =
            ownerMass setup leaks bounds horizon scheduler (profiles n who)
              (ownerRecall setup leaks who before) * factor := by
        by_cases regularStep : RegularStep setup leaks bounds horizon scheduler (sequence n) who
            before joint after
        · obtain ⟨factor, factorNonneg, close, equation⟩ :=
            step_factor steps n prior joint legal realized regularStep
          refine ⟨factor, factorNonneg, ?_, ?_⟩
          · have := (abs_le.mp close).2
            linarith
          · unfold upperSourceFactor
            simp only [regularStep, ↓reduceIte]
            exact equation
        · cases before with
          | none => exact (regularStep trivial).elim
          | some control =>
              cases after with
              | none => exact (regularStep trivial).elim
              | some next =>
                  obtain ⟨actor, acting, other, _⟩ : ∃ actor, control.actor = some actor ∧
                      actor ≠ who ∧ True := by
                    by_contra none_
                    apply regularStep
                    intro actor acting other
                    exact (none_ ⟨actor, acting, other, trivial⟩).elim
                  have bound := irregular.step_le n prior joint legal realized control next rfl rfl
                    regularStep
                  refine ⟨irregular.bound n control joint next * steps.mass n
                    (operationalState setup leaks (some control))
                    (operationalState setup leaks (some next)),
                    mul_nonneg (irregular.bound_nonneg _ _ _ _) (steps.mass_nonneg _ _ _), ?_, ?_⟩
                  · nlinarith [mul_nonneg (irregular.bound_nonneg n control joint next)
                      (steps.mass_nonneg n (operationalState setup leaks (some control))
                        (operationalState setup leaks (some next)))]
                  · change some next ∈ ((application setup leaks).transition (initialLaw setup)
                      horizon scheduler (some control) joint).support at realized
                    rw [transition_respond control acting joint, PMF.mem_support_pure_iff]
                      at realized
                    cases Option.some.inj realized
                    have actorNe : ¬ control.actor = some who := by
                      rw [acting]
                      exact fun same => other (Option.some.inj same)
                    unfold upperSourceFactor
                    simp only [regularStep, operationalFactor_operationalState, actorNe,
                      ↓reduceIte,
                      ownerRecall, (application setup leaks).respond_recall_other control.execution
                        actor who (Ne.symm other)]
                    ring
      have weightEq : upperWeight irregular n (prior.extend joint legal realized) =
          upperWeight irregular n prior * factor := by
        unfold upperWeight
        simp only [upperSourceWeight, operationalRecord, record, operationalWeight]
        linear_combination (upperSourceWeight irregular n prior * operationalWeight setup leaks who
          (steps.mass n) (operationalState setup leaks before :: rest)) * equation
      rw [weightEq]
      simp only [ExecutionProtocol.Trace.length, pow_succ]
      calc _ ≤ ((1 + steps.error n) ^ prior.length * upperWeight irregular n prior) *
            ((1 + steps.error n) * factor) :=
          mul_le_mul previous stepLe stepNonneg (mul_nonneg powerNonneg
            (upperWeight_nonneg irregular n prior))
        _ = _ := by ring

/-- The reach of a history is at most its upper weight up to the uniform
factorization error. -/
theorem reach_le_upperWeight_uniform
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ)
    {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
        (profiles n) ⟨state, trace⟩).toReal ≤
      (1 + steps.error n) ^ (2 * horizon + 1) * upperWeight irregular n trace := by
  refine (reach_le_upperWeight irregular n trace).trans ?_
  apply mul_le_mul_of_nonneg_right _ (upperWeight_nonneg irregular n trace)
  have length := trace_length_le trace
  exact pow_le_pow_right₀ (by linarith [steps.error_nonneg n]) (by omega)

/-- **Domination by a counterpart.** If a regular history with the same
operational record and the same recall of the observer has source weight at
least the upper source weight of a history divided by `ratio`, then the reach
of the history is at most `(1 + error) / (1 - error)` times `ratio` times the
reach of the counterpart, where `error` is the uniform factorization error. -/
theorem reach_le_of_counterpart
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ)
    {state other : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (counterpart : (onePacketProtocol setup leaks bounds horizon scheduler).Trace other)
    (regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who counterpart)
    (record : operationalRecord setup leaks bounds horizon scheduler counterpart =
      operationalRecord setup leaks bounds horizon scheduler trace)
    (sameRecall : ownerRecall setup leaks who other = ownerRecall setup leaks who state)
    {ratio : ℝ} (ratioNonneg : 0 ≤ ratio)
    (dominated : upperSourceWeight irregular n trace ≤
      ratio * othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who
        counterpart)
    (small : (1 + steps.error n) ^ (2 * horizon + 1) - 1 < 1) :
    ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
        (profiles n) ⟨state, trace⟩).toReal ≤
      (1 + ((1 + steps.error n) ^ (2 * horizon + 1) - 1)) /
          (1 - ((1 + steps.error n) ^ (2 * horizon + 1) - 1)) * ratio *
        ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) ⟨other, counterpart⟩).toReal := by
  set error := (1 + steps.error n) ^ (2 * horizon + 1) - 1 with errorEq
  have errorNonneg : 0 ≤ error := by
    have := one_le_pow₀ (n := 2 * horizon + 1)
      (show (1 : ℝ) ≤ 1 + steps.error n by linarith [steps.error_nonneg n])
    linarith
  set common := operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler trace) *
    ownerMass setup leaks bounds horizon scheduler (profiles n who)
      (ownerRecall setup leaks who state) with commonEq
  have commonNonneg : 0 ≤ common :=
    mul_nonneg (operationalWeight_nonneg setup leaks (steps.mass_nonneg n) _)
      (ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _)
  have upper := reach_le_upperWeight_uniform irregular n trace
  have upperEq : upperWeight irregular n trace = upperSourceWeight irregular n trace * common := by
    unfold upperWeight
    rw [commonEq]
    ring
  have close := (onePacketReachFactorization steps).2 n counterpart regular
  have counterpartEq : factoredWeight sequence profiles steps n counterpart =
      othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who counterpart *
        common := by
    unfold factoredWeight
    rw [record, sameRecall, commonEq]
    ring
  rw [counterpartEq] at close
  have lower := (abs_le.mp close).1
  set counterpartReach := ((onePacketInformation setup leaks bounds horizon
    scheduler).historyReachWeight (profiles n) ⟨other, counterpart⟩).toReal
  have weightNonneg := mul_nonneg
    (othersSourceWeight_nonneg (sequence n) who counterpart) commonNonneg
  have positive : 0 < 1 - error := by linarith
  have reachLower : (1 - error) * (othersSourceWeight setup leaks bounds horizon scheduler
      (sequence n) who counterpart * common) ≤ counterpartReach := by linarith
  rw [upperEq] at upper
  have chain : (1 + error) * (upperSourceWeight irregular n trace * common) ≤
      (1 + error) * (ratio * othersSourceWeight setup leaks bounds horizon scheduler
        (sequence n) who counterpart * common) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right dominated commonNonneg)
      (by linarith)
  calc _ ≤ (1 + error) * (upperSourceWeight irregular n trace * common) := by
        rw [show (1 + steps.error n) ^ (2 * horizon + 1) = 1 + error by rw [errorEq]; ring]
          at upper
        exact upper
    _ ≤ (1 + error) * ratio * (othersSourceWeight setup leaks bounds horizon scheduler
          (sequence n) who counterpart * common) := by nlinarith [chain]
    _ ≤ (1 + error) / (1 - error) * ratio * counterpartReach := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ positive]
        have : 0 ≤ (1 + error) * ratio := mul_nonneg (by linarith) ratioNonneg
        nlinarith [mul_le_mul_of_nonneg_left reachLower this]

end Weights

/-- **Counterpart inputs from domination.** If the reach of every irregular
history is at most `slack * scale / floor ^ depth` times the reach of its
counterpart, the counterpart inputs of `Vegas.ForcedBeliefInputs` hold with the
common weight the reach divided by the cube of the scale. -/
theorem counterpart_fields_of_domination {α : Type*} (reach : α → ℝ) (counterpart : α → α)
    {scale floor slack : ℝ} {depth : ℕ} (scalePos : 0 < scale) (floorPos : 0 < floor)
    (irregular : α → Prop)
    (dominated : ∀ history, irregular history →
      reach history ≤ slack * scale / floor ^ depth * reach (counterpart history)) :
    (∀ history, irregular history →
      reach history ≤ scale ^ 3 * (reach history / scale ^ 3)) ∧
    ∀ history, irregular history →
      scale ^ 2 * floor ^ depth * (reach history / scale ^ 3) ≤
        slack * reach (counterpart history) := by
  have cubePos : 0 < scale ^ 3 := pow_pos scalePos 3
  have powerPos : 0 < floor ^ depth := pow_pos floorPos depth
  refine ⟨fun history _ => by rw [mul_div_cancel₀ _ cubePos.ne'], fun history bad => ?_⟩
  have bound := dominated history bad
  have rewrite : scale ^ 2 * floor ^ depth * (reach history / scale ^ 3) =
      floor ^ depth / scale * reach history := by
    field_simp
  rw [rewrite]
  have factorNonneg : 0 ≤ floor ^ depth / scale := div_nonneg powerPos.le scalePos.le
  calc floor ^ depth / scale * reach history ≤
        floor ^ depth / scale * (slack * scale / floor ^ depth * reach (counterpart history)) :=
      mul_le_mul_of_nonneg_left bound factorNonneg
    _ = slack * reach (counterpart history) := by
      field_simp

end Vegas
