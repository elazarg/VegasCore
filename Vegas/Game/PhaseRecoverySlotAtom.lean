/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingEncodingLaw
import Vegas.Game.PhaseBindingNonmissingReference

/-! # Source content and operational slot factors in actual binding atoms -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

/-- The complete fresh-slot atom separates the original AUX content mass from
its purely physical uniform slot factor, even for accepted failed bindings. -/
theorem phaseRecoverySlotPolicy_atom (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (serial : Nat)
    (eligible : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      past view) (result : PublicationResult (L.Val payload)) :
    phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding past view (phaseBindingResponse runtime leaks who event payload
          result serial) =
      ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload past view).card :
        ENNReal)⁻¹ *
        ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) (result, false) := by
  classical
  rw [phaseRecoverySlotPolicy, PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro choice
  let data := phaseRecoveryBindingData setup mode event who payload binding choice.1
  change _ * (if data.2 then PMF.pure _ else _) _ =
    _ * (@ite ENNReal ((result, false) = data) (Classical.propDecidable _) _ 0)
  cases flag : data.2 with
  | true =>
      have distinct : (result, false) ≠ data := by
        intro equal
        have := congrArg Prod.snd equal
        simp only [flag, Bool.false_eq_true] at this
      have nonsilent : phaseBindingResponse runtime leaks who event payload result serial ≠
          (⟨none⟩ : (phaseApplication runtime leaks).Action) := by
        intro equal
        have impossible := congrArg (fun response => response.transmission.isNone) equal
        cases impossible
      simp only [↓reduceIte, PMF.pure_apply, ite_eq_right nonsilent, ite_eq_right distinct,
        mul_zero]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [PhaseCount.phaseBindingSlotPolicy_atom runtime leaks bounds who event payload
        (fun _ _ => PMF.pure data.1) past view serial eligible result]
      have matched : (result, false) = data ↔ data.1 = result := by
        constructor
        · exact fun equal => (congrArg Prod.fst equal).symm
        · intro equal
          exact Prod.ext equal.symm flag.symm
      simp only [matched, PMF.pure_apply]
      by_cases same : data.1 = result
      · simp only [same, ite_true, mul_one]
        exact mul_comm _ _
      · have reverse : result ≠ data.1 := Ne.symm same
        simp only [same, reverse, ite_false, mul_zero]

/-- At an actual unsent binding callback, the exact physical response atom
has the original AUX typed-result mass times the eligible-slot factor. -/
theorem phaseSourceSlotPolicy_atom_of_history (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control))
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) (result : PublicationResult (L.Val payload)) :
    phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who) (control.execution.observe (phaseApplication runtime leaks)
          who) (phaseBindingResponse runtime leaks who event payload result serial) =
      ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who)).card : ENNReal)⁻¹ *
        ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event
            (control.execution.observe (phaseApplication runtime leaks) who)))).map
              (fun choice => phaseRecoveryBindingData setup mode event who payload binding
                choice.1)) (result, false) := by
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  rw [phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed assessment
    control.execution valid who event payload binding request]
  have eligible := PhaseCount.mem_phaseBindingSlots_of_history runtime leaks bounds menu plan
    inputs horizon scheduler control trace who event payload binding request unsent values serial
    bounded fresh
  exact phaseRecoverySlotPolicy_atom setup mode runtime leaks bounds wellFormed assessment who
    event payload binding _ _ serial eligible result

end Vegas
