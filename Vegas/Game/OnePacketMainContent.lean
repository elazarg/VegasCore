module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketFactorization
public import Vegas.Game.SourceServiceCanonicalAcceptance

@[expose] public section

/-! # Positive source content of honest responses

The honest component samples a source action and makes its canonical physical
response. A transmitting canonical response decodes to that same source action;
its source probability is positive on support. Menu normalization to silence
has content one. These pointwise facts require no service or history premise.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem canonical_sent_decodes
    (execution : (application setup timeouts leaks).Execution) (who : Player)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (action : (graph setup).Action event) (material : (application setup timeouts leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who) event action).transmission =
        some material) :
    sentSourceAction setup timeouts leaks
      (execution.respond (application setup timeouts leaks) who
        ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event action))
      ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
        (execution.observe (application setup timeouts leaks) who) event action) =
      decodeEventAction setup.program event action := by
  have afterEq : (execution.respond (application setup timeouts leaks) who
      ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
        (execution.observe (application setup timeouts leaks) who) event action)).application =
      (application setup timeouts leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [submits]
  obtain ⟨output, witness⟩ := canonical_response_witness execution who event turn action material
    submits
  unfold sentSourceAction
  rw [submits, Option.bind_some, afterEq]
  rcases witness with binding | opening
  · obtain ⟨candidate, owner, payload, layoutEq, call, _fixed, decision, _output⟩ := binding
    change material.call.packet = .commitment event candidate at call
    rw [call, decision]
    cases node : nodeView (graph setup) event with
    | bind actor other outputEq codeEq =>
        have kinds := outputEq.symm.trans layoutEq
        obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj kinds
        simp only [callContent, node]
    | sample other law outputEq codeEq =>
        have kinds := outputEq.symm.trans layoutEq
        cases kinds
    | resolve actor other binding checks outputEq codeEq =>
        have kinds := outputEq.symm.trans layoutEq
        cases kinds
  · obtain ⟨candidate, raw, owner, payload, binding, checks, outputEq, codeEq, result,
      call, node, _resolved, decision, _output⟩ := opening
    change material.call.packet = .opening event candidate raw at call
    simp only [call, callContent, node, decision]

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- A supported source-main response has positive source content.
Menu normalization to silence has content one. -/
theorem contentFactor_pos_of_honestChoice
    (source : setup.intendedModel.BehavioralAssessment)
    (who : Player) (execution : (application setup timeouts leaks).Execution)
    (response : (application setup timeouts leaks).Action)
    (choice : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (execution.logs who, execution.observe (application setup timeouts leaks) who)))
    (chosen : choice.1 = some response)
    (supported : choice ∈ (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler source who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who))).support) :
    0 < contentFactor setup timeouts leaks source who execution
      (execution.respond (application setup timeouts leaks) who response) response := by
  cases emits : response.transmission with
  | none => simp only [contentFactor, emits]; exact zero_lt_one
  | some material =>
      have nonsilent : response.transmission ≠ none := by rw [emits]; exact Option.some_ne_none _
      have responseSupport : response ∈ (honestResponse setup timeouts leaks source who
          (execution.logs who) (execution.observe (application setup timeouts leaks)
            who)).support := by
        obtain ⟨original, originalSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        have recorded := (congrArg Subtype.val same).trans chosen
        by_cases offered : original ∈ bounds.onePacketActions timeouts leaks who
            (execution.logs who) (execution.observe (application setup timeouts leaks) who)
        · simp only [responseChoice, dite_eq_left offered, Option.some.injEq] at recorded
          exact recorded ▸ originalSupport
        · have quiet : response = ⟨none⟩ := by
            simpa only [responseChoice, dite_eq_right offered, Option.some.injEq] using
              recorded.symm
          exact (nonsilent (by rw [quiet])).elim
      unfold honestResponse at responseSupport
      split at responseSupport
      · have quiet := (PMF.mem_support_pure_iff _ _).mp responseSupport
        exact (nonsilent (by rw [quiet])).elim
      · rename_i event turn
        obtain ⟨sampled, sampledSupport, realized⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp responseSupport
        cases encoded : sampled.bind (encodeEventAction? setup.program event) with
        | none =>
            have quiet : response = ⟨none⟩ := by simpa only [encoded] using realized.symm
            exact (nonsilent (by rw [quiet])).elim
        | some action =>
            have responseEq : (canonicalServiceDecision timeouts) leaks who (execution.logs who)
                (execution.observe (application setup timeouts leaks) who) event action =
                  response := by
              simpa only [encoded] using realized
            have submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
                (execution.observe (application setup timeouts leaks) who) event
                  action).transmission =
                  some material := by rw [responseEq, emits]
            have sent := canonical_sent_decodes execution who event turn action material submits
            rw [responseEq] at sent
            obtain ⟨original, originalEq, encodes⟩ := Option.bind_eq_some_iff.mp encoded
            have recovered : decodeEventAction setup.program event action = sampled :=
              (decodeEventAction_encodeEventAction?_eq_some setup.program event original action
                encodes).trans originalEq.symm
            rw [recovered] at sent
            have positive : 0 < ((asIfHonestProfile setup timeouts leaks source who
                (some (execution.logs who,
                  execution.observe (application setup timeouts leaks) who))) sampled).toReal :=
              ENNReal.toReal_pos (PMF.mem_support_iff _ _ |>.mp sampledSupport)
                (PMF.apply_ne_top _ _)
            rw [contentFactor, emits]
            change 0 < ((asIfHonestProfile setup timeouts leaks source who
              (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who)))
              (sentSourceAction setup timeouts leaks
                (execution.respond (application setup timeouts leaks) who response)
                  response)).toReal
            rw [sent]
            exact positive

end Vegas
