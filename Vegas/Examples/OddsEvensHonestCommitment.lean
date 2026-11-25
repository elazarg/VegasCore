module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensLedgerClient
public import Vegas.Pending.ReactiveGraphSteps
public import Interaction.MessageNetworkInvariant

@[expose] public section

/-! # Ledger evidence before the second Odds–Evens commitment -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime EventGraph Interaction GameTheory.Math.Probability

private theorem no_opening_turn (execution : app.Execution) (who : Player)
    (unfinished : eventId 1 ∉ execution.application.config.cut.completed)
    (event : Fin 4) (publication : 2 ≤ event.val)
    (selected : (execution.observe app who).application.publicView.ownTurn? who =
      some (eventId event)) : False := by
  have ready := ((execution.observe app who).application.publicView.ownTurn?_spec who _ selected).1
  have prerequisite : eventId 1 ∈ compiled.order.predecessors (eventId event) := by
    have possibilities : event.val = 2 ∨ event.val = 3 := by omega
    rcases possibilities with rank | rank
    · have eventEq : event = 2 := Fin.ext rank
      subst event
      decide
    · have eventEq : event = 3 := Fin.ext rank
      subst event
      decide
  exact unfinished ((execution.application.config.history_exact _).mp (ready.2 _ prerequisite))

private theorem canonical_binding_evidence
    {Principal : Type} [DecidableEq Principal] {L : IExpr} [IExpr.ResultTypes L]
    {graph : EventGraph Principal L} (limits : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Principal (WitnessedPacket graph))
    (who owner : Principal) (past : List ((reactiveApplication limits) leaks).PlayerEntry)
    (view : ((reactiveApplication limits) leaks).PlayerView) (event : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (value : L.Val payload) (material : ((reactiveApplication limits) leaks).Submission)
    (emitted : (canonicalServiceDecision limits leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) (some (.success value)))).transmission =
      some material) : material.evidence = .none := by
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · rw [canonicalServiceDecision_defaulted limits leaks who past view event _ inactive] at emitted
    cases emitted
  · cases selected : canonicalFreshSlot who view.application with
    | none =>
      simp only [canonicalServiceDecision, canonicalReactiveDecision,
        ite_eq_right inactive, node, cast_cast, cast_eq, Option.bind_some, selected,
        Option.map_none, ReactiveApplication.SubmissionNormalization.action] at emitted
      cases emitted
    | some serial =>
      simp only [canonicalServiceDecision, canonicalReactiveDecision,
        ite_eq_right inactive, node, cast_cast, cast_eq, Option.bind_some, selected,
        Option.map_some, ReactiveApplication.SubmissionNormalization.action,
        reactiveNormalization] at emitted
      rw [← Option.some.inj emitted]
      rfl

private theorem binding_response_evidence (execution : app.Execution) (who : Player)
    (unfinished : eventId 1 ∉ execution.application.config.cut.completed)
    (action : app.Action)
    (supported : action ∈ (policy who (execution.logs who) (execution.observe app who)).support)
    (material : app.Submission) (emitted : action.transmission = some material) :
    material.evidence = .none := by
  let view := execution.observe app who
  let ledgerView := view.ledgerOnly app
  let ledgerPast := (execution.logs who).map (ReactiveApplication.PlayerEntry.ledgerOnly app)
  change action ∈ (respond who ledgerPast ledgerView).support at supported
  by_cases inactive : who ∈ ledgerView.application.publicView.observation.defaulted
  · simp only [respond, ite_eq_left inactive, PMF.mem_support_pure_iff] at supported
    cases supported
    cases emitted
  · cases turn : ledgerView.application.publicView.ownTurn? who with
    | none =>
      simp only [respond, ite_eq_right inactive, turn, PMF.mem_support_pure_iff] at supported
      cases supported
      cases emitted
    | some event =>
      cases recorded : eventRecorded timeouts OddsEvensService.leaks ledgerPast event with
      | true =>
        simp only [respond, ite_eq_right inactive, turn, recorded, ↓reduceIte,
          PMF.mem_support_pure_iff] at supported
        cases supported
        cases emitted
      | false =>
        simp only [respond, ite_eq_right inactive, turn, recorded, Bool.false_eq_true,
          ↓reduceIte] at supported
        change Fin 4 at event
        fin_cases event
        · obtain ⟨bit, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact canonical_binding_evidence OddsEvensService.timeouts OddsEvensService.leaks
            who even _ _ (eventId 0) BaseTy.bool rfl rfl rfl bit material emitted
        · obtain ⟨bit, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact canonical_binding_evidence OddsEvensService.timeouts OddsEvensService.leaks
            who odd _ _ (eventId 1) BaseTy.bool rfl rfl rfl bit material emitted
        · exact (no_opening_turn execution who unfinished 2 (by decide) turn).elim
        · exact (no_opening_turn execution who unfinished 3 (by decide) turn).elim

private def NoEarlyEvidence (execution : app.Execution) : Prop :=
  eventId 1 ∉ execution.application.config.cut.completed →
    execution.network.Satisfies (fun message => message.payload.evidence = none)

private theorem noEarlyEvidence_invariant : app.PolicyInvariant policy NoEarlyEvidence where
  respond execution who action prior supported := by
    intro unfinished
    rw [(reactive_respond_application OddsEvensService.timeouts OddsEvensService.leaks
      execution who action).1] at unfinished
    cases sent : action.transmission with
    | none =>
      simpa only [ReactiveApplication.Execution.respond, sent] using prior unfinished
    | some material =>
      have none := binding_response_evidence execution who unfinished action supported material sent
      simp only [ReactiveApplication.Execution.respond, sent]
      apply (prior unfinished).submit
      rcases material with ⟨call, evidence⟩
      cases none
      rfl
  environment execution next command prior moved := by
    intro unfinished
    have path := (reactiveApplication_graphSteps OddsEvensService.timeouts
      OddsEvensService.leaks).environmentStep execution next command moved
    have valid := prior (fun complete => unfinished
      (Config.Step.path_completed_mono path complete))
    apply app.environmentStep_cases execution next command moved
      (predicate := fun _ next => next.network.Satisfies (fun message =>
        message.payload.evidence = none))
    · exact valid
    · intro who selected _
      exact valid.learn who selected
    · intro id
      have safe := valid.includePending id
      unfold ReactiveApplication.Execution.includePending
      rcases included : execution.network.includePending id with ⟨envelope, network⟩
      cases envelope <;> simpa only [included] using safe
    · exact fun _ _ _ => valid

/-- Before the second commitment has completed, honest ledger-reading play
carries no opening certificate, under any scheduler. -/
theorem acceptedBit_eq_none_before_second_commitment (scheduler : app.Scheduler)
    (rounds : Nat) (execution : app.Execution)
    (reached : execution ∈
      (app.roundsFrom OddsEvensService.initial scheduler policy rounds).support)
    (unfinished : eventId 1 ∉ execution.application.config.cut.completed)
    (who : Player) : acceptedBit? (execution.observe app who) = none := by
  obtain ⟨initial, _, run⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have safe := noEarlyEvidence_invariant.runRounds scheduler rounds
    (ReactiveApplication.Execution.initial app initial) execution
    (fun _ => MessageNetwork.Satisfies.empty) run unfinished
  unfold acceptedBit?
  change (execution.application.accepted (.inr (eventId 0))).bind (fun accepted =>
    execution.network.ledger.findSome? fun message =>
      message.payload.evidence.bind fun fact =>
        if fact.handle = accepted then fact.raw.as? .bool else none) = none
  generalize execution.application.accepted (.inr (eventId 0)) = associated
  cases associated with
  | none => rfl
  | some handle =>
    rw [Option.bind_some]
    apply List.findSome?_eq_none_iff.mpr
    intro message member
    rw [safe.ledger message member]
    rfl

/-- At an unrecorded second commitment in honest play, Odd uses the fair
commitment law. The physical ledger supplies no bit to condition on. -/
theorem policy_at_honest_second_commitment (scheduler : app.Scheduler)
    (rounds : Nat) (execution : app.Execution)
    (reached : execution ∈
      (app.roundsFrom OddsEvensService.initial scheduler policy rounds).support)
    (active : odd ∉ (execution.observe app odd).application.publicView.observation.defaulted)
    (turn : (execution.observe app odd).application.publicView.ownTurn? odd = some (eventId 1))
    (unsent : eventRecorded timeouts OddsEvensService.leaks
      ((execution.logs odd).map (ReactiveApplication.PlayerEntry.ledgerOnly app))
      (eventId 1) = false) :
    policy odd (execution.logs odd) (execution.observe app odd) =
      (uniformLaw Bool).map (fun bit =>
        ordinaryResponse odd
          ((execution.logs odd).map (ReactiveApplication.PlayerEntry.ledgerOnly app))
          ((execution.observe app odd).ledgerOnly app) (eventId 1)
          (some (PublicationResult.success bit))) := by
  have ready :=
    ((execution.observe app odd).application.publicView.ownTurn?_spec odd _ turn).1
  have unfinished : eventId 1 ∉ execution.application.config.cut.completed := fun complete =>
    ready.1 ((execution.application.config.history_exact _).mpr complete)
  have unread := acceptedBit_eq_none_before_second_commitment scheduler rounds execution reached
    unfinished odd
  simp only [policy, ReactiveApplication.ledgerPolicy, respond,
    ReactiveApplication.PlayerView.ledgerOnly, active, ite_false, turn, unsent,
    Bool.false_eq_true]
  change (oddBitDistribution ((execution.observe app odd).ledgerOnly app)).map _ = _
  rw [oddBitDistribution_of_unknown _ ((acceptedBit?_ledgerOnly _).trans unread)]

end Vegas.Examples.OddsEvensLedgerClient
