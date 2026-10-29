/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensRecoveryService
import Vegas.Examples.OddsEvensFairValue
import Vegas.Pending.ReactiveOpeningConformance
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Pending.ReactiveCountVerdict

/-! # Concrete client decisions after runtime irregularities

The actual Odds–Evens application rejects a premature certified opening while
retaining its evidence in the recipient's ledger view. Subsequent native
commitment and opening handlers admit either response bit. Opposite-bit play
earns 126 against successful disclosure, compared with the fair response's
expected 100, and both of the recipient's packets satisfy the count verdict.

Relative expiry is inert before six ticks and excludes the missing owner at
six. The survivor can still open and collect 200; automatic service fails the
excluded owner's later opening. The excluded owner's base utility is fixed.
These are checked operations and payoff comparisons. A scheduler realizing
every prefix under an all-history service contract and a complete sequentially
rational client require separate results.
-/

noncomputable section

namespace VegasTests.RecoveryScenarios

open Vegas Vegas.EventGraphRuntime Vegas.Examples.OddsEvens Interaction
  GameTheory.Math.Probability

private abbrev runtime := Vegas.Examples.OddsEvensRecoveryService.runtime
private abbrev app := Vegas.Examples.OddsEvensRecoveryService.app
private abbrev event (n : Fin 4) : compiled.EventId := n
private def initial : app.Execution :=
  ReactiveApplication.Execution.initial (app := app) ⟨EventGraphRuntime.State.initial
    (setup.eventInputs (Env.empty _)), ∅⟩

private def candidate (who : Player) : Handle compiled := (who, .prepared 0)
private def raw (bit : Bool) : Raw simpleExpr := ⟨.bool, bit⟩
private def commit (who : Player) (e : Fin 4) (bit : Bool) : app.Action :=
  ⟨some ⟨⟨.commitment (event e) (candidate who), some (raw bit)⟩, .none⟩⟩
private def opening (who : Player) (e : Fin 4) (bit : Bool) : app.Action :=
  ⟨some ⟨⟨.opening (event e) (candidate who) (raw bit), none⟩,
    .owned ⟨candidate who, raw bit⟩⟩⟩

private def firstCommit (bit : Bool) : app.Execution :=
  (initial.respond app even (commit even 0 bit)).includePending app (even, 0)

private abbrev submitted (bit : Bool) :=
  (initial.respond app even (commit even 0 bit)).application.native

private theorem firstReady (bit : Bool) : (submitted bit).config.cut.Ready (event 0) := by
  change (EventOrder.Cut.empty compiled.order).Ready (event 0)
  decide

private theorem firstUnused (bit : Bool) : (submitted bit).HandleUnused (candidate even) := by
  intro field
  cases field with
  | inl input => exact Fin.elim0 input
  | inr e => change none ≠ some (candidate even); simp

private def bound (bit : Bool) : EventGraphRuntime.State compiled :=
  { ((submitted bit).complete (event 0) (firstReady bit) (.success bit) (.success bit)) with
    accepted := Function.update (submitted bit).accepted (.inr (event 0)) (some (candidate even))
    candidates := (submitted bit).candidates.freeze (candidate even) }

private theorem firstAccepted (bit : Bool) :
    EventGraphRuntime.handle runtime (submitted bit)
      ⟨(even, 0), .commitment (event 0) (candidate even)⟩ =
      some (bound bit) := by
  rw [EventGraphRuntime.handle_commitment_eq runtime (submitted bit) (even, 0) (event 0)
    (candidate even) even .bool rfl rfl rfl (firstReady bit) (by change 0 < 6; decide)
    rfl rfl rfl (firstUnused bit)]
  rfl

private theorem firstRecoveryAccepted (bit : Bool) :
    app.handle (initial.respond app even (commit even 0 bit)).application
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩ =
        some ⟨bound bit, ∅⟩ := by
  change RecoveryState.handle runtime (⟨submitted bit, ∅⟩ : RecoveryState compiled)
    ⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩ =
      some ⟨bound bit, ∅⟩
  simp only [RecoveryState.handle,
    RecoveryState.excludedCall_of_empty (⟨submitted bit, ∅⟩ : RecoveryState compiled) rfl,
    Bool.false_eq_true, ↓reduceIte,
    WitnessedPacket.tokenValid_commitment, firstAccepted, Option.map_some]
  exact congrArg some (RecoveryState.inclusionResult_drain_of_empty _ _ _ rfl)

private theorem first_receipts (bit : Bool) : (firstCommit bit).receipts = [((even, 0), true)] := by
  cases bit <;>
    change [((even, 0), (app.handle _
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩).isSome)] = _
  all_goals rw [firstRecoveryAccepted]; rfl

private theorem first_application (bit : Bool) :
    (firstCommit bit).application = ⟨bound bit, ∅⟩ := by
  cases bit <;>
    change (app.handle _
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩).getD _ = _
  all_goals rw [firstRecoveryAccepted]; rfl

private def earlyOpening (bit : Bool) : app.Execution :=
  (firstCommit bit).respond app even (opening even 2 bit)

example (bit : Bool) :
    ((earlyOpening bit).network.pending.head?).map (fun msg => msg.payload.token) = some none := by
  cases bit <;>
    simp only [earlyOpening, ReactiveApplication.Execution.respond, first_application]
  all_goals decide

example (bit : Bool) :
    ((earlyOpening bit).network.pending.head?).map (fun msg => msg.payload.evidence) =
      some (some ⟨candidate even, raw bit⟩) := by
  cases bit <;>
    simp only [earlyOpening, ReactiveApplication.Execution.respond, first_application]
  all_goals decide

private def rejectedOpening (bit : Bool) : app.Execution :=
  (earlyOpening bit).includePending app (even, 1)

private theorem rejection (state : app.State) (call : Payload compiled)
    (fact : Option (OpeningFact compiled)) :
    app.handle state ⟨(even, 1), ⟨call, fact, none⟩⟩ = none := by
  change RecoveryState.handle runtime state _ = none
  simp only [RecoveryState.handle, WitnessedPacket.tokenValid_none, Bool.false_eq_true,
    ↓reduceIte, ite_self]

example (bit : Bool) : (rejectedOpening bit).receipts =
    [((even, 0), true), ((even, 1), false)] := by
  cases bit <;>
    simp only [rejectedOpening, earlyOpening, ReactiveApplication.Execution.includePending,
      ReactiveApplication.Execution.respond, first_application]
  all_goals change (firstCommit _).receipts ++ [((even, 1), (app.handle _
    ⟨(even, 1), ⟨.opening (event 2) (candidate even) (raw _), some ⟨candidate even, raw _⟩,
      none⟩⟩).isSome)] = _
  all_goals rw [rejection, first_receipts]; rfl

private theorem rejected_application (bit : Bool) :
    (rejectedOpening bit).application = ⟨bound bit, ∅⟩ := by
  have pending : (earlyOpening bit).network.lookup (even, 1) =
      some ⟨(even, 1), ⟨.opening (event 2) (candidate even) (raw bit),
        some ⟨candidate even, raw bit⟩, none⟩⟩ := by
    cases bit <;>
      simp only [earlyOpening, ReactiveApplication.Execution.respond, first_application]
    all_goals rfl
  simp only [rejectedOpening, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, pending, rejection, Option.getD_none]
  simp only [earlyOpening, ReactiveApplication.Execution.respond, first_application]
  rfl

example (bit : Bool) :
    (((rejectedOpening bit).observe app odd).messages.ledger[1]?).map
      (fun msg => msg.payload.evidence) = some (some ⟨candidate even, raw bit⟩) := by
  cases bit <;>
    simp only [rejectedOpening, earlyOpening, ReactiveApplication.Execution.includePending,
      ReactiveApplication.Execution.respond, ReactiveApplication.Execution.observe,
      first_application]
  all_goals decide

private def secondSubmitted (e o : Bool) : EventGraphRuntime.State compiled :=
  (RecoveryState.submit (⟨bound e, ∅⟩ : RecoveryState compiled) odd
    ⟨⟨.commitment (event 1) (candidate odd), some (raw o)⟩, .none⟩).native

example (e o : Bool) :
    ((rejectedOpening e).respond app odd (commit odd 1 o)).application.native =
      secondSubmitted e o := by
  simp only [ReactiveApplication.Execution.respond, rejected_application]
  rfl

private theorem secondReady (e o : Bool) :
    (secondSubmitted e o).config.cut.Ready (event 1) := by
  cases e <;> cases o <;> decide

private theorem secondUnused (e o : Bool) :
    (secondSubmitted e o).HandleUnused (candidate odd) := by
  intro field
  cases field with
  | inl input => exact Fin.elim0 input
  | inr named =>
      cases e <;> cases o <;> fin_cases named <;> decide

private def bothBound (e o : Bool) : EventGraphRuntime.State compiled :=
  { ((secondSubmitted e o).complete (event 1) (secondReady e o) (.success o) (.success o)) with
    accepted := Function.update (secondSubmitted e o).accepted (.inr (event 1))
      (some (candidate odd))
    candidates := (secondSubmitted e o).candidates.freeze (candidate odd) }

example (e o : Bool) : EventGraphRuntime.handle runtime (secondSubmitted e o)
    ⟨(odd, 0), .commitment (event 1) (candidate odd)⟩ = some (bothBound e o) := by
  rw [EventGraphRuntime.handle_commitment_eq runtime (secondSubmitted e o) (odd, 0) (event 1)
    (candidate odd) odd .bool rfl rfl rfl (secondReady e o) (by change 0 < 6; decide)
    rfl rfl rfl (secondUnused e o)]
  rfl

private theorem evenOpeningReady (e o : Bool) :
    (bothBound e o).config.cut.Ready (event 2) := by
  cases e <;> cases o <;> decide

private def evenOpened (e o : Bool) : EventGraphRuntime.State compiled :=
  (bothBound e o).complete (event 2) (evenOpeningReady e o) true (.success e)

example (e o : Bool) : EventGraphRuntime.handle runtime (bothBound e o)
    ⟨(even, 2), .opening (event 2) (candidate even) (raw e)⟩ = some (evenOpened e o) := by
  unfold raw
  rw [EventGraphRuntime.handle_opening_eq runtime (bothBound e o) (even, 2) (event 2)
    (candidate even) even .bool _ _ rfl rfl rfl (evenOpeningReady e o)
    (by change 0 < 6; decide) rfl rfl rfl e rfl rfl (.success e) rfl]
  rfl

private theorem oddOpeningReady (e o : Bool) :
    (evenOpened e o).config.cut.Ready (event 3) := by
  cases e <;> cases o <;> decide

private def finished (e o : Bool) : EventGraphRuntime.State compiled :=
  (evenOpened e o).complete (event 3) (oddOpeningReady e o) true (.success o)

example (e o : Bool) : EventGraphRuntime.handle runtime (evenOpened e o)
    ⟨(odd, 1), .opening (event 3) (candidate odd) (raw o)⟩ = some (finished e o) := by
  unfold raw
  rw [EventGraphRuntime.handle_opening_eq runtime (evenOpened e o) (odd, 1) (event 3)
    (candidate odd) odd .bool _ _ rfl rfl rfl (oddOpeningReady e o)
    (by change 0 < 6; decide) rfl rfl rfl o rfl rfl (.success o) rfl]
  rfl

example (e o : Bool) : (finished e o).config.cut.Terminal := by
  cases e <;> cases o <;> decide

example (e o : Bool) :
    decodeState? (terminalRefs program) (finished e o).config.store = some (bitTerminal e o) := by
  rfl

example (e : Bool) : cash (.success e) (.success (!e)) odd = 126 := by
  cases e <;> decide

example (e o : Bool) :
    cash (.success e) (.success o) odd ≤ cash (.success e) (.success (!e)) odd := by
  cases e <;> cases o <;> decide

example (e : Bool) :
    expect (PMF.uniformOfFintype Bool)
      (fun o => (cash (.success e) (.success o) odd : ℝ)) = 100 :=
  uniform_opponent_value e odd

private def beforeTimeout (e : Bool) (clock : Nat) : RecoveryState compiled :=
  ⟨{ bound e with clock }, ∅⟩

example (e : Bool) (clock : Nat) :
    RecoveryState.environment runtime (beforeTimeout e clock) .advanceClock =
      PMF.pure (beforeTimeout e (clock + 1)) := by
  simp only [RecoveryState.environment, environmentStep, PMF.pure_map]
  exact congrArg PMF.pure (RecoveryState.environmentResult_drain_of_empty _ _ _ rfl)

private theorem timeoutReady (e : Bool) :
    (beforeTimeout e 6).native.config.cut.Ready (event 1) := by
  cases e <;> decide

example (e : Bool) (clock : Nat) (before : clock < 6) :
    RecoveryState.environment runtime (beforeTimeout e clock) (.expire (event 1)) =
      PMF.pure (beforeTimeout e clock) := by
  rw [RecoveryState.environment, environmentStep_expire_of_not_due runtime
    (beforeTimeout e clock).native (event 1)
    (timeoutReady e) 0 rfl (by change ¬ 6 ≤ clock - 0; omega), PMF.pure_map]
  exact congrArg PMF.pure (RecoveryState.environmentResult_drain_of_empty _ _ _ rfl)

private def timedOut (e : Bool) : RecoveryState compiled :=
  ⟨(beforeTimeout e 6).native.complete (event 1) (timeoutReady e) .failure .failure, {odd}⟩

example (e : Bool) : RecoveryState.environment runtime (beforeTimeout e 6) (.expire (event 1)) =
    PMF.pure (timedOut e) := by
  rw [RecoveryState.environment, environmentStep_expire_bind_eq runtime _ (event 1)
    (timeoutReady e) 0 rfl (by change 6 ≤ 6; decide) odd .bool rfl rfl rfl, PMF.pure_map]
  apply congrArg PMF.pure
  change (timedOut e).drain = timedOut e
  apply RecoveryState.drain_eq_of_clear
  intro named
  fin_cases named <;> cases e <;> decide

private theorem survivorReady (e : Bool) : (timedOut e).native.config.cut.Ready (event 2) := by
  cases e <;> decide

private def survivorOpened (e : Bool) : RecoveryState compiled :=
  ⟨(timedOut e).native.complete (event 2) (survivorReady e) true (.success e), {odd}⟩

private theorem automaticReady (e : Bool) : (survivorOpened e).AutomaticReady (event 3) := by
  cases e <;> decide

private def survivorFinished (e : Bool) : RecoveryState compiled :=
  (survivorOpened e).completeAutomatic (event 3) (automaticReady e)

private theorem survivorDrain (e : Bool) : (survivorOpened e).drain = survivorFinished e := by
  have eligible : ∃ named, (survivorOpened e).AutomaticReady named := ⟨event 3, automaticReady e⟩
  have unique (witness : ∃ named, (survivorOpened e).AutomaticReady named) :
      Classical.choose witness = event 3 :=
    setup.eventGraph.sequentialize_ready_unique _ (Classical.choose_spec witness).1
      (automaticReady e).1
  change RecoveryState.drainFuel 1 (survivorOpened e) = _
  simp only [RecoveryState.drainFuel, eligible, ↓reduceDIte, unique]
  rfl

example (e : Bool) : RecoveryState.handle runtime (timedOut e)
    ⟨(even, 1), ⟨.opening (event 2) (candidate even) (raw e),
      some ⟨candidate even, raw e⟩, some ⟨event 2⟩⟩⟩ = some (survivorFinished e) := by
  simp only [RecoveryState.handle]
  have clear : (timedOut e).excludedCall (.opening (event 2) (candidate even) (raw e)) = false := by
    cases e <;> decide
  rw [clear]
  simp only [Bool.false_eq_true, ↓reduceIte, WitnessedPacket.tokenValid_opening]
  unfold raw
  rw [EventGraphRuntime.handle_opening_eq runtime (timedOut e).native (even, 1) (event 2)
    (candidate even) even .bool _ _ rfl rfl rfl (survivorReady e)
    (by change 0 < 6; decide) rfl rfl rfl e rfl rfl (.success e) rfl, Option.map_some]
  exact congrArg some (survivorDrain e)

example (e : Bool) : (survivorFinished e).native.config.cut.Terminal := by
  cases e <;> decide

example (e : Bool) :
    (survivorFinished e).native.config.outputs (event 2) = some (.success e) ∧
      (survivorFinished e).native.config.outputs (event 3) = some .failure ∧
        cash (.success e) .failure even = 200 ∧ cash (.success e) .failure odd = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> cases e <;> decide

example (e : Bool) (remaining : Nat) (actor : Option Player) :
    recoveryExclusionBase (setup := setup) (runtime := runtime)
      (leaks := Vegas.Examples.OddsEvensRecoveryService.leaks)
      (fun _ => ()) sourceUtility (fun _ => 0)
      (some ⟨remaining, actor, {initial with application := timedOut e}⟩) odd = 0 :=
  recoveryExclusionBase_of_excluded _ _ _ _ _ (by change odd ∈ ({odd} : Finset Player); simp)

private def oddCommitPacket : Message Player (WitnessedPacket compiled) :=
  ⟨(odd, 0), ⟨.commitment (event 1) (candidate odd), none, some ⟨event 1⟩⟩⟩

example (traffic : List (Message Player (WitnessedPacket compiled))) :
    CountPermits traffic oddCommitPacket := by
  have noEarlier (other : Message Player (WitnessedPacket compiled)) :
      ¬ EarlierOwnPacket traffic oddCommitPacket other := by
    intro earlier
    exact Nat.not_lt_zero _ earlier.2.2
  refine ⟨rfl, ⟨rfl, rfl, rfl, ⟨0, rfl⟩, ?_⟩, ?_⟩
  · intro other earlier
    exact (noEarlier other earlier).elim
  · intro other earlier
    exact (noEarlier other earlier).elim

private def oddOpeningPacket (o : Bool) : Message Player (WitnessedPacket compiled) :=
  ⟨(odd, 1), ⟨.opening (event 3) (candidate odd) (raw o),
    some ⟨candidate odd, raw o⟩, some ⟨event 3⟩⟩⟩

private def traffic (e o : Bool) : List (Message Player (WitnessedPacket compiled)) :=
  [⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩,
    ⟨(even, 1), ⟨.opening (event 2) (candidate even) (raw e),
      some ⟨candidate even, raw e⟩, none⟩⟩,
    oddCommitPacket,
    ⟨(even, 2), ⟨.opening (event 2) (candidate even) (raw e),
      some ⟨candidate even, raw e⟩, some ⟨event 2⟩⟩⟩,
    oddOpeningPacket o]

example (e o : Bool) : CountPermits (traffic e o) (oddOpeningPacket o) := by
  have earlier (other : Message Player (WitnessedPacket compiled)) :
      EarlierOwnPacket (traffic e o) (oddOpeningPacket o) other ↔ other = oddCommitPacket := by
    constructor
    · intro ⟨member, own, serial⟩
      simp only [traffic, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp_all [oddOpeningPacket, oddCommitPacket, Message.sender, even, odd]
    · rintro rfl
      exact ⟨by simp [traffic], rfl, by change 0 < 1; decide⟩
  refine ⟨rfl, ?_, ?_⟩
  · change certifiedOpening (oddOpeningPacket o).payload = true ∧ odd = odd ∧
      (raw o).ty = .bool ∧
      ∃ other, EarlierOwnPacket (traffic e o) (oddOpeningPacket o) other ∧
        other.payload.call = .commitment (event 1) (candidate odd)
    refine ⟨?_, rfl, rfl, oddCommitPacket, (earlier _).mpr rfl, rfl⟩
    cases o <;> decide
  · intro other before
    rw [(earlier other).mp before]
    change some (event 1) ≠ some (event 3)
    decide

example (e o : Bool) : ¬ CountPermits (traffic e o)
    ⟨(even, 1), ⟨.opening (event 2) (candidate even) (raw e),
      some ⟨candidate even, raw e⟩, none⟩⟩ := by
  intro permitted
  exact Bool.false_ne_true permitted.1

end VegasTests.RecoveryScenarios
