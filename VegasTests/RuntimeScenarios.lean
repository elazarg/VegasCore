module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensService
public import Vegas.Examples.OddsEvensLedgerClient
public import Vegas.Pending.ReactiveOpeningConformance
public import Vegas.Game.NativeExitContinuation
public import Vegas.Pending.ReactiveCountVerdict
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

/-! # Native client decisions after runtime irregularities

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

namespace VegasTests.RuntimeScenarios

open Vegas Vegas.EventGraphRuntime Vegas.Examples.OddsEvens Interaction
  GameTheory.Math.Probability

abbrev timeouts := Vegas.Examples.OddsEvensService.timeouts
abbrev app := Vegas.Examples.OddsEvensService.app
abbrev event (n : Fin 4) : compiled.EventId := n
def initial : app.Execution :=
  ReactiveApplication.Execution.initial (app := app) (EventGraphRuntime.State.initial
    (setup.eventInputs (Env.empty _)))

def candidate (who : Player) : Handle compiled := (who, .prepared 0)
def raw (bit : Bool) : Raw simpleExpr := ⟨.bool, bit⟩
def commit (who : Player) (e : Fin 4) (bit : Bool) : app.Action :=
  ⟨some ⟨⟨.commitment (event e) (candidate who), some (raw bit)⟩, .none⟩⟩
def opening (who : Player) (e : Fin 4) (bit : Bool) : app.Action :=
  ⟨some ⟨⟨.opening (event e) (candidate who) (raw bit), none⟩,
    .owned ⟨candidate who, raw bit⟩⟩⟩

def firstCommit (bit : Bool) : app.Execution :=
  (initial.respond app even (commit even 0 bit)).includePending app (even, 0)

abbrev submitted (bit : Bool) :=
  (initial.respond app even (commit even 0 bit)).application

theorem firstReady (bit : Bool) : (submitted bit).config.cut.Ready (event 0) := by
  change (EventOrder.Cut.empty compiled.order).Ready (event 0)
  decide

private theorem firstUnused (bit : Bool) : (submitted bit).HandleUnused (candidate even) := by
  intro field
  cases field with
  | inl input => exact Fin.elim0 input
  | inr e => change none ≠ some (candidate even); simp

def bound (bit : Bool) : EventGraphRuntime.State compiled :=
  { ((submitted bit).complete (event 0) (firstReady bit) (some (.success bit)) (.success bit)) with
    accepted := Function.update (submitted bit).accepted (.inr (event 0)) (some (candidate even))
    candidates := (submitted bit).candidates.freeze (candidate even) }

private theorem firstAccepted (bit : Bool) :
    EventGraphRuntime.handle timeouts (submitted bit)
      ⟨(even, 0), .commitment (event 0) (candidate even)⟩ =
      some (bound bit) := by
  rw [EventGraphRuntime.handle_commitment_eq timeouts (submitted bit) (even, 0) (event 0)
    (candidate even) even .bool rfl rfl rfl (firstReady bit) (by change 0 < 6; decide) (by
      change even ∉ (∅ : Finset Player); simp)
    rfl rfl rfl (firstUnused bit)]
  rfl

private theorem boundDrain (bit : Bool) : (bound bit).drain = bound bit := by
  apply State.drain_eq_of_clear
  intro named eligible
  obtain ⟨owner, _acting, inactive⟩ := eligible.owned
  have empty : (bound bit).config.defaulted = ∅ := by rfl
  simp [empty] at inactive

private theorem firstNativeAccepted (bit : Bool) (evidence : Option (OpeningFact compiled)) :
    app.handle (initial.respond app even (commit even 0 bit)).application
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), evidence, some ⟨event 0⟩⟩⟩ =
        some (bound bit) := by
  rw [EventGraphRuntime.reactiveApplication_handle]
  simp only [WitnessedPacket.tokenValid_commitment, ↓reduceIte, firstAccepted, Option.map_some]
  exact congrArg some (boundDrain bit)

private theorem first_receipts (bit : Bool) : (firstCommit bit).receipts = [((even, 0), true)] := by
  cases bit <;>
    change [((even, 0), (app.handle _
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩).isSome)] = _
  all_goals rw [firstNativeAccepted]; rfl

private theorem first_application (bit : Bool) :
    (firstCommit bit).application = bound bit := by
  cases bit <;>
    change (app.handle _
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), none, some ⟨event 0⟩⟩⟩).getD _ = _
  all_goals rw [firstNativeAccepted]; rfl

def earlyOpening (bit : Bool) : app.Execution :=
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

def rejectedOpening (bit : Bool) : app.Execution :=
  (earlyOpening bit).includePending app (even, 1)

private theorem rejection (state : app.State) (call : Payload compiled)
    (fact : Option (OpeningFact compiled)) :
    app.handle state ⟨(even, 1), ⟨call, fact, none⟩⟩ = none := by
  rw [EventGraphRuntime.reactiveApplication_handle]
  simp only [WitnessedPacket.tokenValid_none, Bool.false_eq_true, ↓reduceIte]

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
    (rejectedOpening bit).application = bound bit := by
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

def secondSubmitted (e o : Bool) : EventGraphRuntime.State compiled :=
  app.submit (bound e) odd
    ⟨⟨.commitment (event 1) (candidate odd), some (raw o)⟩, .none⟩

example (e o : Bool) :
    ((rejectedOpening e).respond app odd (commit odd 1 o)).application =
      secondSubmitted e o := by
  simp only [ReactiveApplication.Execution.respond, rejected_application]
  rfl

theorem secondReady (e o : Bool) :
    (secondSubmitted e o).config.cut.Ready (event 1) := by
  cases e <;> cases o <;> decide

private theorem secondUnused (e o : Bool) :
    (secondSubmitted e o).HandleUnused (candidate odd) := by
  intro field
  cases field with
  | inl input => exact Fin.elim0 input
  | inr named =>
      cases e <;> cases o <;> fin_cases named <;> decide

def bothBound (e o : Bool) : EventGraphRuntime.State compiled :=
  { ((secondSubmitted e o).complete (event 1) (secondReady e o) (some (.success o)) (.success
    o)) with
    accepted := Function.update (secondSubmitted e o).accepted (.inr (event 1))
      (some (candidate odd))
    candidates := (secondSubmitted e o).candidates.freeze (candidate odd) }

example (e o : Bool) : EventGraphRuntime.handle timeouts (secondSubmitted e o)
    ⟨(odd, 0), .commitment (event 1) (candidate odd)⟩ = some (bothBound e o) := by
  rw [EventGraphRuntime.handle_commitment_eq timeouts (secondSubmitted e o) (odd, 0) (event 1)
    (candidate odd) odd .bool rfl rfl rfl (secondReady e o) (by change 0 < 6; decide)
    (by cases e <;> cases o <;> decide)
    rfl rfl rfl (secondUnused e o)]
  rfl

theorem evenOpeningReady (e o : Bool) :
    (bothBound e o).config.cut.Ready (event 2) := by
  cases e <;> cases o <;> decide

def evenOpened (e o : Bool) : EventGraphRuntime.State compiled :=
  (bothBound e o).complete (event 2) (evenOpeningReady e o) true (.success e)

example (e o : Bool) : EventGraphRuntime.handle timeouts (bothBound e o)
    ⟨(even, 2), .opening (event 2) (candidate even) (raw e)⟩ = some (evenOpened e o) := by
  unfold raw
  rw [EventGraphRuntime.handle_opening_eq timeouts (bothBound e o) (even, 2) (event 2)
    (candidate even) even .bool _ _ rfl rfl rfl (evenOpeningReady e o)
    (by change 0 < 6; decide) (by cases e <;> cases o <;> decide)
    rfl rfl rfl e rfl rfl (.success e) rfl]
  rfl

theorem oddOpeningReady (e o : Bool) :
    (evenOpened e o).config.cut.Ready (event 3) := by
  cases e <;> cases o <;> decide

def finished (e o : Bool) : EventGraphRuntime.State compiled :=
  (evenOpened e o).complete (event 3) (oddOpeningReady e o) true (.success o)

example (e o : Bool) : EventGraphRuntime.handle timeouts (evenOpened e o)
    ⟨(odd, 1), .opening (event 3) (candidate odd) (raw o)⟩ = some (finished e o) := by
  unfold raw
  rw [EventGraphRuntime.handle_opening_eq timeouts (evenOpened e o) (odd, 1) (event 3)
    (candidate odd) odd .bool _ _ rfl rfl rfl (oddOpeningReady e o)
    (by change 0 < 6; decide) (by cases e <;> cases o <;> decide)
    rfl rfl rfl o rfl rfl (.success o) rfl]
  rfl

example (e o : Bool) : (finished e o).config.cut.Terminal := by
  cases e <;> cases o <;> decide

example (e o : Bool) :
    decodeState? (terminalRefs program) (finished e o).config.store =
      some (Env.cons (.success o) (Env.cons (.success e)
        (Env.cons (.success o) (Env.cons (.success e) (Env.empty _))))) := by
  rfl

example (e : Bool) : cash (.success e) (.success (!e)) odd = 126 := by
  cases e <;> decide

example (e o : Bool) :
    cash (.success e) (.success o) odd ≤ cash (.success e) (.success (!e)) odd := by
  cases e <;> cases o <;> decide

example (e : Bool) :
    expect (uniformLaw Bool)
      (fun o => (cash (.success e) (.success o) odd : ℝ)) = 100 := by
  rw [expect_eq_sum]
  cases e <;> norm_num [Fintype.sum_bool, uniformLaw_apply, cash, even, odd]

example (other : PublicationResult Bool) (own : Bool) :
    74 ≤ cash (.success own) other even ∧ cash .failure other even = 0 := by
  cases other with
  | failure => cases own <;> decide
  | success bit => cases bit <;> cases own <;> decide

def oddConditionalValue (probability : ℝ) (choice : Bool) : ℝ :=
  (1 - probability) * (cash (.success false) (.success choice) odd : ℝ) +
    probability * (cash (.success true) (.success choice) odd : ℝ)

private theorem oddConditionalValue_eq (probability : ℝ) :
    oddConditionalValue probability false = 74 + 52 * probability ∧
      oddConditionalValue probability true = 126 - 52 * probability := by
  norm_num [oddConditionalValue, cash, even, odd]
  constructor <;> ring

example (probability : ℝ) :
    (oddConditionalValue probability false ≤
        (oddConditionalValue probability false + oddConditionalValue probability true) / 2 ∧
      oddConditionalValue probability true ≤
        (oddConditionalValue probability false + oddConditionalValue probability true) / 2) ↔
      probability = 1 / 2 := by
  rw [(oddConditionalValue_eq probability).1, (oddConditionalValue_eq probability).2]
  constructor
  · intro optimal
    linarith [optimal.1, optimal.2]
  · intro unbiased
    rw [unbiased]
    norm_num

example (other : PublicationResult Bool) (own : Bool) :
    74 ≤ cash other (.success own) odd ∧ cash other .failure odd = 0 := by
  cases other with
  | failure => cases own <;> decide
  | success bit => cases bit <;> cases own <;> decide

def beforeTimeout (e : Bool) (clock : Nat) : EventGraphRuntime.State compiled :=
  { bound e with clock }

private theorem beforeTimeoutDrain (e : Bool) (clock : Nat) :
    (beforeTimeout e clock).drain = beforeTimeout e clock := by
  apply State.drain_eq_of_clear
  intro named eligible
  obtain ⟨owner, _acting, inactive⟩ := eligible.owned
  have empty : (beforeTimeout e clock).config.defaulted = ∅ := by rfl
  simp [empty] at inactive

example (e : Bool) (clock : Nat) :
    app.environment (beforeTimeout e clock) .advanceClock =
      PMF.pure (beforeTimeout e (clock + 1)) := by
  change (environmentStep timeouts (beforeTimeout e clock) .advanceClock).map State.drain = _
  simp only [environmentStep, PMF.pure_map]
  exact congrArg PMF.pure (beforeTimeoutDrain e (clock + 1))

theorem timeoutReady (e : Bool) :
    (beforeTimeout e 6).config.cut.Ready (event 1) := by
  cases e <;> decide

example (e : Bool) (clock : Nat) (before : clock < 6) :
    app.environment (beforeTimeout e clock) (.expire (event 1)) =
      PMF.pure (beforeTimeout e clock) := by
  change (environmentStep timeouts (beforeTimeout e clock) (.expire (event 1))).map State.drain = _
  rw [environmentStep_expire_of_not_due timeouts
    (beforeTimeout e clock) (event 1) (timeoutReady e) 0 rfl
    (by change ¬ 6 ≤ clock - 0; omega), PMF.pure_map]
  exact congrArg PMF.pure (beforeTimeoutDrain e clock)

def timedOut (e : Bool) : EventGraphRuntime.State compiled :=
  (beforeTimeout e 6).complete (event 1) (timeoutReady e) none .failure

example (e : Bool) : app.environment (beforeTimeout e 6) (.expire (event 1)) =
    PMF.pure (timedOut e) := by
  change (environmentStep timeouts (beforeTimeout e 6) (.expire (event 1))).map State.drain = _
  rw [environmentStep_expire_bind_eq timeouts _ (event 1)
    (timeoutReady e) 0 rfl (by change 6 ≤ 6; decide) odd .bool rfl rfl rfl, PMF.pure_map]
  apply congrArg PMF.pure
  change (timedOut e).drain = timedOut e
  apply State.drain_eq_of_clear
  intro named
  fin_cases named <;> cases e <;> decide

theorem survivorReady (e : Bool) : (timedOut e).config.cut.Ready (event 2) := by
  cases e <;> decide

def survivorOpened (e : Bool) : EventGraphRuntime.State compiled :=
  (timedOut e).complete (event 2) (survivorReady e) true (.success e)

theorem automaticReady (e : Bool) : (survivorOpened e).AutomaticReady (event 3) := by
  cases e <;> decide

def survivorFinished (e : Bool) : EventGraphRuntime.State compiled :=
  (survivorOpened e).completeAutomatic (event 3) (automaticReady e)

private theorem survivorDrain (e : Bool) : (survivorOpened e).drain = survivorFinished e := by
  have eligible : ∃ named, (survivorOpened e).AutomaticReady named := ⟨event 3, automaticReady e⟩
  have unique (witness : ∃ named, (survivorOpened e).AutomaticReady named) :
      Classical.choose witness = event 3 :=
    setup.eventGraph.sequentialize_ready_unique _ (Classical.choose_spec witness).1
      (automaticReady e).1
  change State.drainFuel 1 (survivorOpened e) = _
  simp only [State.drainFuel, eligible, ↓reduceDIte, unique]
  rfl

example (e : Bool) : app.handle (timedOut e)
    ⟨(even, 1), ⟨.opening (event 2) (candidate even) (raw e),
      some ⟨candidate even, raw e⟩, some ⟨event 2⟩⟩⟩ = some (survivorFinished e) := by
  rw [EventGraphRuntime.reactiveApplication_handle]
  simp only [WitnessedPacket.tokenValid_opening, ↓reduceIte]
  unfold raw
  rw [EventGraphRuntime.handle_opening_eq timeouts (timedOut e) (even, 1) (event 2)
    (candidate even) even .bool _ _ rfl rfl rfl (survivorReady e)
    (by change 0 < 6; decide) (by cases e <;> decide)
    rfl rfl rfl e rfl rfl (.success e) rfl, Option.map_some]
  exact congrArg some (survivorDrain e)

example (e : Bool) : (survivorFinished e).config.cut.Terminal := by
  cases e <;> decide

example (e : Bool) :
    (survivorFinished e).config.outputs (event 2) = some (.success e) ∧
      (survivorFinished e).config.outputs (event 3) = some .failure ∧
        cash (.success e) .failure even = 200 ∧ cash (.success e) .failure odd = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> cases e <;> decide

example (e : Bool) (remaining : Nat) (actor : Option Player) :
    exclusionBase setup timeouts (fun _ => ()) sourceUtility (fun _ => 0)
      Vegas.Examples.OddsEvensService.leaks
      (some ⟨remaining, actor, {initial with application := timedOut e}⟩) odd = 0 := by
  apply exclusionBase_of_defaulted
  change odd ∈ (timedOut e).config.defaulted
  cases e <;> decide

def oddCommitPacket : Message Player (WitnessedPacket compiled) :=
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

def oddOpeningPacket (o : Bool) : Message Player (WitnessedPacket compiled) :=
  ⟨(odd, 1), ⟨.opening (event 3) (candidate odd) (raw o),
    some ⟨candidate odd, raw o⟩, some ⟨event 3⟩⟩⟩

def traffic (e o : Bool) : List (Message Player (WitnessedPacket compiled)) :=
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

abbrev client := Vegas.Examples.OddsEvensLedgerClient.policy

def disclosedCommit (bit : Bool) : app.Action :=
  ⟨some ⟨⟨.commitment (event 0) (candidate even), some (raw bit)⟩,
    .owned ⟨candidate even, raw bit⟩⟩⟩

def disclosedIncluded (bit : Bool) : app.Execution :=
  (initial.respond app even (disclosedCommit bit)).includePending app (even, 0)

private theorem disclosed_application (bit : Bool) :
    (disclosedIncluded bit).application = bound bit := by
  cases bit <;>
    change (app.handle (initial.respond app even (commit even 0 _)).application
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), some ⟨candidate even, raw _⟩,
        some ⟨event 0⟩⟩⟩).getD _ = _
  all_goals rw [firstNativeAccepted]; rfl

example (bit : Bool) : (disclosedIncluded bit).receipts = [((even, 0), true)] := by
  cases bit <;>
    change [((even, 0), (app.handle (initial.respond app even (commit even 0 _)).application
      ⟨(even, 0), ⟨.commitment (event 0) (candidate even), some ⟨candidate even, raw _⟩,
        some ⟨event 0⟩⟩⟩).isSome)] = _
  all_goals rw [firstNativeAccepted]; rfl

private theorem disclosed_known (bit : Bool) :
    Vegas.Examples.OddsEvensLedgerClient.acceptedBit?
      ((disclosedIncluded bit).observe app odd) = some bit := by
  cases bit <;>
    simp only [Vegas.Examples.OddsEvensLedgerClient.acceptedBit?,
      ReactiveApplication.Execution.observe, disclosed_application]
  all_goals decide

example (bit : Bool) : Vegas.Examples.OddsEvensLedgerClient.acceptedBit?
    ((earlyOpening bit).observe app odd) = none := by
  cases bit <;>
    simp only [Vegas.Examples.OddsEvensLedgerClient.acceptedBit?, earlyOpening,
      ReactiveApplication.Execution.respond, ReactiveApplication.Execution.observe,
      first_application]
  all_goals decide

example (bit : Bool) : Vegas.Examples.OddsEvensLedgerClient.acceptedBit?
    ((rejectedOpening bit).observe app odd) = some bit := by
  cases bit <;>
    simp only [Vegas.Examples.OddsEvensLedgerClient.acceptedBit?,
      ReactiveApplication.Execution.observe, rejectedOpening, earlyOpening,
      ReactiveApplication.Execution.includePending, ReactiveApplication.Execution.respond,
      first_application]
  all_goals decide

example (bit : Bool) : Vegas.Examples.OddsEvensLedgerClient.oddBitLaw
    ((disclosedIncluded bit).observe app odd) = PMF.pure (!bit) :=
  Vegas.Examples.OddsEvensLedgerClient.oddBitLaw_of_known _ bit (disclosed_known bit)

example (bit : Bool) : Vegas.Examples.OddsEvensLedgerClient.acceptedBit?
    ((firstCommit bit).observe app odd) = none := by
  cases bit <;>
    simp only [Vegas.Examples.OddsEvensLedgerClient.acceptedBit?,
      ReactiveApplication.Execution.observe, first_application]
  all_goals decide

example (bit : Bool) : client odd [] ((disclosedIncluded bit).observe app odd) =
    PMF.pure (Vegas.Examples.OddsEvensLedgerClient.ordinaryResponse odd []
      (((disclosedIncluded bit).observe app odd).ledgerOnly app)
      (event 1) (some (PublicationResult.success (!bit)))) := by
  apply Vegas.Examples.OddsEvensLedgerClient.policy_at_informed_commitment
  · change odd ∉ (disclosedIncluded bit).application.config.defaulted
    rw [disclosed_application]
    cases bit <;> decide
  · change (disclosedIncluded bit).application.publicView.ownTurn? odd = some (event 1)
    rw [disclosed_application]
    cases bit <;> decide
  · rfl
  · exact disclosed_known bit

example (bit choice : Bool) : Vegas.Examples.OddsEvensLedgerClient.ordinaryResponse odd []
    (((disclosedIncluded bit).observe app odd).ledgerOnly app)
    (event 1) (some (PublicationResult.success choice)) = commit odd 1 choice := by
  let nativeView := (((disclosedIncluded bit).observe app odd).ledgerOnly app)
  have selected : canonicalFreshSlot odd nativeView.application = some 0 := by
    change canonicalFreshSlot odd
      ((disclosedIncluded bit).application.playerView odd) = some 0
    rw [disclosed_application]
    exact canonicalFreshSlot_canonical odd _ rfl
  have active : odd ∉ nativeView.application.publicView.observation.defaulted := by
    change odd ∉ (disclosedIncluded bit).application.config.defaulted
    rw [disclosed_application]
    cases bit <;> decide
  have correct := (canonicalServiceDecision_binding timeouts)
    Vegas.Examples.OddsEvensService.leaks odd [] nativeView (event 1) .bool
    rfl rfl rfl active 0 selected (PublicationResult.success choice)
  exact correct

example (bit : Bool) : ¬ CountPermits []
    ⟨(even, 0), ⟨.commitment (event 0) (candidate even), some ⟨candidate even, raw bit⟩,
      some ⟨event 0⟩⟩⟩ := by
  intro permitted
  have missing := permitted.2.1.2.1
  cases missing

end VegasTests.RuntimeScenarios
