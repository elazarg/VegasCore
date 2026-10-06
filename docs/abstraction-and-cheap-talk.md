# Abstraction, leaks and cheap talk on the calendar ledger

Status: design study, not part of the arbitrary-builder target and not a
checklist item. Lower priority than end-to-end Nash and sequential-equilibrium
preservation.

**Realism caveat (project owner).** A chain without covert channels is an
unenforceable abstraction. In a cryptographic implementation every committed
value, like everything else, is encodable, so cheap talk is always available
below this model. A theorem that assumes it away is not preserved down to the
implementation level. Its value is in locating where equilibrium failures can
enter, not in ruling them out.

Status tags used below:
- **[checked]**: a Lean result at HEAD.
- **[read]**: verified by reading the Lean definitions.
- **[known]**: a published result, with its citation.
- **[claim]**: argued here by hand; not checked in Lean.
- **[conj]**: a conjecture.

## 0. Answer in one paragraph

Yes. "No leaks" is an abstraction theorem, not a secure-compilation theorem.

- The pinned `source_audited_raw_nash_iff` is a robust-preservation statement. A *compiled* profile is an equilibrium against every target deviator exactly when the source profile is one. It holds for **every** leak rule, because the compiled opponents babble: their calendar timing is drawn independently of everything (`calendarTiming`), so whatever a deviator learns through leaks is payoff-irrelevant noise.
- The abstraction statement is a different claim. **Every** ledger equilibrium, including ones that no compiler produced, is a source equilibrium up to its joint law. So a player who uses the chain naively, as if it were the source game, misses no equilibrium and is open to no coordination the source does not already allow.

On the calendar with a silent leak rule, this holds by the argument in §1. The one new hypothesis is a strict deposit margin, and one adapter lemma is still open. With leaks on, it fails. The extra capacity is a private, noisy, authenticated, unverifiable *timing* channel inside each event's roster block (§2).

Unused commit-reveal pairs ("yield") do **not** reproduce that channel. Yield is public, noiseless and common knowledge; the leak channel is private, noisy, and its delivery is not observed. Neither contains the other. A pre-play preparation phase is strictly weaker still. The cheapest way to make the compiler fully abstract is to remove the channel from the runtime calendar: owner-suffix rosters, §3. Enlarging the source language is the expensive route.

## 1. The abstraction theorem

### 1.1 What the runtime actually exposes [read]

**Player observation.**
- `ReactiveApplication.Execution.observe` gives a player three things: `network.observe who`, `observePlayer`, and the global `receipts` list.
- `network.observe who` is `⟨leaked who, ledger⟩`.
- `observePlayer` is `State.playerView`: the public view (graph public observation, accepted handles, clock, `PublicView.activatedAt`), the player's own private graph observation, and the player's own candidate catalogue.
- Interaction recall adds the player's own past views, actions and emitted envelopes.

**Leaks.**
- `ObservationRule := Principal → List Message → PMF (Finset MessageId)`. It is sampled at each activation.
- `MessageNetwork.learn` adds only *fresh, foreign, pending* envelopes.
- `learn_empty` gives `learn who ∅ = network`.

**Submission is invisible to others.**
- `MessageNetwork.submit_observe`: no player's network view changes.
- `reactiveApplication_submit_publicView`: the public view does not change.
- The message id `(sender, nextSerial sender)` is assigned at submission, but `MessageNetwork.nextSerial` and `inputs` are in the *environment* view only, not in any `PlayerView`.
- To confirm: `Submission.register` leaves `config` and other players' candidate catalogues untouched. Its docstring and `register_facts` suggest so.

**The calendar has no builder choices.**
- `rosterBlock` is roster activations, then one `includeLatest event owner` (or `sample`), then ticks, then `expire`.
- `rosterBlock_no_wire`: the `network` policy is **never consulted**.
- `reactiveLatest` includes the owner's latest unpublished pending packet addressed to that event. Foreign packets and malformed packets are never included.

**The native game is sequentialized.** One event is ready at a time, so a packet for event e+1 can carry a readiness token only after e completes. The block of e ends with no player activations after `includeLatest`. A *permitted* packet is therefore pending only inside its own block's roster.

**The audit.**
- `sourceServiceAudit` samples from the full transmitted traffic (`stateTraffic`) and the settled record. It does not use the leak rule.
- `SettledRecord.Permits` forbids the following:
  - every malformed packet;
  - every packet for a settled event that was not accepted with settled content;
  - a commitment whose handle is not `(sender, prepared (bindingCountBefore …))`.
- Complete play (`rosterScheduler_completesPlay`) settles every event. So every surplus packet is eventually forbidden.

### 1.2 Channel inventory under the calendar

| Channel | Leaks on | Leaks off |
| --- | --- | --- |
| Submission timing within a roster block | **Private, uncharged.** Seen by a later roster member that samples the pending packet. | Invisible: submission changes no player view. |
| Content of a pending *permitted* packet | A commitment carries nothing (canonical handle, no evidence). An opening shows a value that becomes public at block end, and no decision intervenes. Only its *presence* (timing) matters. | Invisible. |
| Pending *forbidden* packets (malformed, fresh commitments to non-canonical handles with later openings, tokenless early openings of an existing commitment, surplus copies) | Private to later activations, sometimes forever (never included). **Charged** with probability ≥ ρ. | Invisible. Still charged, because the audit reads all traffic, not leaks. |
| Owner's latest packet, if forbidden (e.g. an opening with an arbitrary raw value) | **Public broadcast on the ledger, charged.** | Same. Leaks are irrelevant. |
| Message-id serials on the ledger and receipts (a "nonce" channel: the serial counts *all* of the sender's submissions) | Public, charged: surplus packets are forbidden. | Same. |
| Builder randomness (a public correlation device) | None: the calendar never calls `network`. | None. |
| Private aliases (opening material, representation) | Private to the author; normalized away (`canonicalRaw_historyLaw`, `baseUtility_normalization`, `serviceAuditObservation_normalization`). | Same. |
| Off-chain talk | Outside the model; a stated limitation. | Same. |

**Conclusion [read/claim].** With leaks off on the calendar, every non-source channel is *charged*. Uncharged non-source behavior changes no other player's view.

Two remarks:
- **The charge needs audit coverage of unincluded traffic.** With a ledger-only audit, the nonce channel becomes free: send k invisible surplus packets, and the included id shows k. Under leaks off, a real watcher cannot see pending traffic. So either keep the idealized all-traffic backend, or make ledger ids not reveal the submission count. Ethereum account nonces count *included* transactions, so the model's `MessageNetwork.nextSerial` is stronger than Ethereum here.
- **A sunk charge is capped.** After a player is charged, further forbidden packets cost nothing, including the public broadcast. This matters only off path, so it is harmless for Nash but not for sequential equilibrium (§1.5).

### 1.3 Statements

Write `Silent leaks := ∀ who pending, leaks who pending = PMF.pure ∅`.

The current `rosterAuditDeposit = (upper − lower)/probability` gives ρ·D = R exactly. That is *weak* deterrence: a player who is exactly indifferent may still send charged signals in equilibrium. The abstraction needs a strict margin η > 0: `D_who = (R_who + η)/ρ_who`. This is a new deposit or a new hypothesis.

**Nash abstraction (exact).**
- Hypotheses: those of the SE pin, plus `Silent service.leaks` and the strict margin.
- Conclusion: for every raw profile `π̂` that is a Nash equilibrium of the audited raw game, there is a source profile `σ` such that
  - `σ` is Nash in the source protocol model, and
  - the joint law of `(parameter, public outcome, audited payoff vector)` under `π̂` equals the source law of `(parameter, public outcome, utility vector)` under `σ`. In particular, the charge is 0 almost surely.

Together with the existing iff, this gives **equality of the Nash outcome-law sets**: ledger = source. That is the game-theoretic analogue of full abstraction, and Maskin's *full* implementation, as opposed to the existing weak implementation.

**Approximate Nash abstraction.**
- For ε-Nash `π̂`, each player's forbidden-packet probability is at most ε/η.
- So the decompiled σ is (ε + 2Rδ)-Nash and the laws are within total variation δ = n·ε/η.
- Reuse the TV-to-expectation step planned for N4.

**Outcome-law abstraction.** Under `Silent leaks`, every raw profile that sends no forbidden packet with positive probability has the readout law of some source profile. The decompiled profile `dec π` is built player by player, and `dec (update π i τ̂) = update (dec π) i (dec τ̂)`.

outcome-law abstraction is false without either hypothesis:
- **With a forbidden packet on path:** the charged ledger broadcast can correlate play.
- **With leaks on:** see §2.3.

**Best-response abstraction (corollary of outcome-law abstraction).** Against any forbidden-free leak-silent opponents `π_{-i}`, the best audited ledger payoff of `i` equals its best source payoff against `dec π_{-i}`, and a compiled source policy attains it.

This is the precise form of "a naive player does not need to think about the runtime". The forbidden-free proviso is needed: an opponent who broadcasts by a charged rejected packet reveals information that a runtime-aware best response could use. That opponent pays for it, so it does not affect Nash abstraction.

### 1.4 Proof sketch and reuse

**1. Silence invariance (small, about 150 lines).**
- Under `Silent`, `observePending` is `pure ∅`. By `learn_empty`, `submit_observe` and `reactiveApplication_submit_publicView`, plus the `register` frame fact, another player's submission at a roster visit leaves every other player's view unchanged until `includeLatest`.
- Hence a player's view on a forbidden-free path is a function of the source-level public and private history and its *own* past responses.

**2. Timing irrelevance against arbitrary opponents (core; 1–2.5k lines; medium risk).**

Statement: for any permitted-menu profile `π` and player `i`, the readout law of `π` equals that of `update π i (timedPolicy (dec_i π_i))`.

- `dec_i π_i` is the Kuhn behavioral form of "draw own timing noise, then play `π_i`". It is well defined and per-player because, under silence, `i`'s own timing history is independent of everything except `i`'s source view.
- This generalizes `sourceServiceDeviation_initialized_prefix_factorization` / `sourceServiceDeviation_readout_law` in `Vegas/Game/SourceServiceDeviationReadout.lean`. The deviator's traffic "depends on the source state only through the deviator's source observation". That lemma currently needs the *other* players to be `sourceServiceTimedPolicy`, because under arbitrary leaks only babbling opponents are safe. Silence removes that need.
- Also reuse `rosterPolicy_phase_law` (`Vegas/Game/RevealServiceRosterLaw.lean`) for the per-phase "source choice, then source-free timing" split, and `normalizeDisclosureProfile_runFrom`.
- Induct over the finite player set: law(π) = law(timed(dec π)). Then `sourceServiceTimedProfile_protocol_law` gives the source law of `dec π`. That proves outcome-law abstraction.

**3. Raw to menu at an equilibrium (0.5–1.5k lines; the main risk).**
- **(a) Aliases.** Normalize all players simultaneously. `canonicalRaw_historyLaw` and `SubmissionNormalization.aliasDeviation_historyLaw` are stated against canonical raw opponents, so check that the all-player version is available or is a short corollary.
- **(b) Forbidden mass is zero.** Replace `i`'s policy by its fixed repair. It loses at most R base payoff on the histories where `i` sends a forbidden packet (`rosterAuditDeposit_covers_gain` is history-pointwise), and avoids an expected charge of at least ρD > R there.
  - Reuse `sourceService_continuation_settlement_comparison`, `remaining_events_stopped_coupling` at rank 0, and `sourceService_repair_range_settlement_le`, as `exists_menu_deviation_ge` already does.
  - Gap: these assume the opponents *extend a source profile in the permitted menu* (`agrees : … ExtendsProfile source target`). The NE argument needs the repair against arbitrary raw opponents. Charges depend only on own packets (`includeLatest` filters by sender, the audit reads own envelopes), so this should go through, but the Frame/coupling hypotheses must be re-derived. **This is the riskiest step.**
- **(c) Uncharged off-menu effective responses** must be law-equivalent to menu responses, or be shown never to occur on a forbidden-free path. This needs a classification of `effective \ permitted` responses, which the existing inequality-only route never needed.

**4. Assembly (about 300 lines).**
- Let `σ = dec π`, where `π` is the menu form of `π̂`.
- For a source deviation `τ_i`, the native deviation `timedPolicy τ_i` against `π_{-i}` has, by step 2, the source law of `update σ i τ_i`.
- Native NE then gives source payoff of `τ_i` ≤ native payoff of `π̂` = source payoff of `σ`.
- Package with `UtilityTransfer.isεNash_of_deviation_bounds` or `GameForm.MixtureSimulationOn`. `menuSimulation` and `compileProfile_payoff_law` are templates.

**Total:** about 2–4.5k lines. Step 2 is the new mathematics (it is N3 with every player deviating). Step 3b is the main risk.

### 1.5 Literature placement

**PL.**
- The existing iff is *robust preservation*: compiled code keeps its property against arbitrary target contexts (Abate et al., "Journey Beyond Full Abstraction", CSF 2019).
- Nash abstraction is *full abstraction* (Abadi, "Protection in programming-language translations", ICALP 1998; survey: Patrignani, Ahmed, Clarke, ACM CSUR 51(6), 2019). Here the target contexts are other players, possibly coordinating, and the observable is the equilibrium outcome law.
- Timing and side channels are the textbook reason fully abstract compilation fails; leaks play exactly that role here.

**Game theory.**
- *Full implementation*: all equilibria are good (Maskin, RES 1999), against weak implementation.
- Under leaks off, timing strategies are payoff-equivalent duplicates for every opponent profile. Adding duplicate or superfluous moves is a Thompson / Elmes–Reny strategic-equivalence transformation (Thompson 1952; Elmes & Reny, JET 1994), and Nash outcome sets are invariant under them. Nash abstraction is "the ledger's reduced normal form, after deleting strictly deposit-dominated strategies, is the source's".

**Mechanism design and cryptography (closest in spirit).**
- Izmalkov, Lepinski, Micali, "Perfect implementation", GEB 71 (2011): strategy- and privacy-equivalence of a concrete protocol to the ideal mediated game.
- Lepinski, Micali, shelat, "Collusion-free protocols", STOC 2005: no steganographic covert channels.

Nash abstraction is a collusion-freeness statement for the calendar ledger with silent leaks.

**Scope of the Nash version.** The SE analogue of Nash abstraction is harder, and false as stated without more work. After a sunk capped charge, a player can broadcast for free through rejected ledger packets even with leaks off. Off-path beliefs of a native SE need not decompile to a consistent source assessment. [conj] The SE version of Nash abstraction holds with a non-capped or per-offense charge.

## 2. Cheap talk with leaks on

### 2.1 Extra uncharged capacity [read/claim]

For each owned event e with roster r(e), the owner chooses the visit at which to submit its single permitted packet (resolutions may also stay silent, but that outcome is public). Each later roster member j samples, independently at each of its activations, whether the packet is pending, with the leak kernel's probability.

| Property | Value |
| --- | --- |
| Alphabet | At most (number of owner visits), plus one for resolutions |
| Audience | Roster members positioned after the owner's first visit; **private** to each |
| Noise | Z-channel: "seen" implies submitted; "unseen" is ambiguous |
| Delivery | Not observed by the sender; receivers do not see each other's samples, so there is no common knowledge |
| Authentication | Authenticated: only the owner's packet can be the permitted pending packet |
| Verifiability | Unverifiable: timing is unbound to hidden values |
| When | Interleaved: at every block, i.e. mid-game, after private inputs and the owner's own hidden binding choice |

Content is useless. A binding packet carries no content. An opening's value is public at block end with no intervening decision.

### 2.2 Charged extras, deterred under a strict margin and free after a sunk charge

- **Verifiable early disclosure of an existing commitment.** A tokenless early opening, pending forever and leaked in earlier blocks, gives a later player the committed value *verifiably* before its own decision. It is forbidden at settlement.
- **Arbitrary authenticated messages.** Malformed packets, or fresh non-canonical commit-and-open pairs (a "yield" in raw form), leaked privately.
- **Public authenticated broadcast.** A rejected opening with an arbitrary value as the owner's latest packet goes on the ledger.
- **The nonce channel** (§1.2).

So the source would need "verifiable early disclosure" as a primitive only to match off-path or post-charge behavior. It is not needed for the Nash outcome set under a strict margin.

### 2.3 Example: leaks implement an outcome no public talk can [claim]

**The program.**
- Alice has a private input θ, uniform on {0,1}. It may be drawn at a mid-game private-input event.
- Event 2 is an Alice binding (any value) with roster `[Alice, Bob, Alice]`.
- Events 3 and 4 are Bob's and Carol's *bindings* of a guess of θ, revealed only at events 5 and 6.
- Carol is in no roster before her own event. When she is activated, Alice's event-2 packet has already been included, so it is not pending.
- Payoffs: Bob gets 1 if his guess is correct, Carol gets 1 if hers is correct, and Alice gets 1 if Bob is correct.
- The leak rule shows Bob each foreign pending packet with probability p ∈ (0,1].

**The ledger profile.**
- Alice submits at visit 1 if θ = 1, and at visit 3 if θ = 0.
- Bob guesses 1 iff he saw Alice's packet pending. If not seen, his posterior on θ = 1 is (1−p)/(2−p) < 1/2.
- Carol guesses arbitrarily, since her posterior is 1/2.

**It is a Nash equilibrium.**
- For θ = 1, early submission gives Alice p against 0 for late.
- For θ = 0, late gives 1 against 1−p.
- Bob is best-responding.
- Every raw deviation is forbidden and weakly deterred.

The result is P(Bob correct) = (1+p)/2 > 1/2 = P(Carol correct).

**No public-talk extension reaches this.** Take any extension of the source by public messages: yield pairs at any position, a preparation phase, or any public broadcast. In every Nash equilibrium of it, P(Carol correct) ≥ P(Bob correct).
- Bob's guess is a function of the public history h before his commitment plus randomness independent of θ given h. So P(Bob correct | h) ≤ max(μ_h, 1−μ_h).
- Carol's public history refines h, and she best-responds. By convexity, P(Carol correct) = E max(μ_{h'}, 1−μ_{h'}) ≥ E max(μ_h, 1−μ_h).
- This assumes the Vegas source has no player-to-player *private* channel: publications are public, and private inputs come from Nature. Confirm this before citing it.

Even an equilibrium-selecting compiler cannot reach this law from such a source.

### 2.4 Yield, preparation and communication equilibria

**Yield is not the leak channel.** It differs on audience (public vs private), noise (deterministic vs a fixed kernel), common knowledge, and commitment. Yield commits, then reveals, so two pairs give Aumann–Maschler–Stearns jointly controlled lotteries (Aumann & Maschler, *Repeated Games with Incomplete Information*, 1995, reprinting the 1968 ACDA report). That is a public fair coin.

The two are mutually incomparable:
- Under leaks off, Nash abstraction implies the ledger has no public coin. In Battle of the Sexes the ledger Nash payoffs are {(2,1), (1,2), (2/3,2/3)}, while source plus two yield pairs reaches (3/2,3/2).
- With leaks on, the timing channel is sequential: a later sender sees the earlier one, so it cannot jointly control a lottery. [conj] Leaks-on ledgers cannot reach (3/2,3/2) in general.
- Conversely, §2.3 shows leaks reach what yield cannot.
- Also, compiling yield adds calendar blocks, which adds more timing channels.

**Preparation is weaker still.**
- Information arises mid-game: private-input events, the owner's own hidden binding, and public events in between. Pre-play talk cannot condition on it. In §2.3, draw θ after the preparation phase: even a *private* pre-play channel to Bob is then useless.
- Known theory says stage-by-stage communication strictly exceeds pre-play:
  - Myerson, "Multistage games with communication", Econometrica 54(2), 1986;
  - Forges, "An approach to communication equilibria", Econometrica 54(6), 1986;
  - von Stengel & Forges, "Extensive-form correlated equilibrium", Math. OR 33(4), 2008 (normal-form CE ⊆ EFCE, sometimes strictly).

**Where the leaks-on ledger sits.**
- [claim/conj] By Myerson's revelation principle, NE(source) = NE-laws(ledger, leaks off) ⊆ NE-laws(ledger, leaks on) ⊆ communication-equilibrium laws of the source.
  - The first equality is Nash abstraction plus the iff.
  - The last inclusion holds once the leaks-on ledger is shown to be the source extended by the leak-timing device (an analogue of outcome-law abstraction with that device).
  - The middle inclusion is strict by §2.3.
- [known] Unmediated cheap talk can implement correlated or communication equilibria only with enough players and suitable channels:
  - Bárány, Math. OR 17(2), 1992: four or more players, private channels, complete information;
  - Forges, "Universal mechanisms", Econometrica 58(6), 1990;
  - Ben-Porath, JET 80, 1998 and JET 108, 2003;
  - Gerardi, JET 114, 2004: five or more players, sequential equilibrium.
- [known] Noise itself can help: Blume, Board & Kawamura, "Noisy talk", TE 2(4), 2007; Goltsman, Hörner, Pavlov & Squintani, JET 144(4), 2009. A noisy private channel is not a degenerate form of public talk.
- [conj] The leak device is far from universal: a fixed kernel, Z-noise, sequential senders, one alphabet per block. The leaks-on set is strictly between the two bounds for typical programs.

## 3. Recommendation

1. **Decide the deposit margin first** (about 50 lines). Add a strict-margin deposit `(R+η)/ρ`, or a hypothesis. Nash abstraction is false-as-stated at η = 0 only in knife-edge ties, but a theorem cannot exclude them.
2. **Prove outcome-law abstraction under `Silent`** (1–2.5k lines; the core). Generalize the single-deviator factorization to "timing irrelevance against arbitrary opponents", then induct over players. It is independently useful: it is exactly the decompilation map, and it gives the best-response form best-response abstraction.
3. **Prove Nash abstraction (exact NE)** (0.5–1.5k lines). Steps 3a–3c of §1.4. First check in a small model that the repair dominates against off-menu opponents (3b) and classify uncharged off-menu responses (3c). Pin it next to `source_audited_raw_nash_iff` as "Nash outcome sets coincide".
4. **Owner-suffix rosters: a configuration, not a source change** (about 300 lines on top of Nash abstraction).
   - Hypothesis: in every `rosters e`, no non-owner follows the owner's first occurrence.
   - On a forbidden-free path, no permitted packet is then ever pending at a non-owner activation. Forbidden packets do not occur on an NE path. So every leak rule is effectively silent on path, and Nash abstraction holds with **any** leak rule.
   - This makes the compiler fully abstract with leaks on, without touching the source. It costs only the reaction slots that let others observe the owner mid-block. Check whether the SE pin or the watcher story relies on non-owner visits after the owner; `CommittedResolutionService` interleaves Alice and Bob, so some examples would change.
5. **Do not add yield to obtain abstraction.** It neither matches the leak channel nor preserves Nash abstraction, since it adds public coins. The source change that makes the leaks-on compiler fully abstract *with the current rosters* is a private noisy "whisper" primitive: the owner picks one of its block visits, and each later roster member receives a leak-kernel sample. That is the runtime exposed in the source, in the spirit of `S_exp`. Keep it as a paper remark, not a formalization target.
6. **Do not try an SE version of Nash abstraction yet.** The capped charge makes post-offense talk free; the abstraction would need per-offense charges or a new argument. Record it as open.
7. **Paper text.**
   - The §2.3 example as a checked-by-hand proposition. A small exact script is enough; a Lean version would be 0.5–1k lines with little payoff.
   - A remark that the existing iff holds for every leak rule *because* compiled opponents babble.
   - A remark on the nonce channel and the all-traffic audit assumption (§1.2).

**Order:** 1, then 2, then 3, then 4. Items 5–7 are prose.
