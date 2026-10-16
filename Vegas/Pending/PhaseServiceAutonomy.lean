/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryTranscript
import Interaction.ReactiveRecordedRounds

/-! # Activation clocks from the original seed and clock-erased own packets -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability
open LocalSeedController (CountedQueryLog positiveQueries exhaustedClocks encodeUnsentLogFrom)

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (counterLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => phaseApplication runtime leaks
local notation "counterApp" => runtime.reactiveApplication counterLeaks
local notation "encode" => encodeUnsentLogFrom (runtime := runtime) (leaks := counterLeaks)

private theorem deterministic_words_prefix (next : List Bool → Bool)
    (first second : List Bool)
    (left : ∀ before answer after, first = before ++ answer :: after → next before = answer)
    (right : ∀ before answer after, second = before ++ answer :: after → next before = answer) :
    first <+: second ∨ second <+: first := by
  have compare (fuel : Nat) : ∀ (before first second : List Bool), first.length ≤ fuel →
      (∀ past answer after, first = past ++ answer :: after → next (before ++ past) = answer) →
      (∀ past answer after, second = past ++ answer :: after → next (before ++ past) = answer) →
      first <+: second ∨ second <+: first := by
    induction fuel with
    | zero =>
        intro before first second bound _left _right
        have empty : first = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bound)
        subst first
        exact Or.inl List.nil_prefix
    | succ fuel ih =>
        intro before first second bound left right
        cases first with
        | nil => exact Or.inl List.nil_prefix
        | cons answer first =>
            cases second with
            | nil => exact Or.inr List.nil_prefix
            | cons other second =>
                have same : answer = other :=
                  (left [] answer first rfl).symm.trans (right [] other second rfl)
                subst other
                have rest := ih (before ++ [answer]) first second (by simpa using bound)
                  (fun past chosen after eq => by
                    simpa only [List.append_assoc, List.singleton_append] using
                      left (answer :: past) chosen after (by rw [eq]; rfl))
                  (fun past chosen after eq => by
                    simpa only [List.append_assoc, List.singleton_append] using
                      right (answer :: past) chosen after (by rw [eq]; rfl))
                rcases rest with rest | rest
                · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, rest⟩)
                · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, rest⟩)
  simpa only [List.nil_append] using compare first.length [] first second le_rfl left right

omit [Fintype Player] in
private def packetPattern (attempt : CommitAttemptId)
    (word : List (Nat × List (Message Player (CommitAttemptPacket graph)))) :
    List (List (MessageId Player × Bool)) :=
  word.map fun item => item.2.map fun message =>
    (message.id, message.payload.tokenValid attempt)

omit [Fintype Player] [DecidableEq Player] in
private def clockedPackets (clocks : List Nat) (packets : List (List (MessageId Player × Bool))) :
    List (PhaseSeedEmission graph) :=
  (clocks.zip packets).flatMap fun item =>
    item.2.map fun packet => ⟨item.1, packet.1, packet.2⟩

omit [Fintype Player] [DecidableEq Player] in
private theorem restore_word_emissions (attempt : CommitAttemptId)
    (word : List (Nat × List (Message Player (CommitAttemptPacket graph)))) (count : Nat) :
    ((word.take count).flatMap fun item => item.2.map (Prod.mk item.1)).map
        (PhaseSeedInput.operationalEmission attempt) =
      clockedPackets ((word.map Prod.fst).take count)
        ((packetPattern attempt word).take count) := by
  induction count generalizing word with
  | zero => rfl
  | succ count ih =>
      cases word with
      | nil => rfl
      | cons item word =>
          simpa only [List.take_succ_cons, List.map_cons, List.flatMap_cons, List.map_append,
            List.map_map, packetPattern, clockedPackets, List.zip_cons_cons, Function.comp_def,
            PhaseSeedInput.operationalEmission] using
            congrArg (fun rest => (item.2.map fun message =>
              (⟨item.1, message.id, message.payload.tokenValid attempt⟩ :
                PhaseSeedEmission graph)) ++ rest) (ih word)

omit [Fintype Player] in
private def patternInput (packets : List (List (MessageId Player × Bool)))
    (before : List Bool) : PhaseSeedOperationalInput graph :=
  let prior := encode 0 0 before
  let clocks := (positiveQueries prior).map (fun query => query.input.elapsed)
  ⟨(exhaustedClocks prior).length, clocks, clockedPackets clocks (packets.take clocks.length)⟩

omit [Fintype Player] in
private theorem restored_encoded_word_entry (owner : Player) (attempt : CommitAttemptId)
    (raw : List (Nat × List (Message Player (CommitAttemptPacket graph))))
    (word before after : List Bool) (answer : Bool) (split : word = before ++ answer :: after)
    (clocks : raw.map Prod.fst =
      (positiveQueries (encode 0 0 word)).map (fun query => query.input.elapsed)) :
    (patternInput runtime counterLeaks (packetPattern attempt raw) before,
      if answer then (.activate owner : (app).Command) else .wait) ∈
      (encode 0 0 word).map
        (restoreWordCounterEntry runtime leaks counterLeaks owner attempt raw) := by
  let prior := encode 0 0 before
  let elapsed := (exhaustedClocks prior).length
  let index := (positiveQueries prior).length
  let entry : LocalSeedEntry graph (counterApp).Command :=
    ⟨⟨⟨elapsed, []⟩, index⟩, if answer then .activation else .exhausted⟩
  have form : encode 0 0 word = prior ++ entry ::
      (if answer then encode elapsed (index + 1) after else encode (elapsed + 1) index after) := by
    rw [split, LocalSeedController.encodeUnsentLogFrom_append]
    cases answer <;> simp only [Nat.zero_add, encodeUnsentLogFrom, prior, entry, elapsed, index,
      Bool.false_eq_true, ite_false, ite_true]
  have prefixClocks : (raw.map Prod.fst).take index =
      (positiveQueries prior).map (fun query => query.input.elapsed) := by
    rw [clocks, form]
    simp only [positiveQueries, List.filterMap_append, List.map_append]
    simpa only [index, positiveQueries, List.length_map] using
      (List.take_left (l₁ := (positiveQueries prior).map (fun query => query.input.elapsed))
        (l₂ := (positiveQueries (entry ::
          (if answer then encode elapsed (index + 1) after
            else encode (elapsed + 1) index after))).map (fun query => query.input.elapsed)))
  apply List.mem_map.mpr
  refine ⟨entry, ?_, ?_⟩
  · rw [form]
    exact List.mem_append_right _ List.mem_cons_self
  · apply Prod.ext
    · change PhaseSeedInput.operational attempt
          { elapsed := elapsed
            activationClocks := (raw.take index).map Prod.fst
            emissions := (raw.take index).flatMap fun item => item.2.map (Prod.mk item.1) } = _
      change (⟨elapsed, (raw.take index).map Prod.fst,
          ((raw.take index).flatMap fun item => item.2.map (Prod.mk item.1)).map
            (PhaseSeedInput.operationalEmission attempt)⟩ : PhaseSeedOperationalInput graph) = _
      rw [List.map_take, restore_word_emissions, prefixClocks]
      simp only [patternInput, prior, elapsed, index, List.length_map]
    · cases answer <;> rfl

private theorem consistent_packet_words_prefix
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision) (coordinate : PhaseSeedAddress graph) (owner : Player) (seed : LocalSeed)
    (firstRaw secondRaw : List (Nat × List (Message Player (CommitAttemptPacket graph))))
    (first second : List Bool)
    (firstClocks : firstRaw.map Prod.fst =
      (positiveQueries (encode 0 0 first)).map (fun query => query.input.elapsed))
    (secondClocks : secondRaw.map Prod.fst =
      (positiveQueries (encode 0 0 second)).map (fun query => query.input.elapsed))
    (packets : packetPattern coordinate.1.attempt firstRaw =
      packetPattern coordinate.1.attempt secondRaw)
    (left : ∀ item ∈ (encode 0 0 first).map
      (restoreWordCounterEntry runtime leaks counterLeaks owner coordinate.1.attempt firstRaw),
      reply runtime leaks decideLocal coordinate seed item.1 = item.2)
    (right : ∀ item ∈ (encode 0 0 second).map
      (restoreWordCounterEntry runtime leaks counterLeaks owner coordinate.1.attempt secondRaw),
      reply runtime leaks decideLocal coordinate seed item.1 = item.2) :
    first <+: second ∨ second <+: first := by
  classical
  let next := fun before : List Bool => decide (reply runtime leaks decideLocal coordinate seed
    (patternInput runtime counterLeaks (packetPattern coordinate.1.attempt firstRaw) before) =
      .activate owner)
  apply deterministic_words_prefix next first second
  · intro before answer after split
    have chosen := left _ (restored_encoded_word_entry runtime leaks counterLeaks owner
      coordinate.1.attempt firstRaw first before after answer split firstClocks)
    cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at chosen <;>
      simp only [next, chosen, reduceCtorEq, decide_false, decide_true]
  · intro before answer after split
    have chosen := right _ (restored_encoded_word_entry runtime leaks counterLeaks owner
      coordinate.1.attempt secondRaw second before after answer split secondClocks)
    rw [← packets] at chosen
    cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at chosen <;>
      simp only [next, chosen, reduceCtorEq, decide_false, decide_true]

omit [Fintype Player] in
private theorem encoded_positive_prefix (first second : List Bool) (extended : first <+: second) :
    (positiveQueries (encode 0 0 first)).map (fun query => query.input.elapsed) <+:
      (positiveQueries (encode 0 0 second)).map (fun query => query.input.elapsed) := by
  obtain ⟨after, rfl⟩ := extended
  rw [LocalSeedController.encodeUnsentLogFrom_append]
  simp only [positiveQueries, List.filterMap_append, List.map_append]
  exact ⟨_, rfl⟩


/-- Equal original local seeds and clock-erased own packet patterns determine
all actual activation clocks, including after a send. Foreign histories and
private packet contents may differ; no clock equality is assumed. -/
theorem clocks_eq_of_seed_packet_pattern
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision) (timed : DeadlineExpiry runtime decideLocal)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon firstRemaining secondRemaining : Nat) (owner : Player)
    (first second : (app).Execution)
    (firstTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family firstSeeds)).Trace
        (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family secondSeeds)).Trace
        (some ⟨secondRemaining, some owner, second⟩))
    (coordinate : PhaseSeedAddress graph)
    (firstRequest : first.application.SeedRequest owner coordinate.1)
    (secondRequest : second.application.SeedRequest owner coordinate.1)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (samePackets :
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((first.respond app owner ⟨none⟩).recall owner)).map (fun item =>
          item.2.map fun message => (message.id, message.payload.tokenValid coordinate.1.attempt)) =
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((second.respond app owner ⟨none⟩).recall owner)).map (fun item =>
          item.2.map fun message =>
            (message.id, message.payload.tokenValid coordinate.1.attempt))) :
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (first.recall owner) (first.observe app owner)).activationClocks ++
      [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (first.recall owner) (first.observe app owner)).elapsed] =
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (second.recall owner) (second.observe app owner)).activationClocks ++
      [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (second.recall owner) (second.observe app owner)).elapsed] := by
  classical
  let counterLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
    fun _ _ => PMF.pure ∅
  let driver := controller runtime leaks priority decideLocal
  let firstRaw := PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
    ((first.respond app owner ⟨none⟩).recall owner)
  let secondRaw := PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
    ((second.respond app owner ⟨none⟩).recall owner)
  obtain ⟨firstCounted, firstClocks, _firstWaits, firstRestored⟩ :=
    active_query_transcript_signature runtime leaks counterLeaks priority decideLocal timed
      firstSeeds bounds plan ordered maximal inputs horizon firstRemaining owner first firstTrace
        coordinate firstRequest
  obtain ⟨secondCounted, secondClocks, _secondWaits, secondRestored⟩ :=
    active_query_transcript_signature runtime leaks counterLeaks priority decideLocal timed
      secondSeeds bounds plan ordered maximal inputs horizon secondRemaining owner second
        secondTrace coordinate secondRequest
  have emptyLog (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
      ∀ entry ∈ items.map (counterEntry runtime leaks counterLeaks owner),
        entry.query.input.emitted = [] := by
    intro entry member
    obtain ⟨item, _member, rfl⟩ := List.mem_map.mp member
    rfl
  have unresolvedLog (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
      ∀ entry ∈ items.map (counterEntry runtime leaks counterLeaks owner),
        entry.reply = .activation ∨ entry.reply = .exhausted := by
    intro entry member
    obtain ⟨item, _member, rfl⟩ := List.mem_map.mp member
    dsimp only [counterEntry]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨firstWord, firstEncoded⟩ := firstCounted.encode_unsent (emptyLog _) (unresolvedLog _)
  obtain ⟨secondWord, secondEncoded⟩ := secondCounted.encode_unsent (emptyLog _) (unresolvedLog _)
  have compatible (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed)) (remaining : Nat)
      (execution : (app).Execution)
      (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon (driver.family seeds)).Trace
          (some ⟨remaining, some owner, execution⟩)) :
      ∀ item ∈ driver.coordinateTranscriptFrom seeds.1 coordinate [] execution.environmentRecall,
        driver.reply coordinate (seeds.2 coordinate) item.1 = item.2 := by
    have genuine := ((app).deterministic_transcript_invariant driver.choose seeds).history
      (inputs.map (PhaseRuntimeState.initial plan)) horizon (fun _ _ => True.intro)
        ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon _ trace)
    exact ((driver.command_rectangle_transcript seeds.1 seeds.2 []
      execution.environmentRecall).mp genuine).2 coordinate
  have firstClockWord := active_owner_word_clocks runtime leaks bounds plan inputs horizon
    (driver.family firstSeeds) firstRemaining owner first firstTrace coordinate firstRequest
  have secondClockWord := active_owner_word_clocks runtime leaks bounds plan inputs horizon
    (driver.family secondSeeds) secondRemaining owner second secondTrace coordinate secondRequest
  rw [firstEncoded] at firstClocks firstRestored
  rw [secondEncoded] at secondClocks secondRestored
  have firstRawClocks : firstRaw.map Prod.fst =
      (positiveQueries (encodeUnsentLogFrom (runtime := runtime) (leaks := counterLeaks)
        0 0 firstWord)).map (fun query => query.input.elapsed) :=
    firstClockWord.trans firstClocks.symm
  have secondRawClocks : secondRaw.map Prod.fst =
      (positiveQueries (encodeUnsentLogFrom (runtime := runtime) (leaks := counterLeaks)
        0 0 secondWord)).map (fun query => query.input.elapsed) :=
    secondClockWord.trans secondClocks.symm
  have comparable := consistent_packet_words_prefix runtime leaks counterLeaks decideLocal
    coordinate owner (firstSeeds.2 coordinate) firstRaw secondRaw firstWord secondWord
    firstRawClocks secondRawClocks samePackets
    (by rw [firstRestored]; exact compatible firstSeeds firstRemaining first firstTrace)
    (by rw [secondRestored, sameSeed];
        exact compatible secondSeeds secondRemaining second secondTrace)
  have clockPrefix := comparable.elim
    (fun extended => Or.inl (encoded_positive_prefix runtime counterLeaks _ _ extended))
    (fun extended => Or.inr (encoded_positive_prefix runtime counterLeaks _ _ extended))
  rw [← firstRawClocks, ← secondRawClocks] at clockPrefix
  have equalLength : (firstRaw.map Prod.fst).length = (secondRaw.map Prod.fst).length := by
    simpa only [List.length_map] using congrArg List.length samePackets
  have sameClocks : firstRaw.map Prod.fst = secondRaw.map Prod.fst :=
    clockPrefix.elim (fun extended => extended.eq_of_length equalLength)
      (fun extended => (extended.eq_of_length equalLength.symm).symm)
  exact firstClockWord.symm.trans (sameClocks.trans secondClockWord)

end Vegas.EventGraphRuntime.PhaseServiceScheduler
