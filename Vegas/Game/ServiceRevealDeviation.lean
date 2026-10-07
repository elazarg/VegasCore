/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealCongruence
import Vegas.Game.ServiceOpeningHonestLaw

/-! # A block of disclosures against one deviator

Against the first-turn clients of a source profile that opens effectively, one
player follows an arbitrary native policy through a sealed block of
disclosures. Every other owner opens each of its disclosures; along the runs on
which the deviator does not withhold (`Vegas.DeviatorWithheld`) it opens its own
as well, so the block decodes to the open chain of the source configuration
(`Vegas.openChain`). The deviator's traffic, gated by withholding, factors
through its source view after the open chain
(`Vegas.asyncDeviation_revealBlock_factorization`): two starts whose open chains
look alike to the deviator publish alike (`Vegas.revealTail_store_agree`), so
the block's runs from them have equal gated readouts.

In the source, the deviator opens the block's disclosures as its residual
source policy does and follows a policy of the residual program afterwards
(`Vegas.revealGraft`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Source

/-- A policy whose decisions at the leading disclosures are those of `head`
and whose residual policy is `rest`. -/
def revealGraft (who : Player) : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : RevealPrefix program count) → BehavioralPolicy who program →
    BehavioralPolicy who (revealTail count program prefixed).tail → BehavioralPolicy who program
  | 0, _, _, _, _, _, rest => rest
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed, head, rest =>
      (head.1, revealGraft who count next prefixed head.2 rest)
  | _ + 1, _, _, .ret _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _, _ => prefixed.elim

/-- A graft opens through the leading disclosures as its head does. -/
theorem OpensThrough.revealGraft {who : Player} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (registry : Registry Γ) (revelations : Revelations Γ) (head : BehavioralPolicy who program)
      (rest : BehavioralPolicy who (revealTail count program prefixed).tail),
      OpensThrough count program prefixed registry revelations head →
      OpensThrough count program prefixed registry revelations
        (Vegas.revealGraft who count program prefixed head rest) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed registry revelations head rest _; trivial
  | succ count ih =>
      intro Γ names program prefixed registry revelations head rest opens
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact ⟨opens.1, ih next prefixed _ _ head.2 rest opens.2⟩

/-- The residual profile of a profile updated with a graft is the residual
profile updated with the graft's residual policy. -/
theorem revealTailProfile_update_revealGraft (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (profile : BehavioralProfile program) (head : BehavioralPolicy who program)
      (rest : BehavioralPolicy who (revealTail count program prefixed).tail),
      revealTailProfile count program prefixed
          (Function.update profile who (revealGraft who count program prefixed head rest)) =
        Function.update (revealTailProfile count program prefixed profile) who rest := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed profile head rest; rfl
  | succ count ih =>
      intro Γ names program prefixed profile head rest
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          change revealTailProfile count next prefixed
              (afterReveal (Function.update profile who
                (head.1, revealGraft who count next prefixed head.2 rest))) = _
          rw [afterReveal_update]
          exact ih next prefixed (afterReveal profile) head.2 rest

/-- **The source run of a grafted deviator through leading disclosures.** When
every player opens effectively at the leading disclosures, the deviator with
its own decisions there, the source run of the profile updated with a graft is
the residual source run, from the open chain, of the residual profile updated
with the graft's residual policy. -/
theorem iterate_revealGraft [Fintype Player] (who : Player) (count : Nat)
    {Γ : SourceCtx Player L} {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (prefixed : RevealPrefix program count)
    (rest : BehavioralPolicy who (revealTail count program prefixed).tail) (more : Nat)
    (config : Config Player L Γ)
    (opens : ∀ player, OpensThrough count program prefixed config.registry config.revelations
      (profile player)) :
    (fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who
          (revealGraft who count program prefixed (profile who) rest))))^[count + more]
        (PMF.pure (ProtocolState.entry program config)) =
      ((fun law => law.bind (ProtocolState.behavioralStateStep
        (revealTail count program prefixed).tail
        (Function.update (revealTailProfile count program prefixed profile) who rest)))^[more]
        (PMF.pure (ProtocolState.entry _ (openChain count program prefixed config)))).map
          (revealTail count program prefixed).lift := by
  rw [iterate_openChain count program _ prefixed more config, revealTailProfile_update_revealGraft]
  intro player
  by_cases same : player = who
  · subst same
    rw [Function.update_self]
    exact OpensThrough.revealGraft count program prefixed _ _ _ rest (opens player)
  · rw [Function.update_of_ne same]
    exact opens player

/-- The deviator's view after the open chain determines its view before. -/
theorem openChain_view_reflects (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (left right : Config Player L Γ),
      (openChain count program prefixed left).view who =
          (openChain count program prefixed right).view who →
        left.view who = right.view who := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed left right same; exact same
  | succ count ih =>
      intro Γ names program prefixed left right same
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          have later := ih next prefixed _ _ same
          calc left.view who
              = ((revealSuccessor published selected left
                  (effectiveDisclosure published selected left true)).view who).back
                  (decide (owner = who)) := (back_reveal_view who published selected left _).symm
            _ = ((revealSuccessor published selected right
                  (effectiveDisclosure published selected right true)).view who).back
                  (decide (owner = who)) := congrArg _ later
            _ = right.view who := back_reveal_view who published selected right _

/-- The residual view after leading disclosures, read off the program's view
of an embedded residual state. -/
def revealTailRecover (who : Player) : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : RevealPrefix program count) → Option (ProtocolView who program) →
      Option (ProtocolView who (revealTail count program prefixed).tail)
  | 0, _, _, _, _, view => view
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed, view =>
      revealTailRecover who count next prefixed (view.bind (Sum.elim (fun _ => none) some))
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The program's view of an embedded residual state determines the residual
view. -/
theorem revealTailRecover_spec (who : Player) : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : RevealPrefix program count)
    (state : Option (ProtocolState (revealTail count program prefixed).tail)),
    revealTailRecover who count program prefixed
        ((state.map (revealTail count program prefixed).lift).map
          (ProtocolState.observe who program)) =
      state.map (ProtocolState.observe who _) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed state; cases state <;> rfl
  | succ count ih =>
      intro Γ names program prefixed state
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ next =>
          have later := ih next prefixed state
          cases state with
          | none => exact later
          | some state => exact later

end Source

variable {setup : Setup (Player := Player) (L := L)}

/-- **Alike-looking open chains publish alike.** Two stores that agree with
residual states after leading disclosures, the states looking alike to one
player, agree on every publication of the program's context and on the
output of every leading disclosure. -/
theorem revealTail_store_agree (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program)
      (left right : State L (revealTail count program prefixed).context)
      (leftStore rightStore : EventGraph.Store (graphLayout setup.program)),
      (revealTailRefs setup count program prefixed refs embedding).Agrees left leftStore →
      (revealTailRefs setup count program prefixed refs embedding).Agrees right rightStore →
      sourceObserve who left = sourceObserve who right →
      (∀ {name : VarId} {payload : L.Ty} (source : HasVar Γ name (.publication payload)),
        leftStore (refs.get source).field = rightStore (refs.get source).field) ∧
      ∀ index : Fin (eventCount program), index.val < count →
        leftStore (.inr (embedding.event index)) = rightStore (.inr (embedding.event index)) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed refs embedding left right leftStore rightStore leftAgree
        rightAgree same
      refine ⟨fun source => ?_, fun index below => absurd below (Nat.not_lt_zero _)⟩
      have leftRead := leftAgree source
      have rightRead := rightAgree source
      have cell : left.get source = right.get source := by
        have observed := congrArg (fun observation => observation.cells _ _ source) same
        simpa only [sourceObserve] using observed
      unfold EventGraph.FieldRef.get? at leftRead rightRead
      change cast _ (leftStore (refs.get source).field) = _ at leftRead
      change cast _ (rightStore (refs.get source).field) = _ at rightRead
      rw [cell] at leftRead
      exact (cast_inj _).mp (leftRead.trans rightRead.symm)
  | succ count ih =>
      intro Γ names program prefixed refs embedding left right leftStore rightStore leftAgree
        rightAgree same
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          obtain ⟨publications, events⟩ := ih next prefixed
            (refs.cons (name := published) ⟨.inr (embedding.event ⟨0, by simp [eventCount]⟩),
              reveal_head_layout embedding⟩)
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) left right leftStore
            rightStore leftAgree rightAgree same
          refine ⟨fun source => publications (.there source), fun index below => ?_⟩
          by_cases head : index.val = 0
          · have indexIs : index = ⟨0, by simp [eventCount]⟩ := Fin.ext head
            subst indexIs
            exact publications .here
          · obtain ⟨later, laterEq⟩ : ∃ later, index.val = later + 1 :=
              ⟨index.val - 1, by omega⟩
            have laterBelow : later < eventCount next := by
              have := index.isLt
              simp only [eventCount] at this
              omega
            have indexIs : index = Fin.cast (by simp [eventCount])
                (Fin.succ (⟨later, laterBelow⟩ : Fin (eventCount next))) :=
              Fin.ext (by simp only [Fin.val_cast, Fin.val_succ]; omega)
            rw [indexIs]
            exact events ⟨later, laterBelow⟩ (by simp only; omega)

/-- A decoded block of disclosures gives the residual references' agreement
with the open configuration and its history. -/
theorem revealTail_agrees_of_decode (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) (store : EventGraph.Store (graphLayout setup.program))
    (history : History Player L)
    (config : Config Player L (revealTail count program prefixed).context)
    (decoded : decodeSourcePrefix? program refs registry revelations embedding.ref count store
      history = some ((revealTail count program prefixed).lift (ProtocolState.entry _ config))) :
    (revealTailRefs setup count program prefixed refs embedding).Agrees config.state store ∧
      history = config.history := by
  rw [decodeSourcePrefix?_revealTail_entry count program prefixed] at decoded
  cases state : decodeState? (revealTailRefs setup count program prefixed refs embedding) store
    with
  | none =>
      rw [state] at decoded
      cases decoded
  | some value =>
      rw [state, Option.map_some] at decoded
      have same := ((revealTail_lift_injective count program prefixed).comp
        (ProtocolState.entry_injective _)) (Option.some.inj decoded)
      rw [← same]
      exact ⟨decodeState?_agrees _ _ _ state, rfl⟩

section Block

variable {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

open Classical in
/-- **A block of disclosures against one deviator.** On a reveal-relaxed graph,
under the asynchronous contract with timely delays, against the first-turn
clients of a source profile that opens effectively at the leading disclosures,
one player follows an arbitrary native policy. From completion boundaries at
the start `low` of a sealed block of disclosures at which the deviator has not
withheld, every run until the block is done along which the deviator has not
withheld decodes to the open chain of the source configuration; and the
deviator's traffic, gated by withholding, jointly with the open chain, factors
through the deviator's view of the open chain. -/
theorem asyncDeviation_revealBlock_factorization
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : RevealBlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {Γ : SourceCtx Player L} {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (count : Nat) (prefixed : RevealPrefix program count)
    (positive : 0 < count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (highEq : low + count = high)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
      (source seed).revelations (source seed).registry embedding refsBefore low)
    (opens : ∀ seed player, OpensThrough count program prefixed (source seed).registry
      (source seed).revelations (profile player))
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs low
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
        deviation) low (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (alive : ∀ seed ∈ prior.support, ¬ DeviatorWithheld who (execution seed).application.config)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    (∀ seed ∈ prior.support, ∀ final ∈
      ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
          deviation) (BlockDone high) horizon (execution seed)).support,
      ¬ DeviatorWithheld who final.application.config →
      decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))) =
        some ((revealTail count program prefixed).lift
          (ProtocolState.entry _ (openChain count program prefixed (source seed))))) ∧
    ∃ kernel : DecisionView who (revealTail count program prefixed).context → PMF (Option _),
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
            deviation) (BlockDone high) horizon (execution seed)).map fun final =>
          if DeviatorWithheld who final.application.config then none
          else some (openChain count program prefixed (source seed),
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
      ((prior.map source).bind fun config =>
        PMF.pure (openChain count program prefixed config)).bind fun config =>
          (kernel (config.view who)).map (Option.map fun extra => (config, extra)) := by
  classical
  let app := serviceApplication setup mode deadline leaks
  let traffic := (serviceRuntime setup mode deadline).bindingTraffic leaks who
  let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile
    who deviation
  subst highEq
  have suffix := (aligned prior.support_nonempty.choose).graphSuffix
  have publications := prefixed.publications (mode := mode) suffix
  have sealed := RevealBlockEnd.sealed relaxed wall publications
  let assignment := openAssignment setup mode (· ≠ who) count program prefixed embedding
    (fun _ => none)
  -- Facts at the block's start.
  have startFacts (seed : Seed) (supported : seed ∈ prior.support) :
      Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) ∧
      (∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks (execution seed) owner ∧
        CanonicalSlotsUsed setup leaks (execution seed) owner) ∧
      ActivationsAnswered setup leaks (execution seed) := by
    refine ⟨app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler _ _
      (bounded seed supported) _ (boundary seed supported).supported, fun owner honest => ?_,
      roundsFrom_activationsAnswered _ _ (boundary seed supported).supported⟩
    exact canonicalSlots_roundsFrom scheduler _ owner (bound := bound)
      (firstTurnTiming setup turns mode) wholeProfile
      (by simp only [deviatedTurnProfile, Function.update_of_ne honest]) _ _
      (boundary seed supported).supported
  -- Every other owner opens: the run is the one with the openings assigned.
  have opened (seed : Seed) (supported : seed ∈ prior.support) :
      app.runUntil scheduler players (BlockDone (low + count))
          (horizon - (execution seed).environmentRecall.length) (execution seed) =
        app.runUntil scheduler (blockPlayers bound turns wholeProfile who deviation assignment)
          (BlockDone (low + count)) (horizon - (execution seed).environmentRecall.length)
          (execution seed) := by
    obtain ⟨⟨trace⟩, _, _⟩ := startFacts seed supported
    have start := boundary seed supported
    rw [show players = blockPlayers bound turns wholeProfile who deviation (fun _ => none) from
        deviatedTurnProfile_firstTurn_eq_blockPlayers bound turns wholeProfile who deviation,
      blockPlayers_eq_drawnPlayers, blockPlayers_eq_drawnPlayers]
    exact drawnPlayers_runUntil_open relaxed wall bound turns wholeProfile (· ≠ who)
      (fun _ => deviation) (execution seed) start.ordered start.untouched publications count
      program profile prefixed refs (source seed).registry (source seed).revelations embedding
      refsBefore low (aligned seed) (fun player _ => opens seed player) le_rfl rfl (fun _ => none)
      (fun _ _ none => by cases none) _ 0 (by simpa only [Nat.zero_add] using trace)
  -- Context references completed at the start keep agreeing.
  have agreeAlong (seed : Seed) (supported : seed ∈ prior.support)
      {after : (serviceGraph setup mode).Config}
      (reach : ConfigReaches setup (execution seed).application.config after) :
      refs.Agrees (source seed).state after.store :=
    reach.agrees refs (source seed).state (checkpoint seed).agrees
      (fun ref producer fieldEq => by
        have before := refsBefore ref ⟨0, Nat.lt_of_lt_of_le positive prefixed.le_eventCount⟩
        rw [fieldEq] at before
        change producer.val < (embedding.event _).val at before
        rw [(aligned seed).graphSuffix.rankEq] at before
        exact ((boundary seed supported).ordered.2 producer).mpr (by simpa using before))
  -- A configuration of the block with every disclosure opened decodes to the open chain.
  have decodeOpened (seed : Seed) (supported : seed ∈ prior.support)
      (after : (serviceGraph setup mode).Config)
      (reach : ConfigReaches setup (execution seed).application.config after)
      (afterPrefix : after.cut.IsPrefix (low + count))
      (allOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
        event.val < low + count → OpenedAt after event) :
      decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count after.store
          (decodeHistory setup.program (after.history.map
            (setup.eventGraph.fromModeCompletion mode))) =
        some ((revealTail count program prefixed).lift
          (ProtocolState.entry _ (openChain count program prefixed (source seed)))) :=
    revealBlockDecode relaxed wholeProfile (execution seed).application.config after reach
      (boundary seed supported).ordered afterPrefix publications allOpened count program profile
      prefixed refs embedding refsBefore low (source seed) (aligned seed)
      (agreeAlong seed supported reach) []
      (by rw [List.append_nil]; exact (checkpoint seed).history)
      (fun completion => by
        simp only [List.not_mem_nil, false_iff, not_and, not_lt]
        intro _ lower
        exact lower)
      List.Pairwise.nil le_rfl rfl
  -- Along the runs on which the deviator has not withheld, the block is opened.
  have openedRun (seed : Seed) (supported : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (app.runUntil scheduler
        (blockPlayers bound turns wholeProfile who deviation assignment) (BlockDone (low + count))
        (horizon - (execution seed).environmentRecall.length) (execution seed)).support)
      (live : ¬ DeviatorWithheld who final.application.config) :
      ConfigReaches setup (execution seed).application.config final.application.config ∧
        final.application.config.cut.IsPrefix (low + count) ∧
        ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
          event.val < low + count → OpenedAt final.application.config event := by
    obtain ⟨⟨trace⟩, ownSlots, answered⟩ := startFacts seed supported
    have start := boundary seed supported
    have done := runUntil_blockDone_of_trace _ contract.completes (low + count) _ _ final trace
      reached
    have reach := runUntil_configReaches scheduler _ _ _ _ final reached
    have inside := runUntil_within sealed scheduler _ _ _ final
      (start.withinBlock (Nat.le_add_right _ _)) reached
    refine ⟨reach, inside.within.isPrefix wall.1 done, fun event lower upper => ?_⟩
    obtain ⟨index, below, rfl⟩ := prefixed.embedded (aligned seed).graphSuffix event lower upper
    obtain ⟨owner, payload, binding, checks, outputEq, codeEq, _, owned⟩ :=
      CompiledSuffix.revealPrefix_resolve (mode := mode) count program prefixed refs _ _
        embedding refsBefore low (aligned seed).graphSuffix index below
    by_cases isWho : owner = who
    · subst isWho
      by_contra notOpened
      exact live ⟨_, nodeView_resolve_actor outputEq codeEq, notOpened⟩
    · rw [blockPlayers_eq_drawnPlayers] at reached
      exact openBlock_opened contract timely turns wholeProfile (· ≠ who) (fun _ => deviation)
        (execution seed) start.ordered start.untouched
        (fun owner honest => (ownSlots owner honest).1) answered count program prefixed refs
        (source seed).revelations (source seed).registry embedding refsBefore
        (aligned seed).graphSuffix _ 0
        (by simpa only [Nat.zero_add] using trace) final reached index below
        (fun other otherOwned => by
          rw [owned] at otherOwned
          cases otherOwned
          exact isWho)
        (done _ upper)
  refine ⟨fun seed supported final reached live => ?_, ?_⟩
  · unfold ReactiveApplication.runUntilHorizon at reached
    rw [opened seed supported] at reached
    obtain ⟨reach, finalPrefix, allOpened⟩ := openedRun seed supported final reached live
    exact decodeOpened seed supported _ reach finalPrefix allOpened
  -- The openings assigned are those of every other owner of the block.
  have assigned : ∀ event owner, low ≤ event.val → event.val < low + count →
      (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
        ∀ {payload : L.Ty}
          (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload),
          assignment event = some (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            true) := by
    intro event owner lower upper actor honest payload outputEq
    obtain ⟨index, below, rfl⟩ := prefixed.embedded suffix event lower upper
    obtain ⟨owner', payload', binding, checks, outputEq', codeEq', _, owned⟩ :=
      CompiledSuffix.revealPrefix_resolve (mode := mode) count program prefixed refs _ _
        embedding refsBefore low suffix index below
    have ownerIs : owner' = owner :=
      Option.some.inj ((nodeView_resolve_actor outputEq' codeEq').symm.trans actor)
    subst ownerIs
    exact openAssignment_opens (· ≠ who) count program prefixed embedding (fun _ => none) index
      below (fun other otherOwned => by
        rw [owned] at otherOwned
        cases otherOwned
        exact honest) outputEq
  -- The deviator's traffic, gated by withholding.
  let gate := fun final : app.Execution =>
    if DeviatorWithheld who final.application.config then none else some (traffic final)
  have gateReadout (rounds : Nat) (start : app.Execution) :
      (app.runUntil scheduler (blockPlayers bound turns wholeProfile who deviation assignment)
          (BlockDone (low + count)) rounds start).map gate =
        ((app.runUntil scheduler (blockPlayers bound turns wholeProfile who deviation assignment)
          (BlockDone (low + count)) rounds start).map
            (openedReadout who low (low + count))).map (Option.map Prod.fst) := by
    rw [PMF.map_comp]
    congr 1
    funext final
    simp only [gate, Function.comp_apply, openedReadout]
    split_ifs <;> rfl
  have coupled : ∀ left ∈ prior.support, ∀ _leftAction ∈ (PMF.pure () : PMF Unit).support,
      ∀ right ∈ prior.support, ∀ _rightAction ∈ (PMF.pure () : PMF Unit).support,
      (openChain count program prefixed (source left)).view who =
        (openChain count program prefixed (source right)).view who →
      traffic (execution left) = traffic (execution right) →
      (app.runUntilHorizon scheduler players (BlockDone (low + count)) horizon
          (execution left)).map gate =
        (app.runUntilHorizon scheduler players (BlockDone (low + count)) horizon
          (execution right)).map gate := by
    intro left leftSupported _ _ right rightSupported _ _ sameView sameRead
    obtain ⟨⟨leftTrace⟩, leftOwn, leftAnswered⟩ := startFacts left leftSupported
    obtain ⟨⟨rightTrace⟩, rightOwn, rightAnswered⟩ := startFacts right rightSupported
    have counts : horizon - (execution left).environmentRecall.length =
        horizon - (execution right).environmentRecall.length := by
      rw [show (execution left).environmentRecall = (execution right).environmentRecall from
        congrArg (fun value => value.2.2.1) sameRead]
    -- Openings of the two starts, completed beyond the run.
    obtain ⟨leftVirtual, leftReach, leftPrefix, leftOpened⟩ := exists_openedVirtual _
      (boundary left leftSupported).ordered count wall.1 publications
    obtain ⟨rightVirtual, rightReach, rightPrefix, rightOpened⟩ := exists_openedVirtual _
      (boundary right rightSupported).ordered count wall.1 publications
    obtain ⟨leftAgree, -⟩ := revealTail_agrees_of_decode count program prefixed refs _ _ embedding
      _ _ _
      (decodeOpened left leftSupported leftVirtual leftReach leftPrefix leftOpened)
    obtain ⟨rightAgree, -⟩ := revealTail_agrees_of_decode count program prefixed refs _ _ embedding
      _ _ _
      (decodeOpened right rightSupported rightVirtual rightReach rightPrefix rightOpened)
    have stores := (revealTail_store_agree who count program prefixed refs embedding _ _ _ _
      leftAgree rightAgree (congrArg Prod.fst sameView)).2
    have virtualAgree : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
        event.val < low + count → leftVirtual.outputs event = rightVirtual.outputs event := by
      intro event lower upper
      obtain ⟨index, below, rfl⟩ := prefixed.embedded suffix event lower upper
      exact stores index below
    have startReadouts : openedReadout who low (low + count) (execution left) =
        openedReadout who low (low + count) (execution right) := by
      unfold openedReadout
      rw [ite_eq_right (alive left leftSupported), ite_eq_right (alive right rightSupported)]
      refine congrArg some (Prod.ext sameRead ?_)
      change blockMarks who low (low + count) (execution left) =
        blockMarks who low (low + count) (execution right)
      rw [blockMarks_start who (boundary left leftSupported).untouched
          (fun owner honest => (leftOwn owner honest).1),
        blockMarks_start who (boundary right rightSupported).untouched
          (fun owner honest => (rightOwn owner honest).1)]
    unfold ReactiveApplication.runUntilHorizon
    rw [opened left leftSupported, opened right rightSupported, gateReadout, gateReadout, counts]
    congr 1
    exact openedBlock_readout_congr sealed publications contract timely turns wholeProfile who
      deviation assignment assigned (execution left) (execution right)
      (boundary left leftSupported).ordered (boundary right rightSupported).ordered leftReach
      rightReach leftPrefix rightPrefix leftOpened rightOpened virtualAgree _ _ _
      (OpenedBlockRun.initial bound who (Nat.le_add_right _ _) (execution left)
        ⟨0, ⟨by rw [Nat.zero_add, ← counts]; exact leftTrace⟩⟩
        (boundary left leftSupported).ordered (boundary left leftSupported).untouched
        (fun owner honest => (leftOwn owner honest).1) leftAnswered)
      (OpenedBlockRun.initial bound who (Nat.le_add_right _ _) (execution right)
        ⟨0, ⟨by rw [Nat.zero_add]; exact rightTrace⟩⟩
        (boundary right rightSupported).ordered (boundary right rightSupported).untouched
        (fun owner honest => (rightOwn owner honest).1) rightAnswered)
      startReadouts
  obtain ⟨kernel, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => traffic (execution seed)) (fun config => config.view who) noise factor
    (fun _ => PMF.pure ()) (fun config _ => openChain count program prefixed config)
    (fun config => config.view who)
    (fun seed _ => (app.runUntilHorizon scheduler players (BlockDone (low + count)) horizon
      (execution seed)).map gate)
    (fun left _ _ _ right _ _ _ same => openChain_view_reflects who count program prefixed left
      right same) coupled
  refine ⟨kernel, ?_⟩
  have mapped := congrArg (PMF.map fun pair : Config Player L _ × Option _ =>
    pair.2.map fun extra => (pair.1, extra)) law
  simp only [PMF.map_bind, PMF.pure_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]
    at mapped
  refine Eq.trans ?_ (mapped.trans ?_)
  · apply bind_congr_on_support _
    intro seed _
    apply map_congr_on_support _
    intro final _
    simp only [gate]
    split_ifs <;> rfl
  · simp only [PMF.bind_map, Function.comp_def]

end Block

end Vegas
