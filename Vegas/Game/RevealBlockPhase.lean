module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.LastOwnedPhase
public import Vegas.Game.RevealBlockJoint
public import Vegas.Game.RevealBlockGraph

@[expose] public section

/-! # The phase of a block of concurrent reveals

A flat block of concurrent reveals is one phase of the deviation simulation.
On the ledger its successor key and final traffic keep the factored form. On
the graph, when the deviator is served last, every honest block reveal is
completed first, and then the deviator's block reveal, if any, by a policy
patched there with the deviator's conditional choice on the ledger. On average,
the last-served erased-key law of every normalized deviation of the base after
the phase is that law of its patched policy before the phase.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A final execution of a block run has no automatically ready event. -/
theorem blockRun_quiescent {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    {finish : Nat} (execution : (serviceApplication setup mode duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      players (fun current => BlockDone finish current.application.config) horizon
      execution).support) :
    final.application.config.Quiescent := by
  let app := serviceApplication setup mode duration leaks
  have finalSupported := app.roundsFrom_runUntil scheduler players (serviceInitialLaw setup mode)
    (fun current => BlockDone finish current.application.config) _ execution final supported
    reached
  obtain ⟨used, usedLe, _, lengths⟩ := app.runUntil_runRounds scheduler players
    (fun current => BlockDone finish current.application.config) _ execution final reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players final.environmentRecall.length (by omega) final finalSupported
  exact quiescent_of_automatic _ (legalFacts setup leaks horizon scheduler _ trace).quiescent

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- **Averaged targets from a channel.** When the final traffic of a phase is a
channel read from a view of the starting key and the final key is read from the
starting key and the final traffic, an average of targets after the phase is an
average of targets before it once each target before is the channel average of
targets after. -/
theorem averaged_target_of_channel {Seed Key View Traffic Final Out : Type}
    (prior : PMF Seed) (key : Seed → Key) (run : Seed → PMF Final)
    (traffic : Final → Traffic) (finalKey : Final → Key) (view : Key → View)
    (channel : View → PMF Traffic) (endKey : Key → Traffic → Key)
    (after before : Key → PMF Out)
    (joint : (prior.bind fun seed => (run seed).map fun final => (key seed, traffic final)) =
      (prior.map key).bind fun current => (channel (view current)).map fun extra =>
        (current, extra))
    (ends : ∀ seed ∈ prior.support, ∀ final ∈ (run seed).support,
      finalKey final = endKey (key seed) (traffic final))
    (pointwise : ∀ current ∈ (prior.map key).support,
      before current = (channel (view current)).bind fun extra => after (endKey current extra)) :
    (prior.bind fun seed => (run seed).bind fun final => after (finalKey final)) =
      prior.bind fun seed => before (key seed) := by
  calc (prior.bind fun seed => (run seed).bind fun final => after (finalKey final))
      = prior.bind fun seed => ((run seed).map fun final => (key seed, traffic final)).bind
          fun pair => after (endKey pair.1 pair.2) := by
        apply bind_congr_on_support _
        intro seed member
        rw [PMF.bind_map]
        apply bind_congr_on_support _
        intro final reached
        simp only [Function.comp_apply, ends seed member final reached]
    _ = ((prior.map key).bind fun current => (channel (view current)).map fun extra =>
          (current, extra)).bind fun pair => after (endKey pair.1 pair.2) := by
        rw [← joint, PMF.bind_bind]
    _ = (prior.map key).bind fun current =>
          (channel (view current)).bind fun extra => after (endKey current extra) := by
        rw [PMF.bind_bind]
        apply bind_congr_on_support _
        intro current _
        rw [PMF.bind_map]
        rfl
    _ = (prior.map key).bind before :=
        (bind_congr_on_support _ pointwise).symm
    _ = prior.bind fun seed => before (key seed) := by
        rw [PMF.bind_map]
        rfl

/-- **A block of concurrent reveals.** From a coupled prior of block starts whose
deviator traffic is noise read from its normalized view of the order-free key,
the phase that runs a flat block of concurrent reveals to its end has a
successor key and final traffic of the same factored form, and a graph policy
patched at the deviator's block reveal with its conditional choice on the
ledger has, on average, the last-served erased-key law of its tail after the
phase, when honest clients and the base open a reveal exactly when its opening
is accepted. -/
theorem lastBlock_phase {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode duration leaks).Execution)
    (supported : ∀ seed ∈ prior.support, execution seed ∈
      ((serviceApplication setup mode duration leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
          turns (firstTurnTiming setup turns mode)
          ((serviceGraph setup mode).normalizeProfile base)) who deviation)
        (execution seed).environmentRecall.length).support)
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (begin : ∀ seed ∈ prior.support, BlockStart start finish (execution seed).application.config)
    (owners : ∀ seed ∈ prior.support, DefaultOwners (execution seed).application.config)
    (untouched : ∀ seed ∈ prior.support, ∀ event : (serviceGraph setup mode).EventId,
      start ≤ event.val → event.val < finish → Untouched setup leaks event (execution seed))
    (completes : ∀ seed ∈ prior.support, ∀ final ∈
      ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
          (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
          who deviation)
        (fun current => BlockDone finish current.application.config) horizon
        (execution seed)).support,
      BlockDone finish final.application.config)
    (noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
    (factor : prior.map (fun seed => (runKey (execution seed).application.config,
        (bindingTraffic (serviceTimeouts setup mode duration)) leaks who (execution seed))) =
      (prior.map fun seed => runKey (execution seed).application.config).bind fun current =>
        (noise (keyView who current)).map fun extra => (current, extra)) :
    ∃ (build : (serviceGraph setup mode).BehavioralPolicy who →
        (serviceGraph setup mode).BehavioralPolicy who)
      (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _),
      (prior.bind fun seed =>
        ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation)
          (fun current => BlockDone finish current.application.config) horizon
          (execution seed)).map fun final => (runKey final.application.config,
            (bindingTraffic (serviceTimeouts setup mode duration)) leaks who final)) =
        (prior.bind fun seed =>
          ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
            (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
              (firstTurnTiming setup turns mode)
              ((serviceGraph setup mode).normalizeProfile base)) who deviation)
            (fun current => BlockDone finish current.application.config) horizon
            (execution seed)).map fun final => runKey final.application.config).bind
          (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
      ∀ policy, (prior.bind fun seed =>
        ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation)
          (fun current => BlockDone finish current.application.config) horizon
          (execution seed)).bind fun final =>
            keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
              (runKey final.application.config)) =
        prior.bind fun seed =>
          keyTarget ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) who
            (runKey (execution seed).application.config) := by
  classical
  let G := serviceGraph setup mode
  let app := serviceApplication setup mode duration leaks
  let timeouts := serviceTimeouts setup mode duration
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) (G.normalizeProfile base)) who deviation
  let run := fun seed => app.runUntilHorizon scheduler players
    (fun current => BlockDone finish current.application.config) horizon (execution seed)
  let traffic := (bindingTraffic timeouts) leaks who
  let key := fun seed => runKey (execution seed).application.config
  let config := fun seed => (execution seed).application.config
  let view := fun current : RunKey G => (keyView who current, blockHidden who start finish current)
  let P := fun policy : G.BehavioralPolicy who => G.lastDeviationProfile base who policy
  obtain ⟨channel, nextNoise, endKey, joint, factored, ends⟩ := ledgerBlock_joint bound turns
    contract timely (G.normalizeProfile base) decides who deviation start finish shaped
    publications concurrent flat prior execution supported bounded begin owners untouched
    completes noise factor
  have honestLaw : ∀ (policy : G.BehavioralPolicy who) (current : G.Config)
      (event : G.EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef G.layout (.binding owner payload))
      (checks : List (GuardCheck G.layout payload))
      (outputEq : G.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
        .resolve owner payload binding checks),
      nodeView G event = .resolve owner payload binding checks outputEq codeEq →
      owner ≠ who → owner ∉ current.defaulted →
        actionLaw (P policy) current event = PMF.pure (cast (congrArg EventField.Action
          outputEq.symm) (openingAccepted event current.store)) := by
    intro policy current event owner payload binding checks outputEq codeEq node honest active
    have owned := nodeView_resolve_actor outputEq codeEq
    have ownedNode : (G.nodes event).actor = some owner := owned
    rw [actionLaw_lastDeviationProfile_other base who policy current
      (fun same => honest (Option.some.inj (ownedNode.symm.trans same))),
      actionLaw_of_actor _ _ ownedNode, dite_eq_right active]
    exact decides current event owner payload binding checks outputEq codeEq node owned active
  have finalFacts (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (run seed).support) :
      Relation.ReflTransGen Config.Step (config seed) final.application.config ∧
        BlockRecordsSound who start finish (config seed) final.application.config ∧
        DefaultOwners final.application.config ∧ BlockDone finish final.application.config ∧
        final.application.config.Quiescent := by
    obtain ⟨path, sound⟩ := blockRun_facts bound turns contract timely (G.normalizeProfile base)
      decides who deviation start finish shaped publications (execution seed)
      (supported seed member) (bounded seed member) (begin seed member).inside
      (untouched seed member) final reached
    exact ⟨path, sound, DefaultOwners.path path (owners seed member),
      completes seed member final reached,
      blockRun_quiescent (execution seed) (supported seed member) (bounded seed member) final
        reached⟩
  have realized (current : RunKey G) (extra : _)
      (member : extra ∈ (channel (view current)).support)
      (keyed : current ∈ (prior.map key).support) :
      ∃ seed ∈ prior.support, key seed = current ∧
        ∃ final ∈ (run seed).support, traffic final = extra := by
    have paired : (current, extra) ∈ ((prior.map key).bind fun current =>
        (channel (view current)).map fun extra => (current, extra)).support := by
      rw [PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨current, keyed, by
        rw [PMF.support_map]
        exact ⟨extra, member, rfl⟩⟩
    rw [← joint, PMF.support_bind] at paired
    obtain ⟨seed, seedMember, inner⟩ := Set.mem_iUnion₂.mp paired
    rw [PMF.support_map] at inner
    obtain ⟨final, reached, pairEq⟩ := inner
    obtain ⟨keyEq, extraEq⟩ := Prod.mk.inj pairEq
    exact ⟨seed, seedMember, keyEq, final, reached, extraEq⟩
  have startActive (seed : Seed) (member : seed ∈ prior.support) :
      ∀ event : G.EventId, start ≤ event.val → event.val < finish →
        event ∉ (config seed).cut.completed → ∀ owner, G.actor? event = some owner →
          owner ≠ who → owner ∉ (config seed).defaulted :=
    fun event early late pending owner owned _ inactive =>
      pending (((begin seed member).drained event early late).mpr ⟨owner, owned, inactive⟩)
  have closure (seed : Seed) (member : seed ∈ prior.support) (policy : G.BehavioralPolicy who) :
      ∃ final : G.Config,
        Relation.ReflTransGen Config.Step (config seed) final ∧
        (∀ event : G.EventId, event.val < start → event ∈ final.cut.completed) ∧
        (¬ BlockDone finish final → InBlock start finish final) ∧
        BlockRecordsSound who start finish (config seed) final ∧
        lastErasedLaw (P policy) who (config seed) = lastErasedLaw (P policy) who final ∧
        (∀ event : G.EventId, start ≤ event.val → event.val < finish →
          event ∉ final.cut.completed → G.actor? event = some who) ∧
        (∀ event, event ∈ final.cut.completed → event ∈ (config seed).cut.completed ∨
          (start ≤ event.val ∧ event.val < finish ∧ G.actor? event ≠ some who)) ∧
        (who ∈ final.defaulted → who ∈ (config seed).defaulted) := by
    by_cases done : BlockDone finish (config seed)
    · exact ⟨config seed, .refl, (begin seed member).earlier,
        fun running => (running done).elim, fun event fresh finished => (fresh finished).elim,
        rfl, fun event _ late pending => (pending (done event late)).elim,
        fun event finished => Or.inl finished, id⟩
    obtain ⟨final, path, inside, _, sound, law, pending, fresh, whoDefaulted⟩ :=
      lastErasedLaw_honest_block shaped flat publications concurrent (P policy)
        (honestLaw policy) (config seed) (config seed).remaining (config seed) rfl
        ((begin seed member).inside done) .refl (fun event fresh done => (fresh done).elim)
        (startActive seed member)
    exact ⟨final, path, inside.1, fun _ => inside, sound, law, pending, fresh, whoDefaulted⟩
  have honestDoneOf {seed : Seed} {final : G.Config}
      (pending : ∀ event : G.EventId, start ≤ event.val → event.val < finish →
        event ∉ final.cut.completed → G.actor? event = some who) :
      ∀ event : G.EventId, start ≤ event.val → event.val < finish →
        event ∉ (config seed).cut.completed → G.actor? event ≠ some who →
          event ∈ final.cut.completed :=
    fun event early late _ honest => by
      by_contra notDone
      exact honest (pending event early late notDone)
  -- the ends of runs whose deviator has no pending block reveal
  have quietEnds (seed : Seed) (member : seed ∈ prior.support) (policy : G.BehavioralPolicy who)
      (none : ∀ event : G.EventId, start ≤ event.val → event.val < finish →
        G.actor? event = some who → event ∈ (config seed).cut.completed) :
      ∃ final : G.Config,
        lastErasedLaw (P policy) who (config seed) = lastErasedLaw (P policy) who final ∧
        BlockDone finish final ∧
        ∀ other ∈ prior.support, key other = key seed → ∀ last ∈ (run other).support,
          runKey last.application.config = runKey (State.drainConfig final) := by
    obtain ⟨final, path, earlier, _, sound, law, pending, _, _⟩ := closure seed member policy
    have done : BlockDone finish final := by
      intro event late
      by_contra notDone
      by_cases early : start ≤ event.val
      · exact notDone (Config.Step.path_completed_mono path
          (none event early late (pending event early late notDone)))
      · exact notDone (earlier event (by omega))
    refine ⟨final, law, done, fun other otherMember keys last reached => ?_⟩
    obtain ⟨lastPath, lastSound, lastOwners, lastDone, lastQuiet⟩ :=
      finalFacts other otherMember last reached
    have drainPath : Relation.ReflTransGen Config.Step final (State.drainConfig final) :=
      State.drain_graph_steps (State.ofConfig final)
    exact blockEnd_runKey_eq_of_owned_of_keys concurrent flat keys (begin other otherMember)
      (begin seed member) lastPath (path.trans drainPath) lastSound sound.drainConfig
      lastOwners (DefaultOwners.path (path.trans drainPath) (owners seed member)) lastDone
      (BlockDone.path drainPath done) lastQuiet (drainConfig_quiescent final)
      (fun event early late pending owned => by
        have cuts : (config other).cut = (config seed).cut := congrArg Prod.fst keys
        exact (pending (cuts ▸ none event early late owned)).elim)
  have reduce (build : G.BehavioralPolicy who → G.BehavioralPolicy who)
      (pointwise : ∀ policy, ∀ current ∈ (prior.map key).support,
        keyTarget (P (build policy)) who current =
          (channel (view current)).bind fun extra =>
            keyTarget (P policy) who (endKey current extra)) :
      ∀ policy, (prior.bind fun seed => (run seed).bind fun final =>
          keyTarget (P policy) who (runKey final.application.config)) =
        prior.bind fun seed => keyTarget (P (build policy)) who (key seed) :=
    fun policy => averaged_target_of_channel prior key run traffic
      (fun final => runKey final.application.config) view channel endKey
      (keyTarget (P policy) who) (keyTarget (P (build policy)) who) joint ends
      (pointwise policy)
  have quietPointwise (build : G.BehavioralPolicy who → G.BehavioralPolicy who)
      (policy : G.BehavioralPolicy who) (seed : Seed) (member : seed ∈ prior.support)
      (none : ∀ event : G.EventId, start ≤ event.val → event.val < finish →
        G.actor? event = some who → event ∈ (config seed).cut.completed)
      (agreeAfter : ∀ final : G.Config, BlockDone finish final →
        lastErasedLaw (P (build policy)) who final = lastErasedLaw (P policy) who final) :
      keyTarget (P (build policy)) who (key seed) =
        (channel (view (key seed))).bind fun extra =>
          keyTarget (P policy) who (endKey (key seed) extra) := by
    obtain ⟨final, law, done, endsEq⟩ := quietEnds seed member (build policy) none
    rw [keyTarget_runKey (independent _), law, agreeAfter final done,
      ← State.drainConfig_lastErasedLaw (independent policy),
      ← keyTarget_runKey (independent policy)]
    have constant : ∀ extra ∈ (channel (view (key seed))).support,
        keyTarget (P policy) who (endKey (key seed) extra) =
          keyTarget (P policy) who (runKey (State.drainConfig final)) := by
      intro extra extraMember
      obtain ⟨other, otherMember, keys, last, reached, trafficEq⟩ := realized (key seed) extra
        extraMember ((PMF.mem_support_map_iff _ _ _).mpr ⟨seed, member, rfl⟩)
      rw [← trafficEq, ← keys, ← ends other otherMember last reached,
        endsEq other otherMember keys last reached]
    rw [bind_congr_on_support _ constant, PMF.bind_const]
  by_cases hasOwned : ∃ owned : G.EventId, start ≤ owned.val ∧ owned.val < finish ∧
      G.actor? owned = some who
  swap
  · push Not at hasOwned
    refine ⟨id, nextNoise, factored, reduce id fun policy current keyed => ?_⟩
    obtain ⟨seed, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp keyed
    exact quietPointwise id policy seed member
      (fun event early late owned => (hasOwned event early late owned).elim) (fun _ _ => rfl)
  obtain ⟨w, wEarly, wLate, wOwned⟩ := hasOwned
  have wNode : (G.nodes w).actor = some who := wOwned
  obtain ⟨wOwner, payload, binding, checks, outputEq, codeEq, node⟩ :=
    exists_resolve_of_publication (publications w wEarly wLate)
  have ownerEq : wOwner = who :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans wOwned)
  subst wOwner
  have unique : ∀ event : G.EventId, start ≤ event.val → event.val < finish →
      G.actor? event = some who → event = w :=
    fun event early late owned => block_actor_unique concurrent flat early late wEarly wLate
      owned wOwned
  let HonestClosure := fun (seed : Seed) (final : G.Config) =>
    Relation.ReflTransGen Config.Step (config seed) final ∧
      BlockRecordsSound who start finish (config seed) final ∧ DefaultOwners final ∧
      (∀ event : G.EventId, start ≤ event.val → event.val < finish →
        event ∉ (config seed).cut.completed → G.actor? event ≠ some who →
          event ∈ final.cut.completed) ∧
      (BlockDone finish (config seed) → final = config seed)
  obtain ⟨anchor, _⟩ := prior.support_nonempty
  let recover := fun observation : G.PlayerObservation who =>
    if found : ∃ seed ∈ prior.support, ∃ final, HonestClosure seed final ∧
        G.normalizeObservation who (G.playerObserve who final) = observation then
      view (key found.choose)
    else view (key anchor)
  let kernel := fun observation : Option (G.PlayerObservation who) =>
    match observation with
    | some seen => (channel (recover seen)).map fun extra : MessageNetwork Player app.Payload ×
          List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
          PlayerView G × PublicView G =>
        observedAction w extra.2.2.2.2.1.observation
    | none => PMF.pure none
  let build := fun tail : G.BehavioralPolicy who => patchPolicy w (ownedHead w kernel tail) tail
  refine ⟨build, nextNoise, factored, reduce build fun policy current keyed => ?_⟩
  obtain ⟨seed, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp keyed
  have agree : ∀ (current : G.Config) other, other ≠ w →
      actionLaw (P (build policy)) current other = actionLaw (P policy) current other :=
    fun current other different =>
      actionLaw_lastDeviationProfile_patch_of_ne base who w _ policy current different
  by_cases wDone : w ∈ (config seed).cut.completed
  · exact quietPointwise build policy seed member
      (fun event early late owned => by rw [unique event early late owned]; exact wDone)
      (fun final done => lastErasedLaw_patch_completed w agree final (done w wLate))
  obtain ⟨Y, pathY, earlierY, insideYOf, soundY, lawY, pendingY, freshY, whoY⟩ :=
    closure seed member (build policy)
  have whoActiveStart : who ∉ (config seed).defaulted := fun inactive =>
    wDone (((begin seed member).drained w wEarly wLate).mpr ⟨who, wOwned, inactive⟩)
  have whoActive : who ∉ Y.defaulted := fun inactive => whoActiveStart (whoY inactive)
  have wPendingY : w ∉ Y.cut.completed := fun done => by
    rcases freshY w done with old | ⟨_, _, honest⟩
    · exact wDone old
    · exact honest wOwned
  have wReady : Y.cut.Ready w := flat.ready_of_earlier earlierY wEarly wLate wPendingY
  have alone : ∀ other, Y.cut.Ready other → other = w := by
    intro other ready
    have running : ¬ BlockDone finish Y := fun done => wPendingY (done w wLate)
    have bounds := shaped Y (insideYOf running) running other ready
    exact unique other bounds.1 bounds.2 (pendingY other bounds.1 bounds.2 ready.1)
  have nonempty : Y.cut.enabled.Nonempty := ⟨w, (EventOrder.Cut.mem_enabled _ _).mpr wReady⟩
  have startReady := flat.ready_of_earlier (begin seed member).earlier wEarly wLate wDone
  have available : ∀ field ∈ (G.nodes w).readFields, ((config seed).store field).isSome :=
    fun field read => (config seed).read_available startReady read
  have keptY : ∀ field stored, (config seed).store field = some stored →
      Y.store field = some stored :=
    fun field stored found => Config.Step.path_store_of_some pathY field stored found
  have closureSeed : HonestClosure seed Y :=
    ⟨pathY, soundY, DefaultOwners.path pathY (owners seed member), honestDoneOf pendingY,
      fun done => (wDone (done w wLate)).elim⟩
  have recovered : recover (G.normalizeObservation who (G.playerObserve who Y)) =
      view (key seed) := by
    have found : ∃ other ∈ prior.support, ∃ final, HonestClosure other final ∧
        G.normalizeObservation who (G.playerObserve who final) =
          G.normalizeObservation who (G.playerObserve who Y) :=
      ⟨seed, member, Y, closureSeed, rfl⟩
    change (if found : ∃ other ∈ prior.support, ∃ final, HonestClosure other final ∧
        G.normalizeObservation who (G.playerObserve who final) =
          G.normalizeObservation who (G.playerObserve who Y) then
      view (key found.choose) else view (key anchor)) = _
    rw [dite_eq_left found]
    obtain ⟨otherMember, otherFinal, otherClosure, otherViews⟩ := found.choose_spec
    obtain ⟨startViews, hiddens⟩ := blockStart_reflect_general concurrent flat
      publications (begin _ otherMember) (begin seed member) otherClosure.1 pathY
      otherClosure.2.1 soundY otherClosure.2.2.1 closureSeed.2.2.1 otherClosure.2.2.2.1
      closureSeed.2.2.2.1 otherClosure.2.2.2.2 closureSeed.2.2.2.2 otherViews
    change (keyView who (runKey (config found.choose)),
        blockHidden who start finish (runKey (config found.choose))) =
      (keyView who (runKey (config seed)), blockHidden who start finish (runKey (config seed)))
    rw [keyView_runKey, keyView_runKey, startViews, hiddens]
  rw [keyTarget_runKey (independent _) (config seed), lawY,
    lastErasedLaw_patch_step w agree Y wReady (lastPick_eq_of_alone who Y alone nonempty)]
  unfold eventStep
  rw [actionLaw_lastDeviationProfile_owned base who (build policy) Y wNode whoActive]
  simp only [build, patchPolicy, ↓reduceIte]
  rw [ownedHead_self]
  simp only [kernel, PMF.bind_bind, PMF.bind_map]
  rw [recovered]
  apply bind_congr_on_support _
  intro extra extraMember
  obtain ⟨other, otherMember, keys, final, reached, trafficEq⟩ :=
    realized _ extra extraMember keyed
  subst trafficEq
  obtain ⟨finalPath, finalSound, finalOwners, finalDone, finalQuiet⟩ :=
    finalFacts other otherMember final reached
  have cuts : (config other).cut = (config seed).cut := congrArg Prod.fst keys
  have stores : (config other).store = (config seed).store :=
    congrArg (fun key => key.2.1) keys
  have wPendingOther : w ∉ (config other).cut.completed := by rw [cuts]; exact wDone
  have availableOther : ∀ field ∈ (G.nodes w).readFields, ((config other).store field).isSome :=
    by rw [stores]; exact available
  obtain ⟨record, recordFound, decided⟩ := decided_of_pending concurrent flat
    (begin other otherMember) finalPath finalSound finalOwners wEarly wLate wPendingOther
    (finalDone w wLate) wOwned
  obtain ⟨disclose, output, resolved, recorded, stored⟩ := resolve_record_of_path finalPath
    wPendingOther (finalDone w wLate) (outputEq := outputEq) (codeEq := codeEq) availableOther
    ⟨record, recordFound, decided⟩
  have observed : observedAction w (traffic final).2.2.2.2.1.observation =
      some (cast (congrArg EventField.Action outputEq.symm) disclose) :=
    observedAction_playerObserve who final.application.config w wOwned _ _
      ((completionOf_eq_some_iff _ _ _).mp recorded).1
  have resolvedY : EventCode.resolveOutput? binding checks disclose Y.store = some output := by
    rw [resolveOutput_keep keptY (outputEq := outputEq) codeEq available disclose, ← stores]
    exact resolved
  simp only [Function.comp_apply, observed, Option.elim, PMF.pure_bind]
  rw [resolve_step_eq wReady outputEq codeEq whoActive disclose output resolvedY, PMF.pure_bind,
    ← State.drainConfig_lastErasedLaw (independent policy),
    ← keyTarget_runKey (independent policy)]
  change _ = keyTarget (P policy) who (endKey (key seed) (traffic final))
  rw [← keys, ← ends other otherMember final reached]
  let stepped := Y.complete w wReady (cast (congrArg EventField.Action outputEq.symm) disclose)
    (cast (congrArg EventField.Value outputEq.symm) output)
  have steppedMember : stepped ∈ (Y.step w wReady
      (cast (congrArg EventField.Action outputEq.symm) disclose)).support := by
    rw [resolve_step_eq wReady outputEq codeEq whoActive disclose output resolvedY]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have moved : Config.Step Y stepped := ⟨w, wReady, _, steppedMember⟩
  have drainPath : Relation.ReflTransGen Config.Step stepped (State.drainConfig stepped) :=
    State.drain_graph_steps (State.ofConfig stepped)
  have graphPath : Relation.ReflTransGen Config.Step (config seed) (State.drainConfig stepped) :=
    (pathY.tail moved).trans drainPath
  have steppedSound : BlockRecordsSound who start finish (config seed) stepped := by
    intro event fresh done
    by_cases same : event = w
    · subst same
      exact Or.inr ⟨wEarly, wLate, Or.inl wOwned⟩
    · have old : event ∈ Y.cut.completed := by
        rw [Config.complete_cut, EventOrder.Cut.mem_complete] at done
        exact done.resolve_left same
      exact BlockRecordsSound.path (.single moved) soundY event fresh old
  have steppedDone : BlockDone finish stepped := by
    intro event late
    rw [Config.complete_cut, EventOrder.Cut.mem_complete]
    by_cases early : start ≤ event.val
    · by_cases same : event = w
      · exact Or.inl same
      · right
        by_contra notDone
        exact same (unique event early late (pendingY event early late notDone))
    · exact Or.inr (earlierY event (by omega))
  have steppedRecord : completionOf stepped w = some (EventGraph.completion G w
      (some (cast (congrArg EventField.Action outputEq.symm) disclose))
      (cast (congrArg EventField.Value outputEq.symm) output)) := by
    rw [completionOf_complete, Function.update_self,
      Y.actualDecision_of_active w who wNode whoActive]
  have steppedDoneW : w ∈ stepped.cut.completed := steppedDone w wLate
  congr 1
  symm
  refine blockEnd_runKey_eq_of_owned_of_keys concurrent flat keys (begin other otherMember)
    (begin seed member) finalPath graphPath finalSound steppedSound.drainConfig finalOwners
    (DefaultOwners.path graphPath (owners seed member)) finalDone
    (BlockDone.path drainPath steppedDone) finalQuiet (drainConfig_quiescent stepped) ?_
  intro event early late _ owned
  have same := unique event early late owned
  subst same
  refine ⟨recorded.trans (Config.Step.path_completionOf_of_some drainPath _ _
    steppedRecord).symm, ?_⟩
  rw [stored, outputs_path drainPath steppedDoneW, Config.complete_output_same]

end Vegas
