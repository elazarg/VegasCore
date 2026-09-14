/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedReadOrigin
import Vegas.Compile.SealedSourceInputs
import Vegas.Compile.SealedReplay
import Vegas.Compile.RevealAccounting
import Interaction.SealedResolutionEvents

/-! # Public terminal reconstruction for sealed resolution

Public settlement replays only public initial fields and opening events.
Acceptance events remain opaque: their values are never recovered from the
ideal commitment service.  Compiled payoff evaluation is one projection of
this public store, not a definition of utility.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Initial graph fields whose ownership metadata marks them public. -/
def initialPublicStore (G : Graph Player L) : Store L := fun field =>
  match G.field? field with
  | none => none
  | some spec => if spec.owner = none then spec.initialValue? else none

/-- Replay public openings without inspecting accepted commitment handles. -/
def replayPublicOpenings (G : Graph Player L) (ty : L.Ty) (store : Store L) :
    List (SealedProgram.Event Player (L.Val ty)) → Store L
  | [] => store
  | .accepted _ _ :: rest => G.replayPublicOpenings ty store rest
  | .opened node value :: rest =>
      G.replayPublicOpenings ty (store.set (G.nodeTarget node) ⟨ty, value⟩) rest

/-- Store observable from public initial data and the public event log alone. -/
def publicSealedStore (G : Graph Player L) (ty : L.Ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) : Store L :=
  G.replayPublicOpenings ty G.initialPublicStore events

/-- Logical source choices used only to witness a public settlement. They may
differ from private registrations after a publication defaults. -/
private def revealAssignment (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L) : Fin G.nodeCount → L.Val ty := by
  classical
  exact fun producer =>
    if found : ∃ node, (G.nodeRow node).sem = .reveal (G.nodeTarget producer) then
      (Store.getAs store (G.nodeTarget (Classical.choose found).val) ty).getD fallback
    else fallback

private theorem replayPublicOpenings_available (G : Graph Player L)
    (ty : L.Ty) (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (havailable : (Store.getAs store field ty).isSome) :
    (Store.getAs (G.replayPublicOpenings ty store events) field ty).isSome := by
  induction events generalizing store with
  | nil => exact havailable
  | cons event rest ih =>
      cases event with
      | accepted node handle => exact ih store havailable
      | opened node value =>
          apply ih
          by_cases heq : field = G.nodeTarget node
          · subst field
            simp [Store.getAs, TypedValue.as?]
          · rw [Store.getAs_set_ne store heq]
            exact havailable

/-- Any recorded opening makes its target field available to public outcome
evaluation. Later openings have the same type and preserve availability. -/
theorem publicSealedStore_available_of_opened (G : Graph Player L)
    (ty : L.Ty) (events : List (SealedProgram.Event Player (L.Val ty)))
    (node : Nat) (value : L.Val ty) (hopened : .opened node value ∈ events) :
    (Store.getAs (G.publicSealedStore ty events) (G.nodeTarget node) ty).isSome := by
  suffices ∀ store, (Store.getAs (G.replayPublicOpenings ty store events)
      (G.nodeTarget node) ty).isSome from this G.initialPublicStore
  induction events with
  | nil => simp at hopened
  | cons event rest ih =>
      intro store
      rcases List.mem_cons.mp hopened with rfl | htail
      · rw [replayPublicOpenings]
        apply G.replayPublicOpenings_available
        simp [Store.getAs, TypedValue.as?]
      · cases event <;> exact ih htail _

private theorem replayPublicOpenings_getAs_initial (G : Graph Player L)
    (ty : L.Ty) (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (fieldTy : L.Ty) (hfield : ∀ node, field ≠ G.nodeTarget node) :
    Store.getAs (G.replayPublicOpenings ty store events) field fieldTy =
      Store.getAs store field fieldTy := by
  induction events generalizing store with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | accepted node handle => exact ih store
      | opened node value =>
          rw [replayPublicOpenings, ih, Store.getAs_set_ne store (hfield node)]

/-- Public initial data survives replay unchanged; accepted handles supply no
public values and opening targets are freshly allocated event fields. -/
theorem publicSealedStore_getAs_initial (G : Graph Player L)
    (ty : L.Ty) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (spec : FieldSpec Player L) (value : L.Val spec.ty)
    (hfield : G.field? field = some spec) (hsource : spec.source = .initial value)
    (hpublic : spec.owner = none) :
    Store.getAs (G.publicSealedStore ty events) field spec.ty = some value := by
  rw [publicSealedStore, G.replayPublicOpenings_getAs_initial ty _ events field spec.ty
    (G.initial_field_ne_target field spec value hfield hsource)]
  simp [Store.getAs, initialPublicStore, hfield, hpublic, FieldSpec.initialValue?,
    hsource, TypedValue.as?]

end Vegas.EventGraph.Graph

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

omit [DecidableEq (L.Val ty)] in
/-- Every typed public field is available after completion, including runs
with commitment and reveal defaults. No source decoding is assumed. -/
theorem publicSealedStore_available_of_complete
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete state.visible = true)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    ∃ value, Store.getAs (G.publicSealedStore ty state.visible.events)
      ref.field ref.ty = some value := by
  rcases supported.publicField_origin ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨node, producer, owner, guard, htarget, hrefty, hsem, hcommit⟩
  · rw [← hty]
    exact ⟨value, G.publicSealedStore_getAs_initial ty state.visible.events
      ref.field spec value hfield hsource howner⟩
  · have hcompleted : state.visible.completed node.val = true := by
      apply List.all_eq_true.mp hcomplete node.val
      have hlen : supported.compile.rules.length = G.nodeCount := by
        simp [SealedFragment.compile, Graph.nodeOrder]
      simpa only [List.mem_range, resolvingRuntime, hlen] using node.isLt
    have hrule : supported.compile.rules[node.val]? =
        some ⟨.reveal owner producer.val, G.messagePrerequisites node⟩ := by
      rw [supported.compile_rule]
      exact congrArg some (G.sealedRule_reveal_eq node producer owner guard hsem hcommit)
    obtain ⟨value, hopened⟩ := hinvariant.opened_of_completed_reveal
      node.val owner producer.val (G.messagePrerequisites node) hrule hcompleted
    have havailable := G.publicSealedStore_available_of_opened ty
      state.visible.events node.val value hopened
    rw [htarget, hrefty]
    exact Option.isSome_iff_exists.mp havailable

omit [DecidableEq (L.Val ty)] in
private theorem replayPublicOpenings_agrees
    (supported : SealedFragment G ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (allEvents events : List (SealedProgram.Event Player (L.Val ty)))
    (hsub : ∀ event, event ∈ events → event ∈ allEvents)
    (haccepted : ∀ node handle, .accepted node handle ∈ allEvents →
      ∃ owner value rule,
        supported.compile.rules[node]? = some rule ∧ rule.kind = .commit owner ∧
          handle = (owner, node) ∧ service.lookup handle = some value)
    (publicStore : Store L) (cfg result : Config G)
    (hagrees : ∀ field spec, G.field? field = some spec → spec.owner = none →
      publicStore field = cfg.store field)
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    ∀ field spec, G.field? field = some spec → spec.owner = none →
      G.replayPublicOpenings ty publicStore events field = result.store field := by
  induction events generalizing publicStore cfg with
  | nil =>
      cases Option.some.inj hdecode
      exact hagrees
  | cons event rest ih =>
      have htail : ∀ prior, prior ∈ rest → prior ∈ allEvents := by
        intro prior hprior
        exact hsub prior (List.mem_cons_of_mem event hprior)
      unfold Graph.decodeSealedFrom at hdecode
      unfold Graph.decodeSealedEvent at hdecode
      split at hdecode
      · rename_i hnode
        cases event with
        | accepted node handle =>
            cases hlookup : service.lookup handle with
            | none => simp [hlookup] at hdecode
            | some value =>
                simp only [hlookup, Option.map_some, Option.bind_some] at hdecode
                dsimp only [Graph.replayPublicOpenings]
                apply ih htail _ _ ?_ hdecode
                intro field spec hfield hpublic
                by_cases heq : field = G.nodeTarget node
                · subst field
                  obtain ⟨owner, stored, rule, hrule, hkind, hhandle, _⟩ :=
                    haccepted node handle (hsub _ (List.mem_cons_self ..))
                  obtain ⟨index, guard, hindex, hsem⟩ :=
                    supported.ruleAt_commit hrule hkind
                  have htarget := G.field?_nodeTarget
                    (G.nodes_get?_nodeRow index)
                  rw [hindex] at htarget
                  rw [hfield] at htarget
                  have hwf := supported.graphWF index (G.nodeRow index)
                    (G.nodes_get?_nodeRow index)
                  unfold Graph.nodeWFAt at hwf
                  rw [hsem] at hwf
                  have howner : spec.owner = some owner := by
                    rw [Option.some.inj htarget]
                    exact hwf.2.2.1
                  rw [hpublic] at howner
                  contradiction
                · simp only [Config.completeNode, SealedProgram.Event.node]
                  rw [Store.set_ne _ heq]
                  exact hagrees field spec hfield hpublic
        | opened node value =>
            simp only [Option.bind_some] at hdecode
            dsimp only [Graph.replayPublicOpenings]
            apply ih htail _ _ ?_ hdecode
            intro field spec hfield hpublic
            by_cases heq : field = G.nodeTarget node
            · subst field
              simp [Config.completeNode, SealedProgram.Event.node]
            · simp only [Config.completeNode, SealedProgram.Event.node]
              rw [Store.set_ne _ heq, Store.set_ne _ heq]
              exact hagrees field spec hfield hpublic
      · simp at hdecode

omit [DecidableEq (L.Val ty)] in
/-- Public reconstruction agrees with proof-side decoding on every typed
public graph field.  The result does not inspect the ideal service. -/
theorem publicSealedStore_agrees
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (cfg : Config G)
    (hdecode : G.decodeSealedFrom ty state.service (Config.initial G)
      state.visible.events = some cfg)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty state.visible.events) ref.field ref.ty =
      Store.getAs cfg.store ref.field ref.ty := by
  obtain ⟨spec, hfield, hty, howner⟩ := hpublic
  have hagrees := supported.replayPublicOpenings_agrees state.service
    state.visible.events state.visible.events (fun _ h => h)
    hinvariant.acceptedBinding.accepted G.initialPublicStore (Config.initial G) cfg
    (by
      intro field initialSpec hinitial hpublic
      simp only [Graph.initialPublicStore, hinitial, if_pos hpublic,
        Config.initial, Graph.initialStore]) hdecode ref.field spec hfield howner
  unfold Store.getAs Graph.publicSealedStore
  rw [hagrees]

end Vegas.EventGraph.SealedFragment

namespace Vegas.SealedCompilation

open EventGraph Interaction ToEventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

/-- The compiled source payout evaluated solely from public native data.
Applications may instead apply any utility or outcome map to `publicSealedStore`.
-/
def publicPayout? (_compilation : SealedCompilation source ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) : Option (Payout Player) :=
  evalPayoffs? (ToEventGraph.compile source.core).payoffs
    ((ToEventGraph.compile source.core).graph.publicSealedStore ty events)

/-- Public payout evaluation is total at every invariant completed native
state, including after timeout defaults. -/
theorem publicPayout?_isSome_of_complete
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state.visible = true) :
    ∃ payout, compilation.publicPayout? state.visible.events = some payout := by
  apply evalPayoffs?_isSome_of_available
  intro payoff hpayoff ref href
  exact compilation.supported.publicSealedStore_available_of_complete nullValue window
    state hinvariant hcomplete ref
    ((ToEventGraph.compile source.core).payoffsWF payoff hpayoff ref href).1

private theorem evalPayoffEntries?_eq_of_getAs_eq
    (payoffs : List (Player × EventPayoff L)) (left right : Store L)
    (heq : ∀ payoff, payoff ∈ payoffs → ∀ ref, ref ∈ payoff.2.reads →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    evalPayoffEntries? payoffs left = evalPayoffEntries? payoffs right := by
  induction payoffs with
  | nil => rfl
  | cons payoff rest ih =>
      have hhead : ∀ ref, ref ∈ payoff.2.reads →
          Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty := by
        intro ref href
        exact heq payoff (by simp) ref href
      have htail : evalPayoffEntries? rest left = evalPayoffEntries? rest right :=
        ih (by
          intro tailPayoff htailPayoff ref href
          exact heq tailPayoff (by simp [htailPayoff]) ref href)
      cases hleft : ReadEnv.ofStore? left payoff.2.reads with
      | none =>
          cases hright : ReadEnv.ofStore? right payoff.2.reads with
          | none => simp [evalPayoffEntries?, hleft, hright]
          | some rightEnv =>
              have hback := ReadEnv.ofStore?_eq_of_getAs_eq hright
                (fun ref href ↦ (hhead ref href).symm)
              rw [hleft] at hback
              contradiction
      | some leftEnv =>
          have hright := ReadEnv.ofStore?_eq_of_getAs_eq hleft hhead
          simp [evalPayoffEntries?, hleft, hright, htail]

private theorem evalPayoffs?_eq_of_getAs_eq
    (payoffs : List (Player × EventPayoff L)) (left right : Store L)
    (heq : ∀ payoff, payoff ∈ payoffs → ∀ ref, ref ∈ payoff.2.reads →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    evalPayoffs? payoffs left = evalPayoffs? payoffs right := by
  unfold evalPayoffs?
  rw [evalPayoffEntries?_eq_of_getAs_eq payoffs left right heq]

private theorem payout_source_of_public_store
    (store : Store L) (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1)
    (hagrees : ∀ ref, (compile source.core).graph.fieldRefPublic ref →
      Store.getAs store ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      evalPayoffs? (compile source.core).payoffs store =
        some (evalPayoffs (compile source.core).sourcePayoffs terminalEnv) := by
  obtain ⟨terminalEnv, hstar, hcfgPayout, _hbindings⟩ :=
    compile_sourceStar source.core cfg.1 cfg.2 hterminal
  refine ⟨terminalEnv, hstar, ?_⟩
  rw [evalPayoffs?_eq_of_getAs_eq (compile source.core).payoffs store cfg.1.store, hcfgPayout]
  intro payoff hpayoff ref href
  exact hagrees ref ((compile source.core).payoffsWF payoff hpayoff ref href).1

/-- On every decoded terminal source realization, the payout loaded only from
public initial fields and opening events is exactly the written source payout.
The witness is supplied by source adequacy; no private commitment value is
read during public reconstruction. -/
theorem publicPayout?_eq_source_of_terminal
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (cfg : ReachableConfig (ToEventGraph.compile source.core).graph)
    (hterminal : Terminal (ToEventGraph.compile source.core).graph cfg.1)
    (hdecode : (ToEventGraph.compile source.core).graph.decodeSealedFrom ty state.service
      (Config.initial _) state.visible.events = some cfg.1) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx,
          env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      compilation.publicPayout? state.visible.events =
        some (evalPayoffs (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) := by
  exact payout_source_of_public_store _ cfg hterminal
    (compilation.supported.publicSealedStore_agrees nullValue window state hinvariant cfg.1 hdecode)

private theorem exists_terminal_values [Finite Player]
    (compilation : SealedCompilation source ty) (fallback : L.Val ty)
    (values : Fin (compile source.core).graph.nodeCount → L.Val ty) :
    ∃ cfg : ReachableConfig (compile source.core).graph,
      Terminal (compile source.core).graph cfg.1 ∧
      ∀ node owner guard, ((compile source.core).graph.nodeRow node).sem = .commit owner guard →
        cfg.1.nodeValues fallback node = values node := by
  let : Fintype Player := Fintype.ofFinite Player
  let graph := (compile source.core).graph
  let policies := fun who => compilation.supported.valuePolicy values who
  let initial : ReachableConfig graph := ⟨Config.initial graph, .initial⟩
  let law := runPolicyNodes (compile source.core).graphWF
    (compile_guardLive source.core source.legal) policies initial graph.nodeOrder
  obtain ⟨cfg, hcfg⟩ := law.support_nonempty
  have hterminal : Terminal graph cfg.1 := runPolicyNodes_terminal
    (compile source.core).graphWF (compile_guardLive source.core source.legal)
    policies initial graph.nodeOrder graph.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
  refine ⟨cfg, hterminal, ?_⟩
  intro node owner guard hsem
  have hchoices := runPolicyNodes_support_commitValues (compile source.core).graphWF
    (compile_guardLive source.core source.legal) policies initial
    (CommitValuesSupported.initial _) graph.nodeOrder cfg hcfg
  obtain ⟨reads, _, choice, hchoice, hvalue⟩ := hchoices node (hterminal node) owner guard hsem
  simp only [policies, SealedFragment.valuePolicy, FinDist.mem_support_pure] at hchoice
  subst choice
  change cfg.1.store (graph.nodeTarget node) =
    some (⟨guard.ty, cast (congrArg L.Val
      (compilation.supported.commitType node owner guard hsem).symm) (values node)⟩ : TypedValue L)
    at hvalue
  rw [Config.nodeValues, Store.getAs, hvalue]
  simp only [TypedValue.as?, dif_pos (compilation.supported.commitType node owner guard hsem),
    cast_cast, cast_eq, Option.getD_some]

private theorem revealAssignment_reveal
    (fallback : L.Val ty) (store : Store L)
    (node producer : Fin (compile source.core).graph.nodeCount)
    (hsem : ((compile source.core).graph.nodeRow node).sem =
      .reveal ((compile source.core).graph.nodeTarget producer)) :
    (compile source.core).graph.revealAssignment fallback store producer =
      (Store.getAs store ((compile source.core).graph.nodeTarget node) ty).getD fallback := by
  classical
  have found : ∃ node, ((compile source.core).graph.nodeRow node).sem =
      .reveal ((compile source.core).graph.nodeTarget producer) := ⟨node, hsem⟩
  rw [Graph.revealAssignment, dif_pos found]
  rw [source.compiled_reveal_source_injective _ node _ (Classical.choose_spec found) hsem]

private theorem exists_terminal_public_store [Finite Player]
    (compilation : SealedCompilation source ty) (fallback : L.Val ty)
    (store : Store L)
    (havailable : ∀ ref, (compile source.core).graph.fieldRefPublic ref →
      ∃ value, Store.getAs store ref.field ref.ty = some value)
    (hinitial : ∀ field (spec : FieldSpec Player L) (value : L.Val spec.ty),
      (compile source.core).graph.field? field = some spec →
      spec.source = .initial value → spec.owner = none →
      Store.getAs store field spec.ty = some value) :
    ∃ cfg : ReachableConfig (compile source.core).graph,
      Terminal (compile source.core).graph cfg.1 ∧
      ∀ ref, (compile source.core).graph.fieldRefPublic ref →
        Store.getAs store ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty := by
  obtain ⟨cfg, hterminal, hvalues⟩ := compilation.exists_terminal_values fallback
    ((compile source.core).graph.revealAssignment fallback store)
  refine ⟨cfg, hterminal, ?_⟩
  intro ref hpublic
  rcases compilation.supported.publicField_origin ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨node, producer, owner, guard, htarget, hrefty, hsem, hcommit⟩
  · rw [← hty, hinitial ref.field spec value hfield hsource howner]
    have hcfg := Graph.reachable_store_eq_initial_of_not_nodeTarget cfg.2 ref.field
      (fun node => (compile source.core).graph.initial_field_ne_target
        ref.field spec value hfield hsource node.val)
    simp [Store.getAs, hcfg, Graph.initialStore, hfield, FieldSpec.initialValue?,
      hsource, TypedValue.as?]
  · have hav := havailable ref hpublic
    rw [htarget, hrefty] at hav ⊢
    obtain ⟨value, hvalue⟩ := hav
    rw [hvalue, Store.getAs, compilation.supported.terminal_reveal_store cfg hterminal fallback
      node producer hsem, hvalues producer owner guard hcommit,
      revealAssignment_reveal fallback store node producer hsem,
      hvalue]
    simp [TypedValue.as?]

/-- Every completed invariant native state has the public store of a legal
terminal source realization, including after timeout defaults. Source accounting
ensures direct reveals have distinct producers; it is not an extra admission
premise. This support correspondence does not preserve private registrations or
the laws of fixed source policies. -/
theorem public_store_source_of_complete [Finite Player]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state.visible = true) :
    ∃ cfg : ReachableConfig (compile source.core).graph,
      Terminal (compile source.core).graph cfg.1 ∧
      ∀ ref, (compile source.core).graph.fieldRefPublic ref →
        Store.getAs ((compile source.core).graph.publicSealedStore ty state.visible.events)
          ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty := by
  apply compilation.exists_terminal_public_store nullValue _
  · exact compilation.supported.publicSealedStore_available_of_complete nullValue window
      state hinvariant hcomplete
  · exact (compile source.core).graph.publicSealedStore_getAs_initial ty state.visible.events

/-- Public settlement after arbitrary native completion equals the written
source payout of a legal source execution. This includes timeout defaults and
requires neither successful private-state decoding nor timely message service.
It is an existence statement, not a unilateral deviation-law backtranslation. -/
theorem publicPayout?_eq_source_of_complete [Finite Player]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state.visible = true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      compilation.publicPayout? state.visible.events =
        some (evalPayoffs (compile source.core).sourcePayoffs terminalEnv) := by
  obtain ⟨cfg, hterminal, hagrees⟩ :=
    compilation.public_store_source_of_complete nullValue window state hinvariant hcomplete
  exact payout_source_of_public_store _ cfg hterminal hagrees

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.publicPayout?_eq_source_of_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.publicPayout?_eq_source_of_terminal

/-- info: 'Vegas.SealedCompilation.publicPayout?_eq_source_of_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.publicPayout?_eq_source_of_complete
