/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Safety
import Vegas.Graph.Semantics

/-! # Source layout in typed immutable graphs -/

noncomputable section
namespace Vegas.SourceProgram

open Interaction

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]

/-- The immutable graph layout of a source context. Private source cells retain
only their binding; their changing publication component is represented by a
`PublicationMap`. -/
def graphCtx : SourceCtx Player L → VCtx Player L
  | [] => []
  | (name, .publicData payload) :: Γ =>
      (name, .pub payload) :: graphCtx Γ
  | (name, .privateData owner payload) :: Γ =>
      (name, .sealed owner (R.result payload)) :: graphCtx Γ
  | (name, .publication payload) :: Γ =>
      (name, .pub (R.result payload)) :: graphCtx Γ

/-- Source membership transported to the corresponding graph field. -/
def fieldRef : {Γ : SourceCtx Player L} → { name : VarId } →
    { cell : CellTy Player L} → HasVar Γ name cell →
    HasVar (graphCtx (R := R) Γ) name
      (match cell with
       | .publicData payload => .pub payload
       | .privateData owner payload => .sealed owner (R.result payload)
       | .publication payload => .pub (R.result payload))
  | (_, .publicData _) :: _, _, _, .here => .here
  | (_, .privateData _ _) :: _, _, _, .here => .here
  | (_, .publication _) :: _, _, _, .here => .here
  | (_, .publicData _) :: _, _, _, .there h => .there (fieldRef h)
  | (_, .privateData _ _) :: _, _, _, .there h => .there (fieldRef h)
  | (_, .publication _) :: _, _, _, .there h => .there (fieldRef h)

/-- Current public read selected for every retained private source cell. -/
abbrev PublicationMap (Γ : SourceCtx Player L) :=
  ∀ {owner payload name}, HasVar Γ name (.privateData owner payload) →
    Graph.GuardRead (R := R) (graphCtx (R := R) Γ) payload

/-- Initially no private cell has a public result field. -/
def initialMap : {Γ : SourceCtx Player L} → PublicationMap (R := R) Γ
  | [] => fun h => nomatch h
  | (_, .publicData _) :: _ => fun
      | .there h => (initialMap h).weaken
  | (_, .publication _) :: _ => fun
      | .there h => (initialMap h).weaken
  | (_, .privateData _ _) :: _ => fun
      | .here => .pending
      | .there h => (initialMap h).weaken

/-- Extend all publication reads across a newly prepended source cell. -/
def weakenMap {Γ : SourceCtx Player L} (map : PublicationMap (R := R) Γ) :
    ∀ {name : VarId} {cell : CellTy Player L},
      PublicationMap (R := R) ((name, cell) :: Γ) :=
  fun {_ cell} => match cell with
    | .publicData _ => fun
        | .there h => (map h).weaken
    | .publication _ => fun
        | .there h => (map h).weaken
    | .privateData _ _ => fun
        | .here => .pending
        | .there h => (map h).weaken

/-- A freshly prepended publication field resolves exactly the selected
private resource; every other private read is transported beneath that head. -/
def resolveMap {Γ : SourceCtx Player L} (map : PublicationMap (R := R) Γ)
    (unique : (Γ.map Prod.fst).Nodup) {owner payload name}
    (source : HasVar Γ name (.privateData owner payload)) :
    ∀ {published : VarId},
      PublicationMap (R := R) ((published, .publication payload) :: Γ) :=
  fun {_ _ _ readName} read => match read with
    | .there read =>
      if same : readName = name then
        let cellEq := HasVar.type_unique unique (same ▸ read) source
        let payloadEq := (CellTy.privateData.inj cellEq).2
        payloadEq.symm ▸ Graph.GuardRead.publication .here
      else (map read).weaken

/-- Encode source state into immutable graph fields, dropping redundant
private publication statuses. -/
def encodeState : {Γ : SourceCtx Player L} → State L Γ → VEnv L (graphCtx (R := R) Γ)
  | [], _ => VEnv.empty L
  | (_, .publicData _) :: _, state =>
      VEnv.cons (state.get .here)
        (encodeState (fun _ _ h => state.get (.there h)))
  | (_, .privateData _ payload) :: _, state =>
      VEnv.cons ((R.valueEquiv payload).symm
        (BoundValue.resultEquiv _ (state.get .here).1))
        (encodeState (fun _ _ h => state.get (.there h)))
  | (_, .publication payload) :: _, state =>
      VEnv.cons ((R.valueEquiv payload).symm (state.get .here))
        (encodeState (fun _ _ h => state.get (.there h)))

/-- Reconstruct a source state from graph fields and the public read selected
for each retained private cell. This pointwise form makes compiled reads reduce
at their typed source witnesses. -/
def decodeState {Γ : SourceCtx Player L} (map : PublicationMap (R := R) Γ)
    (env : VEnv L (graphCtx (R := R) Γ)) : State L Γ :=
  fun _ cell h => match cell with
    | .publicData _ => env.get (fieldRef (R := R) h)
    | .privateData _ payload =>
        (BoundValue.resultEquiv _ |>.symm (R.valueEquiv payload
          (env.get (fieldRef (R := R) h))), (map h).get env)
    | .publication payload => R.valueEquiv payload (env.get (fieldRef (R := R) h))

@[simp] theorem decodeState_publicData {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ))
    {name payload} (h : HasVar Γ name (.publicData payload)) :
    (decodeState map env).get h = env.get (fieldRef (R := R) h) := rfl

@[simp] theorem decodeState_privateData {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ))
    {name owner payload} (h : HasVar Γ name (.privateData owner payload)) :
    (decodeState map env).get h =
      ((BoundValue.resultEquiv _).symm
        (R.valueEquiv payload (env.get (fieldRef (R := R) h))), (map h).get env) := rfl

@[simp] theorem decodeState_publication {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ))
    {name payload} (h : HasVar Γ name (.publication payload)) :
    (decodeState map env).get h =
      R.valueEquiv payload (env.get (fieldRef (R := R) h)) := rfl

theorem decodeState_resolve {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (unique : (Γ.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name published : VarId}
    (source : HasVar Γ name (.privateData owner payload))
    (result : PublicationResult (L.Val payload))
    (env : VEnv L (graphCtx (R := R) Γ)) :
    decodeState (resolveMap map unique source)
        (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env) =
      Env.cons result
        (updatePrivate (decodeState map env) source (resultPublication result)) := by
  funext readName cell read
  cases read with
  | here =>
      change (decodeState (resolveMap map unique source)
        (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)).get
          (.here) = result
      calc
        _ = _ :=
          decodeState_publication (name := published) (payload := payload) _ _ _
        _ = result := by simp [fieldRef]
  | there read =>
      cases cell with
      | publicData =>
          have different : readName ≠ name := by
            intro same
            subst readName
            have := HasVar.type_unique unique read source
            contradiction
          change (decodeState (resolveMap map unique source)
            (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)).get
              (.there read) = (updatePrivate (decodeState map env) source
                (resultPublication result)).get read
          rw [updatePrivate_get_of_name_ne _ _ _ read different]
          rfl
      | publication =>
          have different : readName ≠ name := by
            intro same
            subst readName
            have := HasVar.type_unique unique read source
            contradiction
          change (decodeState (resolveMap map unique source)
            (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)).get
              (.there read) = (updatePrivate (decodeState map env) source
                (resultPublication result)).get read
          rw [updatePrivate_get_of_name_ne _ _ _ read different]
          rfl
      | privateData readOwner readPayload =>
          by_cases same : readName = name
          · subst readName
            have cellEq := HasVar.type_unique unique read source
            cases cellEq
            have proofEq := HasVar.eq_of_nodup unique read source
            cases proofEq
            change (decodeState (resolveMap map unique source)
              (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)).get
                (.there source) = (updatePrivate (decodeState map env) source
                  (resultPublication result)).get source
            rw [updatePrivate_get_source]
            calc
              _ = _ :=
                decodeState_privateData (name := name) (owner := owner)
                  (payload := payload) (resolveMap map unique source)
                (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)
                (HasVar.there source)
              _ = _ := by
                simp [resolveMap, resultPublication, fieldRef, Graph.GuardRead.get]
                congr 1
                cases result <;> rfl
          · change (decodeState (resolveMap map unique source)
              (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)).get
                (.there read) = (updatePrivate (decodeState map env) source
                  (resultPublication result)).get read
            rw [updatePrivate_get_of_name_ne _ _ _ read same]
            calc
              _ = _ :=
                decodeState_privateData (name := readName) (owner := readOwner)
                  (payload := readPayload) (resolveMap map unique source)
                (VEnv.cons (x := published) ((R.valueEquiv payload).symm result) env)
                (HasVar.there read)
              _ = _ := by simp [resolveMap, same, fieldRef]

/-- Translate a source observation to its graph-layout observation. -/
def encodeObservation {who : Player} : {Γ : SourceCtx Player L} →
    SourceObservation L who Γ → Graph.Observation L who (graphCtx (R := R) Γ)
  | [], _ => ⟨Env.empty _⟩
  | (_, .publicData _) :: _, observation =>
      ⟨Env.cons (observation.cells.get .here)
        (encodeObservation (who := who)
          ⟨fun _ _ h => observation.cells.get (.there h)⟩).cells⟩
  | (_, .publication payload) :: _, observation =>
      ⟨Env.cons ((R.valueEquiv payload).symm (observation.cells.get .here))
        (encodeObservation (who := who)
          ⟨fun _ _ h => observation.cells.get (.there h)⟩).cells⟩
  | (_, .privateData _ payload) :: _, observation =>
      ⟨Env.cons ((observation.cells.get .here).map fun value =>
        (R.valueEquiv payload).symm (BoundValue.resultEquiv _ value.1))
        (encodeObservation (who := who)
          ⟨fun _ _ h => observation.cells.get (.there h)⟩).cells⟩

/-- Evaluate a guard read from a graph observation. Guard reads never inspect
sealed fields, so this needs no arbitrary reconstruction of hidden data. -/
def readObservation {who : Player} {Γ : VCtx Player L} {payload : L.Ty} :
    Graph.GuardRead (R := R) Γ payload → Graph.Observation L who Γ →
      Publication (L.Val payload)
  | .pending, _ => .pending
  | .publicData source, observation => .value (observation.cells.get source)
  | .publication source, observation =>
      match R.valueEquiv _ (observation.cells.get source) with
      | .failure => .failed
      | .success value => .value value

@[simp] theorem readObservation_observe [DecidableEq Player] {who : Player} {Γ : VCtx Player L}
    {payload : L.Ty} (read : Graph.GuardRead (R := R) Γ payload)
    (env : VEnv L Γ) :
    readObservation read (Graph.observe who env) = read.get env := by
  cases read <;> rfl

omit R in
@[simp] theorem observe_get_public [DecidableEq Player] {who : Player} {Γ : VCtx Player L}
    {name : VarId} {payload : L.Ty} (source : HasVar Γ name (.pub payload))
    (env : VEnv L Γ) :
    (Graph.observe who env).cells.get source = env.get source := rfl

omit R in
@[simp] theorem observe_get_sealed [DecidableEq Player] {who owner : Player} {Γ : VCtx Player L}
    {name : VarId} {payload : L.Ty} (source : HasVar Γ name (.sealed owner payload))
    (env : VEnv L Γ) :
    (Graph.observe who env).cells.get source =
      if owner = who then some (env.get source) else none := rfl

/-- Reconstruct a source-shaped observation using an explicit private-status
projection. Separating this irrelevant component makes the raw-view inverse
structural. -/
def decodeObservationWith {who : Player} {Γ : SourceCtx Player L}
    (status : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) → Publication (L.Val payload))
    (observation : Graph.Observation L who (graphCtx (R := R) Γ)) :
    SourceObservation L who Γ where
  cells := fun _ cell h => match cell with
    | .publicData _ => observation.cells.get (fieldRef (R := R) h)
    | .publication payload => R.valueEquiv payload
        (observation.cells.get (fieldRef (R := R) h))
    | .privateData _ payload =>
        (observation.cells.get (fieldRef (R := R) h)).map fun raw =>
          (BoundValue.resultEquiv _ |>.symm (R.valueEquiv payload raw),
            status h)

@[simp] theorem decodeObservationWith_publicData {who : Player}
    {Γ : SourceCtx Player L} (status : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) → Publication (L.Val payload))
    (view : Graph.Observation L who (graphCtx (R := R) Γ))
    {name payload} (h : HasVar Γ name (.publicData payload)) :
    (decodeObservationWith status view).cells.get h =
      view.cells.get (fieldRef (R := R) h) := rfl

@[simp] theorem decodeObservationWith_publication {who : Player}
    {Γ : SourceCtx Player L} (status : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) → Publication (L.Val payload))
    (view : Graph.Observation L who (graphCtx (R := R) Γ))
    {name payload} (h : HasVar Γ name (.publication payload)) :
    (decodeObservationWith status view).cells.get h =
      R.valueEquiv payload (view.cells.get (fieldRef (R := R) h)) := rfl

@[simp] theorem decodeObservationWith_privateData {who : Player}
    {Γ : SourceCtx Player L} (status : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) → Publication (L.Val payload))
    (view : Graph.Observation L who (graphCtx (R := R) Γ))
    {name owner payload} (h : HasVar Γ name (.privateData owner payload)) :
    (decodeObservationWith status view).cells.get h =
      (view.cells.get (fieldRef (R := R) h)).map fun raw =>
        ((BoundValue.resultEquiv _).symm (R.valueEquiv payload raw), status h) := rfl

/-- Reconstruct the source-shaped observation, using the publication map for
the status paired with an owner's visible private binding. -/
def decodeObservation {who : Player} {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ)
    (observation : Graph.Observation L who (graphCtx (R := R) Γ)) :
    SourceObservation L who Γ :=
  decodeObservationWith (fun h => readObservation (map h) observation) observation

theorem decode_observe [DecidableEq Player] {who : Player} {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ)
    (env : VEnv L (graphCtx (R := R) Γ)) :
    decodeObservation map (Graph.observe who env) =
      sourceObserve who (decodeState map env) := by
  apply congrArg (fun cells => SourceObservation.mk cells)
  funext name cell h
  cases cell with
  | publicData => rfl
  | publication => rfl
  | privateData owner payload =>
      change Option.map
        (fun raw => ((BoundValue.resultEquiv _).symm (R.valueEquiv payload raw),
          readObservation (map h) (Graph.observe who env)))
        ((Graph.observe who env).cells.get (fieldRef (R := R) h)) =
        if owner = who then
          some ((BoundValue.resultEquiv _).symm
            (R.valueEquiv payload (env.get (fieldRef (R := R) h))),
            (map h).get env)
        else none
      by_cases same : owner = who
      · rw [observe_get_sealed]
        simp [same]
      · rw [observe_get_sealed]
        simp [same]

theorem encode_decode_observation {who : Player} {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ)
    (observation : Graph.Observation L who (graphCtx (R := R) Γ)) :
    encodeObservation (decodeObservation map observation) = observation := by
  suffices inverse : ∀ {Γ : SourceCtx Player L}
      (status : ∀ {owner payload name},
        HasVar Γ name (.privateData owner payload) → Publication (L.Val payload))
      (view : Graph.Observation L who (graphCtx (R := R) Γ)),
      encodeObservation (decodeObservationWith status view) = view by
    exact inverse _ observation
  intro context status view
  induction context with
  | nil =>
      apply congrArg (fun cells => Graph.Observation.mk cells)
      funext name binding h
      nomatch h
  | cons entry tail ih =>
      obtain ⟨name, cell⟩ := entry
      let tailStatus : ∀ {owner payload readName},
          HasVar tail readName (.privateData owner payload) →
            Publication (L.Val payload) := fun h => status (.there h)
      cases cell with
      | publicData payload | publication payload | privateData owner payload =>
        let tailView : Graph.Observation L who (graphCtx (R := R) tail) :=
          ⟨fun _ _ h => view.cells.get (.there h)⟩
        have tailDecode :
            (⟨fun _ _ h => (decodeObservationWith status view).cells.get (.there h)⟩ :
              SourceObservation L who tail) =
              decodeObservationWith tailStatus tailView := by
          apply congrArg (fun cells => SourceObservation.mk cells)
          funext readName readCell h
          cases readCell <;> rfl
        have tailInverse := ih tailStatus tailView
        apply congrArg (fun cells => Graph.Observation.mk cells)
        funext readName binding h
        cases h with
        | here =>
            simp [decodeObservationWith, Env.get, Env.cons, fieldRef,
              Option.map_map, Function.comp_def]
        | there h =>
            change (encodeObservation
              (⟨fun _ _ h => (decodeObservationWith status view).cells.get (.there h)⟩ :
                SourceObservation L who tail)).cells.get h = tailView.cells.get h
            rw [tailDecode, tailInverse]

end Vegas.SourceProgram
