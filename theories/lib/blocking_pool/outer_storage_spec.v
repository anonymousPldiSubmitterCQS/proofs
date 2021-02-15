From SegmentQueue.lib.blocking_pool
     Require Export outer_storage_interfaces.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.

Definition option_to_value (v: option val): val :=
  match v with
    None => NONEV
  | Some v => SOMEV v
  end.

Theorem option_to_value_inj:
  FinFun.Injective option_to_value.
Proof.
  intros a b. rewrite /option_to_value.
  case: a; case: b=> //=.
  move=> a b. case. by intros ->.
Qed.

Inductive outerStorageState :=
  OuterStorageState {
      failuresInStorage: nat;
      valuesInStorage: gmultiset val
    }.

Definition insertionAddsValue (state: outerStorageState) (v: val) :=
  match state with
    OuterStorageState fs vs => OuterStorageState fs ({[v]} ⊎ vs)
  end.

Definition insertionRemovesFailure (state: outerStorageState) :=
  match state with
    OuterStorageState fs vs => match fs with
                                0 => None
                              | S fs => Some (OuterStorageState fs vs)
                              end
  end.

Definition retrievalAddsFailure (state: outerStorageState) :=
  match state with
    OuterStorageState fs vs => OuterStorageState (S fs) vs
  end.

Locate multiplicity.

Definition retrievalRemovesValue (state: outerStorageState) (value: val) :=
  match state with
    OuterStorageState fs vs =>
    match multiplicity value vs with
      0 => None
    | _ => Some (OuterStorageState fs (vs ∖ {[value]}))
    end
  end.

Record outerStorageSpec Σ `{!heapG Σ} (impl: outerStorageInterface) :=
  OuterStorageSpec {
      is_outer_storage:
        namespace -> gname -> val -> iProp Σ;
      is_outer_storage_persistent N γ s:
        Persistent (is_outer_storage N γ s);
      outer_storage_contents:
        gname -> outerStorageState -> iProp Σ;
      tryInsert_spec N γ s (value : val):
        is_outer_storage N γ s -∗
        <<< ∀ state, ▷ outer_storage_contents γ state >>>
            tryInsert impl s value @ ⊤∖↑N
        <<< ∃ (b: bool),
                if b then
                  outer_storage_contents γ (insertionAddsValue state value)
                else match insertionRemovesFailure state with
                       None => False
                     | Some state' => outer_storage_contents γ state'
                     end, RET #b >>>;
      tryRetrieve_spec N γ s:
         is_outer_storage N γ s -∗
         <<< ∀ state, ▷ outer_storage_contents γ state >>>
              tryRetrieve impl s @ ⊤ ∖ ↑N
         <<< ∃ (v : option val),
                 match v with
                   | Some v' => match retrievalRemovesValue state v' with
                                 | None => False
                                 | Some state' => outer_storage_contents γ state'
                               end
                   | None => outer_storage_contents γ (retrievalAddsFailure state)
                 end, RET option_to_value v >>>;
      newStorage_spec N:
         {{{ True }}}
           newStorage impl #()
         {{{ γ v, RET v; is_outer_storage N γ v
                 ∗ outer_storage_contents γ
                     {| failuresInStorage := 0; valuesInStorage := ∅ |} }}}
      }.

Existing Instances is_outer_storage_persistent.
