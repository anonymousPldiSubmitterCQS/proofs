From SegmentQueue.lib.blocking_pool
     Require Export outer_storage_interfaces.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.
Require Import SegmentQueue.lib.util.getAndSet.
From iris.heap_lang Require Import notation.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.

Open Scope nat.

Section impl.

Variable array_interface: infiniteArrayInterface.

Definition tryInsertQueue: val :=
  λ: "queue" "x",
    let: "insIterator" := Fst "queue" in
    let: "cellPtr" := Snd (iteratorStep array_interface "insIterator") in
    let: "cell" := derefCellPointer array_interface "cellPtr" in
    let: "box" := ref "x" in
    CAS "cell" NONE (SOME "box").

Definition tryRetrieveQueue: val :=
  λ: "queue",
    let: "retIterator" := Snd "queue" in
    let: "cellPtr" := Snd (iteratorStep array_interface "retIterator") in
    let: "cell" := derefCellPointer array_interface "cellPtr" in
    let: "box" := ref "x" in
    let: "old" := getAndSet "cell" (SOME #()) in
    if: "old" ≠ NONE then SOME (!"old") else NONE.

Definition newQueue: val :=
  λ: <>, let: "arr" := newInfiniteArray array_interface #2 in
        (newIterator ("arr" +ₗ #0) #0,
         newIterator ("arr" +ₗ #1) #0).

Definition queueOuterStorageImpl :=
  {|
   tryInsert := tryInsertQueue;
   tryRetrieve := tryRetrieveQueue;
   newStorage := newQueue;
  |}.

End impl.

From iris.algebra Require Import cmra auth list agree csum numbers gmap excl.
From iris.base_logic Require Import lib.invariants.
From iris.bi.lib Require Import fractional.
From SegmentQueue.lib.blocking_pool Require Export outer_storage_spec.

Section proof.

Context `{heapG Σ}.

Notation queue_element_algebra :=
  (agreeR (prodO (optionO valO) (optionO locO))).

Canonical Structure stackStateO := leibnizO stackState.

Notation algebra := (authUR (prodUR (gmapUR locO stack_element_algebra)
                                    (optionUR (exclR stackStateO))
                    )).

Instance algebra_discrete: ∀ (x: algebra), Discrete x.
Proof. apply _. Qed.

Class iStackG Σ := IStackG { iStack_inG :> inG Σ algebra }.
Definition iStackΣ : gFunctors := #[GFunctor algebra].
Instance subG_iStackΣ : subG iStackΣ Σ → iStackG Σ.
Proof. solve_inG. Qed.
Context `{iStackG Σ}.

Notation iProp := (iProp Σ).

Variable (N: namespace).

Definition has_contents γ (nodeℓ: loc) (value: option val) (tail: option loc)
  : iProp := own γ (◯ ({[ nodeℓ := to_agree (value, tail) ]}, None)).

Theorem has_contents_agrees γ ℓ value value' tail tail':
  has_contents γ ℓ value tail -∗ has_contents γ ℓ value' tail' -∗
               ⌜value = value' ∧ tail = tail'⌝.
Proof.
  iIntros "H◯1 H◯2". iDestruct (own_valid_2 with "H◯1 H◯2") as %HValid.
  iPureIntro. move: HValid. rewrite -auth_frag_op -pair_op singleton_op.
  rewrite auth_frag_valid pair_valid singleton_valid. case=> HPf _.
  apply agree_op_invL' in HPf. by case: HPf=> -> ->.
Qed.

Definition stack_state_ownership γ (state: stackState): iProp :=
  own γ (◯ (ε, Excl' state)).

Definition stack_as_outer_storage (state: stackState): outerStorageState :=
  match state with
  | StackEmpty => OuterStorageState 0 ∅
  | StackWithFailures p => OuterStorageState (length (nonEmptyToList p)) ∅
  | StackWithValues val =>
    OuterStorageState 0 (list_to_set_disj (snd <$> nonEmptyToList val))
  end.

Definition outer_storage_state γ (state: outerStorageState): iProp :=
  ∃ s, ⌜stack_as_outer_storage s = state⌝ ∧ stack_state_ownership γ s.

Fixpoint list_contains γ (values: list (loc * val))
  : iProp :=
  match values with
    nil => True
  | cons (ℓ, v) values' =>
    has_contents γ ℓ (Some v) (hd_error (fst <$> values'))
                 ∗ list_contains γ values'
  end.

Instance list_contains_persistent γ values :
  Persistent (list_contains γ values).
Proof. elim: values. apply _. move=> [? ?]. apply _. Qed.

Instance list_contains_timeless γ values :
  Timeless (list_contains γ values).
Proof. elim: values. apply _. move=> [? ?]. apply _. Qed.

Fixpoint list_failures γ (values: list loc) : iProp :=
  match values with
    nil => True
  | cons ℓ values' =>
    has_contents γ ℓ None (hd_error values') ∗ list_failures γ values'
  end.

Instance list_failures_persistent γ values :
  Persistent (list_failures γ values).
Proof. elim: values; apply _. Qed.

Instance list_failures_timeless γ values :
  Timeless (list_failures γ values).
Proof. elim: values; apply _. Qed.

Definition stack_top_value' (state: stackState): option loc :=
  match state with
  | StackEmpty => None
  | StackWithValues ct => Some (fst (hdNonEmpty ct))
  | StackWithFailures ct => Some (hdNonEmpty ct)
  end.

Definition list_state γ (state: stackState): iProp :=
  match state with
  | StackEmpty => True
  | StackWithValues ct => list_contains γ (nonEmptyToList ct)
  | StackWithFailures ct => list_failures γ (nonEmptyToList ct)
  end.

Instance list_state_timeless γ state: Timeless (list_state γ state).
Proof. by case: state; apply _. Qed.

Instance list_state_persistent γ state: Persistent (list_state γ state).
Proof. by case: state; apply _. Qed.

Definition heap_to_ra (heap: gmap loc (option val * option loc)):
  gmapUR locO stack_element_algebra :=
  to_agree <$> heap.

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

Definition loc_to_value (v: option loc): val :=
  option_to_value ((fun x => LitV (LitLoc x)) <$> v).

Theorem loc_to_value_inj:
  FinFun.Injective loc_to_value.
Proof.
  intros a b HInj. apply option_to_value_inj in HInj. move: HInj.
  case: a; case: b=> //=. move=> a b. case. by intros ->.
Qed.

Definition stack_top_value (state: stackState): val :=
  loc_to_value (stack_top_value' state).

Definition heap_value (ℓ: loc) (c: option val * option loc): iProp :=
  ℓ ↦ (option_to_value (fst c), loc_to_value (snd c)).

Definition heap_values (heap: gmap loc (option val * option loc)): iProp :=
  [∗ map] ℓ ↦ c ∈ heap, heap_value ℓ c.

Definition stack_invariant γ topℓ: iProp :=
  ∃ heap (state: stackState),
    own γ (● (heap_to_ra heap, Excl' state))
        ∗ heap_values heap
        ∗ topℓ ↦ stack_top_value state ∗ list_state γ state.

Definition is_stack γ v: iProp :=
  ∃ (topℓ: loc), ⌜v = #topℓ⌝ ∧ inv N (stack_invariant γ topℓ).

Global Instance is_stack_persistent γ v: Persistent (is_stack γ v).
Proof. apply _. Qed.

Lemma stack_top_value_inj γ a b:
  ⌜stack_top_value a = stack_top_value b⌝ -∗
    list_state γ a -∗ list_state γ b -∗
    ⌜a = b⌝.
Proof.
  iIntros (HTopValue) "H1 H2".
  apply loc_to_value_inj in HTopValue. move: HTopValue.
  rewrite /stack_top_value'.
  case: a; case: b=> //=; move=> a' b'; case.
  all: case: a'=> x xs; case: b'=> y ys=> /=.
  - case: y; case: x=> /=. move=> a1 a2 b1 b2 Heq. subst.
    iInduction (xs) as [|x xs] "IH" forall (a1 a2 b2 ys).
    * iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
      iDestruct (has_contents_agrees with "H1h H2h") as %[H1 H2].
      move: H1 H2=> /=. case: ys=> /=; last done.
      by case=> ->.
    * iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
      iDestruct (has_contents_agrees with "H1h H2h") as %[H1 H2].
      move: H1 H2=> /=. case: ys=> /=; first done. move=> y ys.
      case=> HEq; subst. case: y; case: x=> a b c d. case=> HEq; subst.
      simpl.
      iDestruct ("IH" with "H1t H2t") as %HOk. move: HOk. case=> ? ?.
      by subst.
  - case: y=> /= a1 a2 HEq. subst.
    iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
    iDestruct (has_contents_agrees with "H1h H2h") as %[H1 H2].
    done.
  - case: x=> /= a1 a2 HEq. subst.
    iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
    iDestruct (has_contents_agrees with "H1h H2h") as %[H1 H2].
    done.
  - move=> HEq. subst.
    iInduction (xs) as [|x' xs] "IH" forall (x ys).
    * iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
      iDestruct (has_contents_agrees with "H1h H2h") as %[H1 H2].
      move: H1 H2=> /=. case: ys=> //=.
    * iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
      iDestruct (has_contents_agrees with "H1h H2h") as %[H1 H2].
      move: H1 H2=> /=. case: ys=> /=; first done. move=> y ys _.
      case=> HEq; subst.
      iDestruct ("IH" with "H1t H2t") as %HOk. move: HOk. case=> ?.
      by subst.
Qed.

Theorem update_stack_state state γ topℓ storageState state':
  list_state γ state -∗
  list_state γ state' -∗
  stack_invariant γ topℓ -∗
  outer_storage_state γ storageState ==∗
  (⌜storageState = stack_as_outer_storage state⌝ ∧
    topℓ ↦ stack_top_value state ∗
        (topℓ ↦ stack_top_value state' -∗ stack_invariant γ topℓ)
        ∗ outer_storage_state γ (stack_as_outer_storage state') ∨
   ∃ state'', ⌜state'' ≠ state⌝ ∧ list_state γ state'' ∗
        topℓ ↦ stack_top_value state'' ∗
        (topℓ ↦ stack_top_value state'' -∗ stack_invariant γ topℓ)
        ∗ outer_storage_state γ storageState).
Proof.
  iIntros "#HList #HList' HInv H◯".
  iDestruct "HInv" as (heap currentState) "(H● & HHeap & Htopℓ & #HList'')".
  iDestruct "H◯" as (currentState' <-) "H◯".
  destruct (decide (stack_top_value currentState = stack_top_value state))
    as [eq|neq].
  - iDestruct (stack_top_value_inj with "[%] [#] [#]") as %HEq; try done.
    subst.
    iLeft. iFrame "Htopℓ".
    iDestruct (own_valid_2 with "H● H◯")
      as %[[_ HValid%Excl_included]%prod_included _]%auth_both_valid.
    apply leibniz_equiv in HValid. subst.
    iSplitR; first done.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]".
    2: {
      iModIntro. iSplitR "H◯".
      - iIntros "Htopℓ". iExists heap, _. by iFrame.
      - iExists state'. by iFrame.
    }
    apply auth_update, prod_local_update_2.
    apply option_local_update.
    by apply exclusive_local_update.
  - iRight. iExists currentState. iFrame "Htopℓ HList''".
    iSplitR.
    { iPureIntro. intros heq. subst. done. }
    iSplitR "H◯"; last by iExists _; iFrame.
    iModIntro. iIntros "Htopℓ". iExists _, _. by iFrame.
Qed.

Theorem register_heap_value (v: option val) (ℓ': option loc) γ ℓ heap state:
  ℓ ↦ (option_to_value v,
       option_to_value ((fun x => LitV (LitLoc x)) <$> ℓ'))
    -∗ own γ (● (heap_to_ra heap, state))
    -∗ heap_values heap
    ==∗
    ∃ heap', own γ (● (heap_to_ra heap', state)) ∗ heap_values heap' ∗
    has_contents γ ℓ v ℓ'.
Proof.
  iIntros "Hℓ H● HHeap". rewrite /heap_values /heap_value.
  iAssert (⌜heap !! ℓ = None⌝)%I as %HNone.
  {
    destruct (heap !! ℓ) eqn:E; last done. iExFalso.
    iDestruct (big_sepM_lookup with "HHeap") as "HContra"; first done.
    by iDestruct (mapsto_valid_2 with "Hℓ HContra") as %[].
  }
  remember (<[ℓ := (v, ℓ')]> heap) as heap'.
  iAssert ([∗ map] ℓ ↦ c ∈ heap', heap_value ℓ c)%I
    with "[Hℓ HHeap]" as "HHeap'".
  { subst. rewrite big_sepM_insert; last done. iFrame. }
  iMod (own_update with "H●") as "[H● H◯]".
  2: { iFrame "H◯". iExists heap'. by iFrame. }
  subst. rewrite /heap_to_ra -map_fmap_singleton fmap_insert.
  rewrite map_fmap_singleton.
  apply auth_update_alloc, prod_local_update_1.
  apply alloc_singleton_local_update.
  by rewrite lookup_fmap HNone.
  done.
Qed.

Theorem hasContents_load γ ℓ topℓ (x: option val) (y: option loc):
  {{{ inv N (stack_invariant γ topℓ) ∗ has_contents γ ℓ x y }}}
    ! #ℓ
  {{{ RET (option_to_value x, loc_to_value y); True }}}.
Proof.
  iIntros (Φ) "[#HInv #H◯] HΦ". iInv N as ">HOpen".
  iDestruct "HOpen" as (heap state) "(H● & HHeap & HRest)".
  rewrite /heap_values.
  iDestruct (own_valid_2 with "H● H◯")
    as %[[HValid%singleton_included_l _]%prod_included
                                        HAuthValid]%auth_both_valid.
  simpl in *. destruct HValid as (e & HLookup & HInc).
  move: HInc. rewrite Some_included. move=> HAgree.
  move: HAuthValid. case=> /= heapValid _.
  assert (heap_to_ra heap !! ℓ ≡ Some (to_agree (x, y))) as HLookup'.
  {
    case: HAgree.
    - move=> HAg; move: HLookup. by rewrite -HAg.
    - destruct (to_agree_uninj e) as [HH HH1].
      {
        eapply lookup_valid_Some. 2: apply HLookup. done.
      }
      rewrite HLookup. rewrite -HH1. clear. case: HH=> x' y'.
      rewrite to_agree_included. case=> /= -> -> //.
  }
  clear HLookup HAgree.
  rewrite lookup_fmap in HLookup'.
  destruct (decide (heap !! ℓ = Some (x, y))) as [eq|neq].
  2: {
    exfalso. destruct (heap !! ℓ) as [[a b]|] eqn:Z.
    2: rewrite Z in HLookup'; inversion HLookup'.
    rewrite Z in HLookup'. simpl in HLookup'.
    apply Some_equiv_inj in HLookup'.
    apply to_agree_inj in HLookup'. case: HLookup'. simpl.
    move=> A B. move: neq.
    apply leibniz_equiv in A. apply leibniz_equiv in B. by subst.
  }
  iDestruct (big_sepM_lookup_acc with "HHeap") as "[HEl HRestore]";
    first done.
  wp_load.
  iSpecialize ("HRestore" with "HEl"). iModIntro.
  iSpecialize ("HΦ" with "[$]"). iFrame.
  iExists _, _. iFrame.
Qed.

Theorem tryInsertStack_spec γ stack (value : val):
  is_stack γ stack -∗
  <<< ∀ state, ▷ outer_storage_state γ state >>>
      tryInsert stackOuterStorageImpl stack value @ ⊤∖↑N
        <<< ∃ (b: bool),
                if b then
                  outer_storage_state γ (insertionAddsValue state value)
                else match insertionRemovesFailure state with
                       None => False
                     | Some state' => outer_storage_state γ state'
                     end, RET #b >>>.
Proof.
  iIntros "#HIsStack" (Φ) "AU". iDestruct "HIsStack" as (topℓ ->) "HInv".
  wp_lam. wp_pures. iLöb as "IH". wp_bind (!#topℓ)%E.
  iInv N as ">HOpen" "HClose".
  iDestruct "HOpen" as (heap1 state1) "(H● & HHeap & Htopℓ & #HList)".
  wp_load.
  iMod ("HClose" with "[H● HHeap Htopℓ]") as "_".
  { iExists _, _. by iFrame. }
  iModIntro. wp_pures. wp_alloc node as "HNode". iApply fupd_wp.
  iInv N as ">HOpen" "HClose".
  iDestruct "HOpen" as (heap2 state2) "(H● & HHeap & Htopℓ & HList')".
  iMod (register_heap_value (Some value) with "HNode H● HHeap")
    as (?) "(H● & HHeap & #HNode)".
  iMod ("HClose" with "[Htopℓ HList' H● HHeap]") as "_".
  by iExists _, _; iFrame.
  iModIntro. wp_pures.
  destruct state1 as [|[[loc stored] values]|[failure failures]].
  - wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">HOpen" "HClose".
    iMod "AU" as (outerState) "[>outerState HAuClose]".
    iAssert (list_state γ (StackWithValues (NonEmpty _ (node, value) [])))
      with "[#]" as "HList'".
    by simpl; iFrame "HNode".
    iMod (update_stack_state with "HList HList' HOpen outerState")
      as "[(% & Htopℓ & HRestore & outerState)|H]".
    * subst. wp_cmpxchg_suc.
      iDestruct "HAuClose" as "[_ HAuClose]".
      iMod ("HAuClose" with "[outerState]") as "HΦ".
      2: {
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. by wp_pures.
      }
      simpl. iFrame.
    * iDestruct "H"
        as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
      iAssert (⌜stack_top_value StackEmpty = stack_top_value state''⌝ -∗ False)%I
        with "[#]" as %HNe.
      {
        iIntros (HTop).
        by iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
      }
      wp_cmpxchg_fail.
      iDestruct "HAuClose" as "[HAuClose _]".
      iMod ("HAuClose" with "outerStorage") as "AU".
      iModIntro.
      iMod ("HClose" with "[Htopℓ HRestore]") as "_".
      by iSpecialize ("HRestore" with "Htopℓ").
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
  - wp_pures. wp_apply hasContents_load. simpl.
    { iFrame "HInv". iDestruct "HList" as "[$ _]". }
    iIntros "_".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">HOpen" "HClose".
    iMod "AU" as (outerState) "[>outerState HAuClose]".
    iAssert (list_state γ (StackWithValues (NonEmpty _ (node, value)
            ((loc, stored)::values))))
      with "[#]" as "HList'".
    by simpl; iFrame "HNode".
    iMod (update_stack_state with "HList HList' HOpen outerState")
      as "[(% & Htopℓ & HRestore & outerState)|H]".
    * simpl. subst. wp_cmpxchg_suc.
      iDestruct "HAuClose" as "[_ HAuClose]".
      iMod ("HAuClose" with "[outerState]") as "HΦ".
      2: {
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. by wp_pures.
      }
      iFrame.
    * iDestruct "H"
        as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
      iAssert (⌜stack_top_value _ = stack_top_value state''⌝ -∗ False)%I
        with "[#]" as %HNe.
      {
        iIntros (HTop).
        iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
        apply HTop. iApply "HList". iApply "HList''". done.
      }
      wp_cmpxchg_fail.
      iDestruct "HAuClose" as "[HAuClose _]".
      iMod ("HAuClose" with "outerStorage") as "AU".
      iModIntro.
      iMod ("HClose" with "[Htopℓ HRestore]") as "_".
      by iSpecialize ("HRestore" with "Htopℓ").
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
  - wp_pures. wp_apply hasContents_load.
    { simpl. iFrame "HInv". iDestruct "HList" as "[$ _]". }
    iIntros "_".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">HOpen" "HClose".
    iMod "AU" as (outerState) "[>outerState HAuClose]".
    destruct failures as [|failure' failures].
    + iAssert (list_state γ StackEmpty) with "[$]" as "HList'".
      iMod (update_stack_state with "HList HList' HOpen outerState")
        as "[(% & Htopℓ & HRestore & outerState)|H]".
      * subst. wp_cmpxchg_suc.
        iDestruct "HAuClose" as "[_ HAuClose]".
        iMod ("HAuClose" with "[outerState]") as "HΦ".
        2: {
          iModIntro.
          iMod ("HClose" with "[Htopℓ HRestore]") as "_".
          by iSpecialize ("HRestore" with "Htopℓ").
          iModIntro. by wp_pures.
        }
        iFrame.
      * iDestruct "H"
          as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
        iAssert (⌜stack_top_value _ = stack_top_value state''⌝ -∗ False)%I
          with "[#]" as %HNe.
        {
          iIntros (HTop).
          iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
          apply HTop. iApply "HList". iApply "HList''". done.
        }
        wp_cmpxchg_fail.
        iDestruct "HAuClose" as "[HAuClose _]".
        iMod ("HAuClose" with "outerStorage") as "AU".
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. wp_pures. wp_lam. wp_pures.
        by iApply "IH".
    + iAssert (list_state γ (StackWithFailures (NonEmpty _ failure' failures)))
        with "[#]" as "HList'".
      { simpl. iDestruct "HList" as "[_ $]". }
      iMod (update_stack_state with "HList HList' HOpen outerState")
        as "[(% & Htopℓ & HRestore & outerState)|H]".
      * subst. wp_cmpxchg_suc.
        iDestruct "HAuClose" as "[_ HAuClose]".
        iMod ("HAuClose" with "[outerState]") as "HΦ".
        2: {
          iModIntro.
          iMod ("HClose" with "[Htopℓ HRestore]") as "_".
          by iSpecialize ("HRestore" with "Htopℓ").
          iModIntro. by wp_pures.
        }
        iFrame.
      * iDestruct "H"
          as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
        iAssert (⌜stack_top_value _ = stack_top_value state''⌝ -∗ False)%I
          with "[#]" as %HNe.
        {
          iIntros (HTop).
          iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
          apply HTop. iApply "HList". iApply "HList''". done.
        }
        wp_cmpxchg_fail.
        iDestruct "HAuClose" as "[HAuClose _]".
        iMod ("HAuClose" with "outerStorage") as "AU".
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. wp_pures. wp_lam. wp_pures.
        by iApply "IH".
Qed.

Section XX.
Context `{Countable A}.
Implicit Types x y : A.
Implicit Types X Y : gmultiset A.
Lemma gmultiset_difference_disj_union X Y : Y = (X ⊎ Y) ∖ X.
Proof.
  apply gmultiset_eq. move=> x.
  rewrite multiplicity_difference multiplicity_disj_union. lia.
Qed.
End XX.

Theorem tryRetrieveStack_spec γ stack:
  is_stack γ stack -∗
  <<< ∀ state, ▷ outer_storage_state γ state >>>
      tryRetrieve stackOuterStorageImpl stack @ ⊤∖↑N
  <<< ∃ (v : option val),
          match v with
            | Some v' => match retrievalRemovesValue state v' with
                          | None => False
                          | Some state' => outer_storage_state γ state'
                        end
            | None => outer_storage_state γ (retrievalAddsFailure state)
          end, RET option_to_value v >>>.
Proof.
  iIntros "#HIsStack" (Φ) "AU". iDestruct "HIsStack" as (topℓ ->) "HInv".
  wp_lam. wp_pures. iLöb as "IH". wp_bind (!#topℓ)%E.
  iInv N as ">HOpen" "HClose".
  iDestruct "HOpen" as (heap1 state1) "(H● & HHeap & Htopℓ & #HList)".
  wp_load.
  iMod ("HClose" with "[H● HHeap Htopℓ]") as "_".
  { iExists _, _. by iFrame. }
  iModIntro. wp_pures. wp_alloc node as "HNode". iApply fupd_wp.
  iInv N as ">HOpen" "HClose".
  iDestruct "HOpen" as (heap2 state2) "(H● & HHeap & Htopℓ & HList')".
  iMod (register_heap_value None with "HNode H● HHeap")
    as (?) "(H● & HHeap & #HNode)".
  iMod ("HClose" with "[Htopℓ HList' H● HHeap]") as "_".
  by iExists _, _; iFrame.
  iModIntro. wp_pures.
  destruct state1 as [|[[loc stored] values]|[failure failures]].
  - wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">HOpen" "HClose".
    iMod "AU" as (outerState) "[>outerState HAuClose]".
    iAssert (list_state γ (StackWithFailures (NonEmpty _ node [])))
      with "[#]" as "HList'".
    by simpl; iFrame "HNode".
    iMod (update_stack_state with "HList HList' HOpen outerState")
      as "[(% & Htopℓ & HRestore & outerState)|H]".
    * subst. wp_cmpxchg_suc.
      iDestruct "HAuClose" as "[_ HAuClose]".
      iMod ("HAuClose" $! None with "[outerState]") as "HΦ".
      2: {
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. by wp_pures.
      }
      iFrame.
    * iDestruct "H"
        as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
      iAssert (⌜stack_top_value StackEmpty = stack_top_value state''⌝ -∗ False)%I
        with "[#]" as %HNe.
      {
        iIntros (HTop).
        by iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
      }
      wp_cmpxchg_fail.
      iDestruct "HAuClose" as "[HAuClose _]".
      iMod ("HAuClose" with "outerStorage") as "AU".
      iModIntro.
      iMod ("HClose" with "[Htopℓ HRestore]") as "_".
      by iSpecialize ("HRestore" with "Htopℓ").
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
  - wp_pures. wp_apply hasContents_load.
    { simpl. iFrame "HInv". iDestruct "HList" as "[$ _]". }
    iIntros "_".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">HOpen" "HClose".
    iMod "AU" as (outerState) "[>outerState HAuClose]".
    destruct values as [|value' values].
    + iAssert (list_state γ StackEmpty) with "[$]" as "HList'".
      iMod (update_stack_state with "HList HList' HOpen outerState")
        as "[(% & Htopℓ & HRestore & outerState)|H]".
      * subst. wp_cmpxchg_suc.
        iDestruct "HAuClose" as "[_ HAuClose]".
        iMod ("HAuClose" $! (Some stored) with "[outerState]") as "HΦ".
        2: {
          iModIntro.
          iMod ("HClose" with "[Htopℓ HRestore]") as "_".
          by iSpecialize ("HRestore" with "Htopℓ").
          iModIntro. by wp_pures.
        }
        rewrite /retrievalRemovesValue. simpl.
        rewrite gmultiset_disj_union_right_id.
        rewrite multiplicity_singleton.
        rewrite gmultiset_difference_diag.
        iFrame.
      * iDestruct "H"
          as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
        iAssert (⌜stack_top_value _ = stack_top_value state''⌝ -∗ False)%I
          with "[#]" as %HNe.
        {
          iIntros (HTop).
          iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
          apply HTop. iApply "HList". iApply "HList''". done.
        }
        wp_cmpxchg_fail.
        iDestruct "HAuClose" as "[HAuClose _]".
        iMod ("HAuClose" with "outerStorage") as "AU".
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. wp_pures. wp_lam. wp_pures.
        by iApply "IH".
    + iAssert (list_state γ (StackWithValues (NonEmpty _ value' values)))
        with "[#]" as "HList'".
      { simpl. iDestruct "HList" as "[_ $]". }
      iMod (update_stack_state with "HList HList' HOpen outerState")
        as "[(% & Htopℓ & HRestore & outerState)|H]".
      * subst. wp_cmpxchg_suc.
        iDestruct "HAuClose" as "[_ HAuClose]".
        iMod ("HAuClose" $! (Some stored) with "[outerState]") as "HΦ".
        2: {
          iModIntro.
          iMod ("HClose" with "[Htopℓ HRestore]") as "_".
          by iSpecialize ("HRestore" with "Htopℓ").
          iModIntro. by wp_pures.
        }
        iFrame.
        rewrite /retrievalRemovesValue. simpl.
        rewrite multiplicity_disj_union multiplicity_singleton /=.
        rewrite -gmultiset_difference_disj_union. iFrame.
      * iDestruct "H"
          as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
        iAssert (⌜stack_top_value _ = stack_top_value state''⌝ -∗ False)%I
          with "[#]" as %HNe.
        {
          iIntros (HTop).
          iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
          apply HTop. iApply "HList". iApply "HList''". done.
        }
        wp_cmpxchg_fail.
        iDestruct "HAuClose" as "[HAuClose _]".
        iMod ("HAuClose" with "outerStorage") as "AU".
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. wp_pures. wp_lam. wp_pures.
        by iApply "IH".
  - wp_pures. wp_apply hasContents_load. simpl.
    { iFrame "HInv". iDestruct "HList" as "[$ _]". }
    iIntros "_".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">HOpen" "HClose".
    iMod "AU" as (outerState) "[>outerState HAuClose]".
    iAssert (list_state γ (StackWithFailures (NonEmpty _ node
            (failure::failures))))
      with "[#]" as "HList'".
    by simpl; iFrame "HNode".
    iMod (update_stack_state with "HList HList' HOpen outerState")
      as "[(% & Htopℓ & HRestore & outerState)|H]".
    * simpl. subst. wp_cmpxchg_suc.
      iDestruct "HAuClose" as "[_ HAuClose]".
      iMod ("HAuClose" $! None with "[outerState]") as "HΦ".
      2: {
        iModIntro.
        iMod ("HClose" with "[Htopℓ HRestore]") as "_".
        by iSpecialize ("HRestore" with "Htopℓ").
        iModIntro. by wp_pures.
      }
      iFrame.
    * iDestruct "H"
        as (state'') "(% & #HList'' & Htopℓ & HRestore & outerStorage)".
      iAssert (⌜stack_top_value _ = stack_top_value state''⌝ -∗ False)%I
        with "[#]" as %HNe.
      {
        iIntros (HTop).
        iDestruct (stack_top_value_inj with "[%] [] []") as %HContra.
        apply HTop. iApply "HList". iApply "HList''". done.
      }
      wp_cmpxchg_fail.
      iDestruct "HAuClose" as "[HAuClose _]".
      iMod ("HAuClose" with "outerStorage") as "AU".
      iModIntro.
      iMod ("HClose" with "[Htopℓ HRestore]") as "_".
      by iSpecialize ("HRestore" with "Htopℓ").
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
Qed.

Theorem newStack_spec:
  {{{ True }}}
    newStorage stackOuterStorageImpl #()
  {{{ γ v, RET v; is_stack γ v ∗
                  outer_storage_state γ (OuterStorageState 0 ∅) }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam. rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ".
  iMod (own_alloc (● (ε, Excl' StackEmpty) ⋅ ◯ (ε, Excl' StackEmpty)))
    as (γ) "[H● H◯]".
  by apply auth_both_valid.
  iMod (inv_alloc N _ (stack_invariant γ ℓ) with "[Hℓ H●]") as "HInv".
  { iExists ∅, StackEmpty. rewrite /heap_to_ra fmap_empty. iFrame.
    rewrite /heap_values. by iApply big_sepM_empty.
  }
  iApply "HΦ". iSplitL "HInv".
  - iExists _. by iFrame.
  - iExists _. by iFrame.
Qed.

End proof.

Canonical Structure stack_outerStorage `{!heapG Σ} `{!iStackG Σ}:
  outerStorageSpec Σ stackOuterStorageImpl :=
  {|
    is_outer_storage := is_stack;
    outer_storage_contents := outer_storage_state;
    tryInsert_spec := tryInsertStack_spec;
    tryRetrieve_spec := tryRetrieveStack_spec;
    newStorage_spec := newStack_spec;
  |}.
