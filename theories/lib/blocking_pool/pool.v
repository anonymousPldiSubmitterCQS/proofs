Require Import SegmentQueue.lib.thread_queue.thread_queue.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.
From SegmentQueue.lib.blocking_pool Require Import outer_storage_interfaces.
Require Import SegmentQueue.lib.util.future.
From iris.heap_lang Require Import notation.

Section impl.

Variable array_interface: infiniteArrayInterface.

Variable storage_interface: outerStorageInterface.

Definition newPool: val :=
  λ: <>, ((ref #0, newStorage storage_interface #()),
           newThreadQueue array_interface #()).

Definition takePool: val :=
  rec: "loop" "pool" :=
    let: "availablePermits" := Fst (Fst ("pool")) in
    let: "storage" := Snd (Fst ("pool")) in
    let: "e" := Fst (Snd ("pool")) in
    let: "p" := FAA "availablePermits" #(-1) in
    if: #0 < "p" then
      match: tryRetrieve storage_interface "storage" with
        NONE => "loop" "pool"
      | SOME "v" => fillThreadQueueFuture "v"
      end
    else match: suspend array_interface "e" with
           InjR "v" => "v"
         | InjL "x" => "undefined"
         end.

Definition resumePool: val :=
  λ: "d", resume array_interface #(Z.of_nat 300) #true #false #false "d".

Definition putPool: val :=
  rec: "loop" "pool" "value" :=
    let: "availablePermits" := Fst (Fst ("pool")) in
    let: "storage" := Snd (Fst ("pool")) in
    let: "d" := Snd (Snd ("pool")) in
    let: "p" := FAA "availablePermits" #1 in
    let: "completeRefused" :=
       λ: "value'", if: tryInsert storage_interface "storage" "value'"
                    then #()
                    else "loop" "pool" "value"
    in if: #0 ≤ "p" then
         if: tryInsert storage_interface "storage" "value"
         then #()
         else "loop" "pool" "value"
       else resumePool "d" "completeRefused" "value" ;; #().

Definition cancelPoolFuture : val :=
  λ: "pool" "f",
  let: "availablePermits" := Fst (Fst ("pool")) in
  let: "storage" := Snd (Fst ("pool")) in
  let: "d" := Snd (Snd ("pool")) in
  tryCancelThreadQueueFuture'
    array_interface
    #false
    #(Z.of_nat 300)
    #false
    #false
    "d"
    (λ: <>, FAA "availablePermits" #1 < #0)
    (λ: "value'", if: tryInsert storage_interface "storage" "value'"
                  then #()
                  else putPool "pool" "value'")
    (λ: <>, putPool "pool" "value'")
    "f".

End impl.

From SegmentQueue.util Require Import everything big_opL.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth numbers list gset excl csum.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

From SegmentQueue.lib.blocking_pool Require Import outer_storage_spec.

Section proof.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ}.

Notation algebra := (authUR (prodUR natUR natUR)).

Class iPoolG Σ := IPoolG { iPool_inG :> inG Σ algebra }.
Definition iPoolΣ : gFunctors := #[GFunctor algebra].
Instance subG_iPoolΣ : subG iPoolΣ Σ → iPoolG Σ.
Proof. solve_inG. Qed.
Context `{iPoolG Σ}.

Variable (N NFuture: namespace).
Variable (HNDisj: N ## NFuture).
Let NPool := N .@ "Pool".
Let NStorage := N .@ "Storage".
Let NTq := N .@ "Tq".
Notation iProp := (iProp Σ).

Definition insertion_permit γinner := own γinner (◯ (1, 0)).

Definition retrieval_permit γinner := own γinner (◯ (0, 1)).

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Variable storage_interface: outerStorageInterface.
Variable storage_spec: outerStorageSpec _ storage_interface.

Definition pool_inv (U: base_lit -> iProp)
           (γinner γst γtq: gname) (p: loc) : iProp :=
  ∃ (elems: list base_lit) (failures: nat) (ki kr: nat),
    ⌜failures + kr ≤ length elems + ki⌝ ∧
    (([∗ list] e ∈ elems, U e ∧ ⌜lit_is_unboxed e⌝ ∧ ⌜Laterable (U e)⌝) ∗
     outer_storage_contents _ _ storage_spec γst
       (OuterStorageState failures (list_to_set_disj (LitV <$> elems)))
    ) ∗ own γinner (● (ki, kr)) ∗
    ∃ enqueuedThreads, thread_queue_state γtq enqueuedThreads ∗
    p ↦ #((length elems - failures)%Z - enqueuedThreads + ki - kr) ∗
    ⌜(length elems + ki = failures + kr)%nat ∨ enqueuedThreads = 0⌝.

Let tqParams γ U :=
  @ThreadQueueParameters
    Σ
    false
    True
    True
    (insertion_permit γ)
    (fun x => U x ∧ ⌜lit_is_unboxed x⌝ ∧ ⌜Laterable (U x)⌝)%I
    False.

Let isThreadQueue γ U :=
  is_thread_queue NTq NFuture (tqParams γ U) _ array_spec.

Definition is_pool_future γ U :=
  is_thread_queue_future NTq NFuture (tqParams γ U) _ array_spec.

Definition is_pool U γ γst γa γtq γe γd (pool: val): iProp :=
  ∃ e d s (p: loc), ⌜pool = ((#p, s), (e, d))%V⌝ ∧
  is_outer_storage _ _ storage_spec NStorage γst s ∗
  inv NPool (pool_inv U γ γst γtq p) ∗ isThreadQueue γ U γa γtq γe γd e d.

Theorem putPool_spec U γ γst γa γtq γe γd pool (x: base_lit):
  Laterable (U x) -> lit_is_unboxed x ->
  {{{ is_pool U γ γst γa γtq γe γd pool ∗ U x }}}
    putPool array_interface storage_interface pool #x
  {{{ RET #(); True }}}.
Proof.
  iIntros (xLaterable xUnboxed Φ) "[#HIsPool HU] HΦ". wp_lam. wp_pures.
  iSpecialize ("HΦ" with "[$]").
  iDestruct "HIsPool" as (e d s p ->) "(HSt & HInv & HTq)".
  wp_pures.
  iLöb as "IH" forall (Φ).
  wp_bind (FAA _ _).
  iInv "HInv" as (elements1 failures1 ki1 kr1)
                   "(>% & HElems & H● & HOpen)" "HClose".
  iDestruct "HOpen" as (enqueuedThreads1) "(HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures1.
  destruct (decide (0 ≤ length elements1 - failures1 - enqueuedThreads1 + ki1 - kr1)%Z)
    as [HGe|HLt].
  - assert (enqueuedThreads1 = 0) as -> by lia. rewrite Z.sub_0_r.
    wp_faa.
    iAssert (|==> own γ (● (S ki1, kr1)) ∗ insertion_permit γ)%I
      with "[H●]" as ">[H● H◯]".
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_alloc, prod_local_update_1, nat_local_update.
      rewrite Nat.add_0_r. lia.
    }
    iMod ("HClose" with "[-HΦ H◯ HU]") as "_".
    { iExists elements1, failures1, _, _.
      iFrame "HElems H●". iSplitR.
      by iPureIntro; lia.
      iExists 0.
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      rewrite Z.sub_0_r.
      replace (_ + ki1 - kr1 + 1)%Z
        with (length elements1 - failures1 + S ki1 - kr1)%Z by lia.
      iFrame. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    awp_apply (tryInsert_spec with "HSt") without "IH HTq HΦ".
    iInv "HInv" as (elements2 failures2 ki2 kr2)
                    "(>% & [HElems HContents] & >H● & HOpen)".
    iAaccIntro with "HContents".
    {
      iIntros "HContents !>". iFrame "H◯ HU".
      iExists _, _, _, _. by iFrame.
    }
    iIntros (b) "HContents". destruct b.
    + iSplitL.
      2: { iModIntro. iIntros "HΦ". wp_pures. by iApply "HΦ". }
      simpl.
      rewrite -list_to_set_disj_cons.
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      iExists (x::elements2), failures2, ki2', kr2.
      iSplitR. by iPureIntro; simpl; lia.
      simpl.
      iFrame.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iSplitR; first by iPureIntro.
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - failures2 - enq + S ki2' - kr2)%Z
              with (S (length elements2) - failures2 - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
    + iSplitR "HU".
      2: { iModIntro. iIntros "HΦ". wp_pures. wp_lam. wp_pures.
           iApply ("IH" $! Φ with "[$] [$]"). }
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      destruct failures2 as [|failures2']; simpl.
      by iDestruct "HContents" as %[].
      iExists elements2, failures2', ki2', kr2. iFrame.
      iSplitR; first by iPureIntro; lia.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - S failures2' - enq + S ki2' - kr2)%Z
              with (length elements2 - failures2' - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
  - iMod (thread_queue_register_for_dequeue' with "HTq [] HState")
      as "[HState HAwak]"; [by solve_ndisj|lia|by iFrame|].
    wp_faa. iMod ("HClose" with "[-HΦ HAwak HU]") as "_".
    { iExists elements1, failures1, ki1, kr1.
      iFrame "HElems H●". iSplitR; first by iPureIntro.
      iExists (enqueuedThreads1 - 1).
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      by replace
           (length elements1 - failures1 - enqueuedThreads1 + ki1 - kr1 + 1)%Z
        with
          (length elements1 - failures1 - (enqueuedThreads1 - 1)%nat + ki1 - kr1)%Z
        by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_lam. wp_pures.
    wp_apply (resume_spec with "[] [HAwak HU]").
    5: { iFrame "HTq HAwak HU". iPureIntro; done. }
    by solve_ndisj. done. done.
    { simpl. iIntros (Ψ) "!> [H◯ HU] HΨ". wp_pures.
      iSpecialize ("HΨ" with "[%]"). done.
    iDestruct "HU" as "[HU _]".
    awp_apply (tryInsert_spec with "HSt") without "IH HTq HΨ".
    iInv "HInv" as (elements2 failures2 ki2 kr2)
                    "(>% & [HElems HContents] & >H● & HOpen)".
    iAaccIntro with "HContents".
    {
      iIntros "HContents !>". iFrame "H◯ HU".
      iExists _, _, _, _. by iFrame.
    }
    iIntros (b) "HContents". destruct b.
    + iSplitL.
      2: { iModIntro. iIntros "HΦ". wp_pures. by iApply "HΦ". }
      simpl.
      rewrite -list_to_set_disj_cons.
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      iExists (x::elements2), failures2, ki2', kr2.
      iSplitR. by iPureIntro; simpl; lia.
      simpl.
      iFrame.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iSplitR; first by iPureIntro.
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - failures2 - enq + S ki2' - kr2)%Z
              with (S (length elements2) - failures2 - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
    + iSplitR "HU".
      2: { iModIntro. iIntros "HΦ". wp_pures. wp_lam. wp_pures.
           iApply ("IH" $! Ψ with "[$] [$]"). }
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      destruct failures2 as [|failures2']; simpl.
      by iDestruct "HContents" as %[].
      iExists elements2, failures2', ki2', kr2. iFrame.
      iSplitR; first by iPureIntro; lia.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - S failures2' - enq + S ki2' - kr2)%Z
              with (length elements2 - failures2' - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
    }
    iIntros (b) "Hr". simpl. wp_pures. by iApply "HΦ".
Qed.

Theorem newPool_spec (n: nat) U:
  {{{ inv_heap_inv }}}
    newPool array_interface storage_interface #()
  {{{ γ γst γa γtq γe γd s, RET s; is_pool U γ γst γa γtq γe γd s }}}.
Proof.
  iIntros (Φ) "#HHeap HΦ". iApply fupd_wp.
  iMod (own_alloc (● (ε, ε))) as (γ) "H●".
  { apply auth_auth_valid. apply pair_valid. split; done. }
  iModIntro.
  wp_lam. wp_bind (newThreadQueue _ _).
  iApply (newThreadQueue_spec with "HHeap").
  iIntros (γa γtq γe γd e d) "!> [#HTq HThreadState]".
  rewrite -wp_fupd.
  wp_bind (newStorage _ _).
  iApply (newStorage_spec with "[$]").
  iIntros (γst st) "!> [#HStorage HContents]".
  wp_alloc p as "Hp". wp_pures.
  iMod (inv_alloc NPool _ (pool_inv U γ γst γtq p) with "[-HΦ]") as "#HInv".
  { iExists [], 0, 0, 0. simpl. iFrame. iSplitR; first done.
    iExists 0. iFrame. by iLeft. }
  iApply "HΦ". iExists _, _, _, _. iSplitR; first done. by iFrame "HInv HTq".
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

Lemma gmultiset_difference_disj_singleton' X Y B:
  X ∩ B = ∅ -> X ⊎ (Y ∖ B) = (X ⊎ Y) ∖ B.
Proof.
  move=> xintb. apply gmultiset_eq. move=> x.
  rewrite multiplicity_difference multiplicity_disj_union.
  rewrite multiplicity_difference multiplicity_disj_union.
  destruct (decide (x ∈ B)) as [XinB|XnotInB].
  2: { move: XnotInB. rewrite elem_of_multiplicity=> e. lia. }
  assert (not (x ∈ X)) as XnotInX.
  {
    assert (multiplicity x (X ∩ B) = 0) as XnotInXB.
    by rewrite xintb multiplicity_empty.
    move: XnotInXB. rewrite multiplicity_intersection.
    move: XinB xintb. rewrite !elem_of_multiplicity. lia.
  }
  move: XnotInX. rewrite elem_of_multiplicity=> e. lia.
Qed.
End XX.

Lemma XX {A} `{Countable A} x (xs: list A):
  x ∈ xs ->
  ∃ n,
  list_to_set_disj xs ∖ ({[x]}: gmultiset A) =
  list_to_set_disj (take n xs ++ drop (S n) xs) ∧ xs !! n = Some x.
Proof.
  move=> xInXs.
  induction xs.
  - exfalso. inversion xInXs.
  - simpl.
    destruct (decide (a = x)) as [eq|neq].
    * subst.
      rewrite -gmultiset_difference_disj_union.
      exists 0. simpl. rewrite drop_0. done.
    * inversion xInXs; first done. subst.
      rewrite -gmultiset_difference_disj_singleton'.
      2: {
        apply gmultiset_eq. move=> y.
        rewrite multiplicity_empty multiplicity_intersection.
        rewrite !multiplicity_singleton'.
        destruct (decide (y = a)) as [eq'|neq']; simpl; last done.
        destruct (decide (y = x)) as [eq''|neq']; simpl; last done.
        subst. done.
      }
      destruct IHxs as [m Hm]; first done.
      move: Hm. case=> -> HOk.
      exists (S m). simpl. by split.
Qed.

Theorem takePool_spec U γ γst γa γtq γe γd pool:
  {{{ is_pool U γ γst γa γtq γe γd pool }}}
    takePool array_interface storage_interface pool
  {{{ γf v, RET v; is_pool_future γ U γtq γa γf v ∗
                   thread_queue_future_cancellation_permit γf }}}.
Proof.
  iIntros (Φ) "#HIsPool HΦ". wp_lam. wp_pures.
  iDestruct "HIsPool" as (e d s p ->) "(HSt & HInv & HTq)".
  wp_pures.
  iLöb as "IH".
  wp_bind (FAA _ _).
  iInv "HInv" as (elements1 failures1 ki1 kr1)
                   "(>% & HElems & H● & HOpen)" "HClose".
  iDestruct "HOpen" as (enqueuedThreads1) "(HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures1.
  destruct (decide (0 < length elements1 - failures1 - enqueuedThreads1 + ki1 - kr1)%Z)
    as [HGe|HLt].
  - assert (enqueuedThreads1 = 0) as -> by lia. rewrite Z.sub_0_r.
    wp_faa.
    iAssert (|==> own γ (● (ki1, S kr1)) ∗ retrieval_permit γ)%I
      with "[H●]" as ">[H● H◯]".
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_alloc, prod_local_update_2, nat_local_update.
      rewrite Nat.add_0_r. lia. }
    iMod ("HClose" with "[-HΦ H◯]") as "_".
    { iExists elements1, failures1, ki1, (S kr1).
      iFrame "HElems H●". iSplitR.
      by iPureIntro; lia.
      iExists 0.
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      rewrite Z.sub_0_r.
      replace (_ - kr1 + -1)%Z
        with (length elements1 - failures1 + ki1 - S kr1)%Z by lia.
      iFrame. }
    iModIntro. wp_pures.
    rewrite bool_decide_true; last lia. wp_pures.
    awp_apply (tryRetrieve_spec with "HSt") without "IH HTq HΦ".
    iInv "HInv" as (elements2 failures2 ki2 kr2)
                    "(>% & [HElems HContents] & >H● & HOpen)".
    iAaccIntro with "HContents".
    {
      iIntros "HContents !>". iFrame "H◯".
      iExists _, _, _, _. by iFrame.
    }
    iIntros (v) "HContents". destruct v as [v|]; simpl.
    + destruct (multiplicity _ _) as [|m] eqn:E; first done.
      assert (∃ (b: base_lit), v = #b) as [b eq].
      {
        move: E. clear.
        induction elements2; first done.
        simpl. rewrite multiplicity_disj_union.
        destruct (decide (v = #a)) as [->|neq].
        - move=> _. exists a. done.
        - rewrite multiplicity_singleton' decide_False; last done.
          simpl.
          apply IHelements2.
      }
      subst.
      destruct (XX (#b) (LitV <$> elements2)) as [n [-> HElem]].
      { move: E. clear.
        induction elements2; first done.
        simpl. rewrite multiplicity_disj_union.
        destruct (decide (b = a)) as [->|neq].
        - move=> _. constructor.
        - rewrite multiplicity_singleton' decide_False; last by by case.
          simpl.
          move=> HH. move: (IHelements2 HH). by constructor.
      }
      rewrite -fmap_take -fmap_drop -fmap_app.
      assert (elements2 !! n = Some b) as HElem'.
      {
        rewrite list_lookup_fmap in HElem.
        destruct (elements2 !! n); last done.
        simpl in *.
        move: HElem. case=> -> //.
      }
      rewrite big_opL_take_drop_middle; last done.
      iDestruct "HElems" as "(HElems1 & HU & HElems2)".
      iSplitR "HU".
      2: {
        iModIntro. iIntros "HΦ". wp_pures.
        wp_apply (fillThreadQueueFuture_spec with "[HU]").
        2: { iIntros (γf v') "(HFuture & HCancPermit & _)".
             iApply "HΦ". iFrame. }
        rewrite /V'. simpl. iExists b. iFrame. iPureIntro.
        by repeat split.
      }
      iDestruct (own_valid_2 with "H● H◯")
        as %[[_ HValid%nat_included]%prod_included _]%auth_both_valid.
      simpl in *. destruct kr2 as [|kr2']; first lia.
      assert (n < length elements2). by eapply lookup_lt_Some.
      iExists (take n elements2 ++ drop (S n) elements2), failures2, ki2, kr2'.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_2, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      rewrite big_sepL_app.
      rewrite app_length take_length_le; last lia.
      rewrite drop_length.
      iSplitR.
      by iPureIntro; lia.
      iFrame "HElems1 HElems2 HContents".
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iExists enq. iFrame. iSplitL.
      2: by iPureIntro; lia.
      replace (length elements2 - failures2 - enq + ki2 - S kr2')%Z
              with ((n + (length elements2 - S n))%nat -
                                     failures2 - enq + ki2 - kr2')%Z by lia.
      by iFrame.
    + iDestruct (own_valid_2 with "H● H◯")
        as %[[_ HValid%nat_included]%prod_included _]%auth_both_valid.
      simpl in *. destruct kr2 as [|kr2']; first lia.
      iSplitL.
      2: {
        iModIntro. iIntros "HΦ". wp_pures. wp_lam. wp_pures.
        by iApply ("IH" with "HΦ").
      }
      iExists elements2, (S failures2), ki2, kr2'.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_2, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iSplitR; first by iPureIntro; lia.
      iFrame.
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iExists enq. iFrame. iSplitL; last by iPureIntro; lia.
      iModIntro.
      replace (length elements2 - failures2 - enq + ki2 - S kr2')%Z
              with (length elements2 - S failures2 - enq + ki2 - kr2')%Z by lia.
      by iFrame.
  - iMod (thread_queue_append' with "HTq [] HState")
      as "[HState HSus]"=> /=; [by solve_ndisj|done|].
    wp_faa. iMod ("HClose" with "[-HΦ HSus]") as "_".
    { iExists _, _, _, _. iFrame "HElems H●". iSplitR; first done.
      iExists (S enqueuedThreads1).
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      replace (_ - enqueuedThreads1 + ki1 - kr1 + -1)%Z with
          (length elements1 - failures1 - S enqueuedThreads1 + ki1 - kr1)%Z
          by lia.
      done. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_apply (suspend_spec with "[$]")=> /=. iIntros (v) "[(_ & _ & %)|Hv]".
    done.
    iDestruct "Hv" as (γf v') "(-> & HFuture & HCancPermit)". wp_pures.
    iApply "HΦ". iFrame.
Qed.

Theorem cancelPoolFuture_spec U γ γst γa γtq γe γd pool γf f:
  is_pool U γ γst γa γtq γe γd pool -∗
  is_pool_future γ U γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf >>>
    cancelPoolFuture array_interface storage_interface pool f @ ⊤ ∖ ↑NFuture ∖ ↑N
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf
      else (∃ v, ▷ future_is_completed γf v) ∗
           thread_queue_future_cancellation_permit γf, RET #r >>>.
Proof.
  iIntros "#HIsPool #HFuture" (Φ) "AU".
  iDestruct "HIsPool" as (e d s p ->) "(HSt & HInv & HTq)".
  wp_lam. wp_pures. wp_lam.
  wp_pures. awp_apply (try_cancel_thread_queue_future with "HTq HFuture");
              first by solve_ndisj.
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj.
  iIntros "HCancPermit". iAaccIntro with "HCancPermit". by iIntros "$ !> $ !>".
  iIntros (r) "Hr". iExists r. destruct r.
  2: { iDestruct "Hr" as "[$ $]". iIntros "!> HΦ !>". by wp_pures. }
  iDestruct "Hr" as "[#HFutureCancelled Hr]". iFrame "HFutureCancelled".
  rewrite /is_pool_future /is_thread_queue_future.
  iDestruct "Hr" as (i f' s' ->) "Hr"=> /=.
  iDestruct "Hr" as "(#H↦~ & #HTh & HToken)". iIntros "!> HΦ !>". wp_pures.
  wp_lam. wp_pures. wp_apply derefCellPointer_spec.
  by iDestruct "HTq" as "(_ & $ & _)". iIntros (ℓ) "#H↦". wp_pures.
  wp_bind (FAA _ _).
  iInv "HInv" as (elements1 failures1 ki1 kr1)
                   "(>% & HElems & H● & HOpen)" "HClose".
  iDestruct "HOpen" as (enqueuedThreads1) "(>HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  iMod (register_cancellation with "HTq HToken HState")
       as "[HCancToken HState]"; first by solve_ndisj.
  destruct (decide (length elements1 - failures1 - enqueuedThreads1 + ki1 - kr1 < 0)%Z)
    as [HLt|HGe].
  - assert (length elements1 - failures1 + ki1 - kr1 = 0)%Z as HPerms by lia.
    destruct enqueuedThreads1 as [|enqueuedThreads1']=>/=; first lia.
    iDestruct "HState" as "(HState & HCancHandle & #HInhabited)".
    wp_faa.
    iMod ("HClose" with "[-HΦ HCancToken HCancHandle]") as "_".
    { iExists elements1, failures1, ki1, kr1.
      iSplitR; simpl; first done. iFrame. iExists enqueuedThreads1'.
      rewrite Nat.sub_0_r. iFrame "HState".
      iSplitL; last by iLeft; iPureIntro; lia.
      replace (_ - S enqueuedThreads1' + ki1 - kr1 + 1)%Z with
          (length elements1 - failures1 - enqueuedThreads1' + ki1 - kr1)%Z;
        last lia.
      iFrame.
    }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markCancelled_spec with "HTq HInhabited H↦ HCancToken HTh")
              without "HΦ HCancHandle".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> [HΦ HCancHandle]". wp_pures.
    iAssert (▷ cell_cancellation_handle _ _ _ _ _ _)%I
            with "[HCancHandle]" as "HCancHandle"; first done.
    awp_apply (onCancelledCell_spec with "[] H↦~") without "Hv HΦ".
    by iDestruct "HTq" as "(_ & $ & _)".
    iAaccIntro with "HCancHandle". by iIntros "$".
    iIntros "#HCancelled !> [Hv HΦ]". wp_pures.
    iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (x ->) "(#HInhabited' & HAwak & HU)"; simplify_eq.
    wp_pures.
    iDestruct "HU" as "[HU [% %]]".
    wp_apply (resume_spec with "[] [HAwak HU]").
    5: { iFrame "HTq HAwak HU". by iPureIntro. }
    by solve_ndisj. done. done.
    2: {
      iIntros (b) "HContents". destruct b. by wp_pures.
      wp_pures. simpl. iDestruct "HContents" as "[[[]|[]] _]".
    }
    simpl. iIntros (Ψ) "!> [H◯ HU] HΨ". wp_pures.
    iSpecialize ("HΨ" with "[%]"). done.
    iDestruct "HU" as "[HU [% %]]".
    wp_bind (tryInsert _ _ _).
    awp_apply (tryInsert_spec with "HSt") without "HΨ".
    iInv "HInv" as (elements2 failures2 ki2 kr2)
                    "(>% & [HElems HContents] & >H● & HOpen)".
    iAaccIntro with "HContents".
    {
      iIntros "HContents !>". iFrame "H◯ HU".
      iExists _, _, _, _. by iFrame.
    }
    iIntros (b) "HContents". destruct b.
    + iSplitL.
      2: { iModIntro. iIntros "HΦ". wp_pures. by iApply "HΦ". }
      simpl.
      rewrite -list_to_set_disj_cons.
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      iExists (x::elements2), failures2, ki2', kr2.
      iSplitR. by iPureIntro; simpl; lia.
      simpl.
      iFrame.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iSplitR; first by iPureIntro.
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - failures2 - enq + S ki2' - kr2)%Z
              with (S (length elements2) - failures2 - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
    + iSplitR "HU".
      2: { iModIntro. iIntros "HΦ". wp_pures.
           iApply (putPool_spec with "[HU]"); try done.
           { iFrame "HU". iExists _, _, _, _. iFrame "HSt HInv HTq".
             done. }
           by iIntros "!> _".
      }
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      destruct failures2 as [|failures2']; simpl.
      by iDestruct "HContents" as %[].
      iExists elements2, failures2', ki2', kr2. iFrame.
      iSplitR; first by iPureIntro; lia.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - S failures2' - enq + S ki2' - kr2)%Z
              with (length elements2 - failures2' - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
  - rewrite bool_decide_true; last lia.
    assert (enqueuedThreads1 = 0) as -> by lia.
    simpl. iDestruct "HState" as "(HState & HR & #HInhabited)".
    wp_faa.
    iAssert (|==> own γ (● (S ki1, kr1)) ∗ insertion_permit γ)%I
      with "[H●]" as ">[H● H◯]".
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_alloc, prod_local_update_1, nat_local_update.
      rewrite Nat.add_0_r. lia. }
    iMod ("HClose" with "[-HΦ HCancToken H◯]") as "_".
    { iExists elements1, failures1, (S ki1), kr1.
      iFrame "H●". iSplitR; first by iPureIntro; lia.
      iFrame. iExists 0.
      iFrame "HState". iSplitL; last by iRight.
      by replace (_ + ki1 - kr1 + 1)%Z
        with (length elements1 - failures1 - 0%nat + S ki1 - kr1)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markRefused_spec with "HTq HInhabited H↦ HCancToken HTh H◯")
              without "HΦ".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> HΦ". iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (? ->) "[>H◯ [HU >[% %]]]". simplify_eq. wp_pures.
    awp_apply (tryInsert_spec with "HSt") without "HTq HΦ".
    iInv "HInv" as (elements2 failures2 ki2 kr2)
                    "(>% & [HElems HContents] & >H● & HOpen)".
    iAaccIntro with "HContents".
    {
      iIntros "HContents !>". iFrame "H◯ HU".
      iExists _, _, _, _. by iFrame.
    }
    iIntros (b) "HContents". destruct b.
    + iSplitL.
      2: { iModIntro. iIntros "HΦ". wp_pures. by iApply "HΦ". }
      simpl.
      rewrite -list_to_set_disj_cons.
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      iExists (v'::elements2), failures2, ki2', kr2.
      iSplitR. by iPureIntro; simpl; lia.
      simpl.
      iFrame.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iSplitR; first by iPureIntro.
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - failures2 - enq + S ki2' - kr2)%Z
              with (S (length elements2) - failures2 - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
    + iSplitR "HU".
      2: { iModIntro. iIntros "HΦ". wp_pures.
           wp_apply (putPool_spec with "[HU]"); try done.
           { iFrame. iExists _, _, _, _. iFrame "HSt HInv HTq". done. }
           iIntros "_". by wp_pures. }
      iDestruct (own_valid_2 with "H● H◯")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      simpl in *. destruct ki2 as [|ki2']; first lia.
      destruct failures2 as [|failures2']; simpl.
      by iDestruct "HContents" as %[].
      iExists elements2, failures2', ki2', kr2. iFrame.
      iSplitR; first by iPureIntro; lia.
      iMod (own_update_2 with "H● H◯") as "$".
      { apply auth_update_dealloc, prod_local_update_1, nat_local_update.
        rewrite Nat.add_0_r. lia. }
      iDestruct "HOpen" as (enq) "(HTq' & Hp & >%)".
      iExists enq. iFrame "HTq'". iSplitL; last by iPureIntro; lia.
      replace (length elements2 - S failures2' - enq + S ki2' - kr2)%Z
              with (length elements2 - failures2' - enq + ki2' - kr2)%Z
                   by lia.
      by iFrame.
Qed.

End proof.
