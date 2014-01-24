Require Import Equality List.
Set Implicit Arguments.
Open Scope list_scope.

Section Effects.
Variable label : Type.
Hypothesis label_dec : forall l1 l2 : label, {l1 = l2} + {l1 <> l2}.

Inductive tag : Set :=
| NatTag : tag
| ListTag : tag -> tag.
Inductive efftag : Set :=
| ReaderTag : tag -> efftag
| StateTag : tag -> efftag.
Inductive readerEff (A : Type) : Type -> Type :=
| Ask : readerEff A A.
Inductive stateEff (A : Type) : Type -> Type :=
| Put : A -> stateEff A unit
| Get : stateEff A A.
Fixpoint denoteTag (t : tag) : Type :=
  match t with
    | NatTag => nat
    | ListTag t' => list (denoteTag t')
  end.
Definition denoteEfftag (t : efftag) : Type -> Type :=
  match t with
    | ReaderTag r => readerEff (denoteTag r)
    | StateTag r => stateEff (denoteTag r)
  end.

Definition optag := (label * efftag)%type.
Definition optags := list optag.
Definition denoteOptag (t : optag) := denoteEfftag (snd t).

Inductive eff : Type -> optags -> Type :=
| Call : forall A e es R (ef : In e es) (op : denoteOptag e R)
                (k : R -> eff A es), eff A es
| Val : forall A es, A -> eff A es.

Lemma tag_eq_dec : forall (t1 t2 : tag), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Lemma efftag_eq_dec : forall (e1 e2 : efftag), {e1 = e2} + {e1 <> e2}.
Proof. decide equality; apply tag_eq_dec; apply tag_eq_dec. Defined.

Lemma optag_eq_dec : forall (o1 o2 : optag), {o1 = o2} + {o1 <> o2}.
  intros o1 o2.
  destruct o1, o2.
    destruct (efftag_eq_dec e e0).
      destruct e1.
      destruct (label_dec l l0).
        destruct e0. left. apply eq_refl.
        right. intro. refine (n _). congruence.
      right. intro. refine (n _). congruence.
Qed.

Lemma in_remove_other :
  forall A (eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) x1 x2 xs,
    In x1 xs -> x1 <> x2 -> In x1 (remove eq_dec x2 xs).
  intros A eq_dec x1 x2 xs elem neq.
  induction xs.
    tauto.

    destruct elem; unfold remove; destruct (eq_dec x2 a).
      exfalso. rewrite H in e. apply (neq (eq_sym e)). 
      left. assumption.
      apply (IHxs H).
      apply (in_cons a x1 _ (IHxs H)).
Qed.

Lemma neq_sym : forall A (a b : A), a <> b -> b <> a.
Proof. intros A a b neq. intro. apply (neq (eq_sym H)). Qed.

Fixpoint runReader_impl {ty : tag}{nm : label}{es : optags}{A : Type}
  (rdr : In (nm, ReaderTag ty) es)
  (AEq : denoteTag ty = A)
  (prog : eff A es)
  (ctx : denoteTag ty)
  {struct prog} : eff A (remove optag_eq_dec (nm, ReaderTag ty) es).
  destruct prog.
    destruct (optag_eq_dec (nm, ReaderTag ty) e).
      destruct e0.
      destruct op.

      apply (runReader_impl ty nm es A rdr AEq (k ctx) ctx).
      
      refine (@Call A e (remove optag_eq_dec (nm, ReaderTag ty) es) R _ op
                    (fun x => runReader_impl ty nm es A rdr AEq (k x) ctx)).
        apply (in_remove_other optag_eq_dec es ef (neq_sym n)).
      
    apply (Val _ a).
Defined.

Fixpoint runState_impl {ty : tag}{nm : label}{es : optags}{A S : Type}
  (st : In (nm, StateTag ty) es)
  (SEq : denoteTag ty = S)
  (prog : eff A es)
  (s : denoteTag ty)
  {struct prog} : eff (A * S) (remove optag_eq_dec (nm, StateTag ty) es).
  destruct prog.
    destruct (optag_eq_dec (nm, StateTag ty) e).
      destruct e0.
      destruct op.

      apply (runState_impl ty nm es A S st SEq (k tt) d).

      apply (runState_impl ty nm es A S st SEq (k s) s).
      
      refine (@Call _ _ (remove optag_eq_dec (nm, StateTag ty) es) R _ op
                    (fun x => runState_impl ty nm es A S st SEq (k x) s)).
        apply (in_remove_other optag_eq_dec es ef (neq_sym n)).
      
    rewrite SEq in s.
    apply (Val _ (a, s)).
Defined.

Fixpoint bind {A B : Type}{es : optags}
              (prog : eff A es) (f : A -> eff B es) {struct prog} : eff B es.
  destruct prog.
  apply (Call e ef op (fun x => bind A B es (k x) f)).
  apply (f a).
Defined.
Notation "m >>= f" := (bind m f)
  (at level 70, right associativity).
Notation "m >> f" := (m >>= fun _ => f)
  (at level 70, right associativity).

Definition eta {A : Type}{ts : optags} (x : A) : eff A ts := Val ts x.
Definition ask {ty : tag}{nm : label}{es : optags} (rdr : In (nm, ReaderTag ty) es)
  : eff (denoteTag ty) es :=
  Call (nm, ReaderTag ty) rdr (Ask (denoteTag ty)) (fun x => Val _ x).
Definition get {ty : tag}{nm : label}{es : optags} (rdr : In (nm, StateTag ty) es)
  : eff (denoteTag ty) es :=
  Call (nm, StateTag ty) rdr (Get (denoteTag ty)) (fun x => Val _ x).
Definition put {ty : tag}{nm : label}{es : optags}
  (rdr : In (nm, StateTag ty) es) (s : denoteTag ty)
  : eff unit es :=
  Call (nm, StateTag ty) rdr (Put s) (fun _ => Val _ tt).

Reserved Notation "{ p1 ~~ p2 } / { mask }" (at level 70, no associativity).
Inductive equiveff (mask : optags) : forall A es, eff A es -> eff A es -> Prop :=
| EqVal : forall A es (x y : A), x = y -> {Val es x ~~ Val es y} / {mask}
| EqCall : forall A e es R (ef1 ef2 : In e es) (op : denoteOptag e R)
                  (k1 k2 : R -> eff A es),
    (forall x, {k1 x ~~ k2 x} / {mask}) ->
    {Call e ef1 op k1 ~~ Call e ef2 op k2} / {mask}
| EqIgnore : forall A e es R (ef : In e es) (op : denoteOptag e R)
                    (eMasked : In e mask) (k : R -> eff A es) (p : eff A es),
  (forall x, {k x ~~ p} / {mask}) ->
  {Call e ef op k ~~ p} / {mask}

| EqSym : forall A es (p1 p2 : eff A es),
  {p1 ~~ p2} / {mask} -> {p2 ~~ p1} / {mask}
| EqTrans : forall A es (p1 p2 p3 : eff A es),
  {p1 ~~ p2} / {mask} -> {p2 ~~ p3} / {mask} -> {p1 ~~ p3} / {mask}

| AskAsk :
    forall ty nm es (rdr : In (nm, ReaderTag ty) es),
      {(ask rdr >>= fun x => eta (x, x)) ~~
       (ask rdr >>= fun x => ask rdr >>= fun y => eta (x, y))} / {mask}

| GetQuery :
    forall B ty nm es (p : eff B es) (st : In (nm, StateTag ty) es),
      {p ~~ (get st >> p)} / {mask}
| GetGet :
    forall ty nm es (st : In (nm, StateTag ty) es),
      {(get st >>= fun s => eta (s, s)) ~~
       (get st >>= fun s1 => get st >>= fun s2 => eta (s1, s2))} / {mask}
| PutPut :
    forall ty nm es x y (st : In (nm, StateTag ty) es),
      {put st y ~~ (put st x >> put st y)} / {mask}
| PutGet :
    forall ty nm es (st : In (nm, StateTag ty) es) x,
      {(put st x >> get st) ~~ (put st x >> eta x)} / {mask}
| GetPut :
    forall ty nm es (st : In (nm, StateTag ty) es),
      {(get st >>= put st) ~~ eta tt} / {mask}
where "{ p1 ~~ p2 } / { mask }" := (equiveff mask p1 p2).

Lemma equiveff_refl : forall mask A es (p : eff A es), {p ~~ p} / {mask}.
  intros mask A es p.
  induction p.
    apply EqCall; assumption.
    apply EqVal; reflexivity.
Qed.

Lemma return_bind : forall mask (A B : Type)(es : optags)(f : A -> eff B es)(x : A),
  {(eta x >>= f) ~~ f x} / {mask}.
  intros mask A B es f x.
  unfold bind, eta; apply equiveff_refl.
Qed.
Lemma bind_return : forall mask (A : Type)(es : optags)(p : eff A es),
  {(p >>= eta) ~~ p} / {mask}.
  intros mask A es p.
  unfold bind, eta.
  induction p.
    apply EqCall; assumption.
    apply EqVal; reflexivity.
Qed.
Lemma bind_assoc :
  forall mask A B C es (p : eff A es) (f : A -> eff B es) (g : B -> eff C es),
    {((p >>= f) >>= g) ~~ (p >>= fun x => (f x >>= g))} / {mask}.
  intros mask A B C es p f g.
  induction p.
    unfold bind. apply EqCall. apply (fun x => H x f g).
    unfold bind. apply equiveff_refl.
Qed.

Definition runEmpty (A : Type) (p : eff A nil) : A.
  dependent destruction p.
  exfalso. destruct ef.
  assumption.
Defined.
  
Fixpoint local_impl {ty : tag}{nm : label}{es : optags}{A : Type}
  (rdr : In (nm, ReaderTag ty) es)
  (f : denoteTag ty -> denoteTag ty)
  (prog : eff A es)
  {struct prog}
  : eff A es.
  destruct prog.
    destruct (optag_eq_dec (nm, ReaderTag ty) e).
      destruct e0.
      remember op.
      destruct op.
      apply (Call (nm, ReaderTag ty) ef d(fun x => local_impl ty nm es A rdr f (k (f x)))).
      
      apply (Call e ef op (fun x => local_impl ty nm es A rdr f (k x))).

    apply (Val _ a).
Defined.

Fixpoint rep {A : Type}{es : optags} (n : nat) (m : eff A es) : eff unit es :=
  match n with
  | O    => eta tt
  | S n' => m >> rep n' m
  end.
Definition tick {nm : label}{es : optags} (st : In (nm, StateTag NatTag) es) : eff unit es :=
  get st >>= fun m => put st (m+1).

Fixpoint runCountReader {ty : tag}{rdrNm stNm : label}{es : optags}{A : Type}
  (rdr : In (rdrNm, ReaderTag ty) es)
  (st : In (stNm, StateTag NatTag) es)
  (AEq : denoteTag ty = A)
  (prog : eff A es)
  (ctx : denoteTag ty)
  {struct prog} : eff A (remove optag_eq_dec (rdrNm, ReaderTag ty) es).
  destruct prog.
    destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
      destruct e0.
      destruct op.

      refine (tick (in_remove_other optag_eq_dec es st _) >>
              runCountReader ty rdrNm stNm es A rdr st AEq (k ctx) ctx).
        discriminate.
      
      refine (@Call A e (remove optag_eq_dec (rdrNm, ReaderTag ty) es) R _ op
                    (fun x => runCountReader ty rdrNm stNm es A rdr st AEq (k x) ctx)).
        apply (in_remove_other optag_eq_dec es ef (neq_sym n)).
      
    apply (Val _ a).
Defined.

Definition note {ty : tag}{nm : label}{es : optags}
  (trace : In (nm, StateTag (ListTag ty)) es) (v : denoteTag ty) : eff unit es :=
  get trace >>= fun m => put trace (v :: m).
Lemma list_tag_nofix : forall ty, ListTag ty <> ty.
  induction ty; try discriminate.
    injection.
    intro.
    apply (IHty H0).
Qed.

Fixpoint runTraceState {ty : tag}{stNm traceNm : label}{es : optags}{A S : Type}
  (st : In (stNm, StateTag ty) es)
  (trace : In (traceNm, StateTag (ListTag ty)) es)
  (SEq : denoteTag ty = S)
  (prog : eff A es)
  (s : denoteTag ty)
  {struct prog} : eff (A * S) (remove optag_eq_dec (stNm, StateTag ty) es).
  destruct prog.
    destruct (optag_eq_dec (stNm, StateTag ty) e).
      destruct e0.
      destruct op.

      refine (note (in_remove_other optag_eq_dec es trace _) d >>
              runTraceState ty stNm traceNm es A S st trace SEq (k tt) d).
        intro.
        assert (ListTag ty = ty) by congruence.
        apply (list_tag_nofix H0).
      apply (runTraceState ty stNm traceNm es A S st trace SEq (k s) s).
      
      refine (@Call _ _ (remove optag_eq_dec (stNm, StateTag ty) es) R _ op
                    (fun x => runTraceState ty stNm traceNm es A S st trace SEq (k x) s)).
        apply (in_remove_other optag_eq_dec es ef (neq_sym n)).
      
    rewrite SEq in s.
    apply (Val _ (a, s)).
Defined.

Section Stuff.
  Hypothesis equiveff_bind :
    forall mask (A B : Type) (es : optags) (p1 p2 : eff A es) (f1 f2 : A -> eff B es),
      {p1 ~~ p2} / {mask} ->
      (forall x, {f1 x ~~ f2 x} / {mask}) ->
      {(p1 >>= f1) ~~ (p2 >>= f2)} / {mask}.

  Lemma runReader_equiveff_impl {mask : optags}{ty : tag}{rdrNm : label}{es : optags}{A : Type}
    (rdr : In (rdrNm, ReaderTag ty) es)
    (AEq : denoteTag ty = A)
    : forall (p1 p2 : eff A es)(ctx : denoteTag ty),
        {p1 ~~ p2} / {mask} ->
        {runReader_impl rdr AEq p1 ctx ~~ runReader_impl rdr AEq p2 ctx} / {mask}.
    intros p1 p2 ctx p1Ep2.
    induction p1Ep2.
      rewrite H. apply (EqVal _ _ eq_refl).
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
        destruct e0.
        unfold runReader_impl.
        destruct (optag_eq_dec (rdrNm, ReaderTag ty) (rdrNm, ReaderTag ty)).
          dependent destruction e.
          destruct op.
          apply H0.
  
        apply EqCall. auto.
        
        unfold runReader_impl.
          destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
          tauto.
          apply EqCall.
          auto.

      (* EqIgnore *)
      unfold runReader_impl.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
        destruct e0.
        destruct op.
        apply H0.
        
        apply EqIgnore. assumption. apply (fun x => H0 x rdr AEq).

      (* EqSym *)
      apply (EqSym (IHp1Ep2 rdr AEq)).
  
      (* EqTrans *)
      apply (EqTrans (IHp1Ep2_1 rdr AEq) (IHp1Ep2_2 rdr AEq)).
  
      (* AskAsk *)
      unfold ask, bind, runReader_impl.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, ReaderTag ty0)).
        assert (tyEq : ty = ty0) by congruence. destruct tyEq.
        assert (nmEq : rdrNm = nm) by congruence. destruct nmEq.
        dependent destruction e.
        destruct (optag_eq_dec (rdrNm, ReaderTag ty) (rdrNm, ReaderTag ty)).
          dependent destruction e. apply equiveff_refl.
          exfalso. apply (n eq_refl).
        apply AskAsk.
        
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetQuery _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetGet _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (PutPut _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (PutGet _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetPut _).
  Qed.
  
  Lemma local_equiveff_impl {mask}{ty : tag}{rdrNm : label}{es : optags}{A : Type}
    (rdr : In (rdrNm, ReaderTag ty) es)
    (f : denoteTag ty -> denoteTag ty)
    : forall (p1 p2 : eff A es),
        {p1 ~~ p2} / {mask} ->
        {local_impl rdr f p1 ~~ local_impl rdr f p2} / {mask}.
    intros p1 p2 p1Ep2.
    induction p1Ep2.
      rewrite H. apply (EqVal _ _ eq_refl).
  
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
        destruct e0.
        unfold local_impl.
        destruct (optag_eq_dec (rdrNm, ReaderTag ty) (rdrNm, ReaderTag ty)).
          dependent destruction e.
          destruct op.
          apply EqCall.
          apply (fun x => H0 (f x) rdr).
  
        apply EqCall; auto.
        
        unfold local_impl.
          destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
          tauto.
          apply EqCall.
          auto.
          
      (* EqIgnore *)
      unfold local_impl.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
        destruct e0.
        destruct op.
        apply EqIgnore. assumption.
        apply (fun x => H0 (f x) rdr).
        
        apply EqIgnore. assumption.
        apply (fun x => H0 x rdr).

      (* EqSym *)
      apply (EqSym (IHp1Ep2 rdr)).
  
      (* EqTrans*)
      apply (EqTrans (IHp1Ep2_1 rdr) (IHp1Ep2_2 rdr)).
          
      (* AskAsk *)
      unfold ask, eta, bind, local_impl.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, ReaderTag ty0)).
        assert (tyEq : ty = ty0) by congruence. destruct tyEq.
        assert (nmEq : rdrNm = nm) by congruence. destruct nmEq.
        dependent destruction e.
        destruct (optag_eq_dec (rdrNm, ReaderTag ty) (rdrNm, ReaderTag ty)).
          dependent destruction e.
          apply (equiveff_bind _ _
                   (AskAsk _ ty rdrNm es rdr0)
                   (fun xy => equiveff_refl _ (Val es (f (fst xy), f (snd xy))))).
          
          exfalso. apply (n eq_refl).
        apply AskAsk.

      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetQuery _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetGet _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (PutPut _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (PutGet _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetPut _).
  Qed.

  Lemma runState_equiveff_impl {mask}{ty : tag}{stNm : label}{es : optags}{A S : Type}
    (st : In (stNm, StateTag ty) es)
    (SEq : denoteTag ty = S)
    (stateUnmasked : ~ In (stNm, StateTag ty) mask)
    : forall (p1 p2 : eff A es) (s : denoteTag ty),
        {p1 ~~ p2} / {mask} ->
        {runState_impl st SEq p1 s ~~ runState_impl st SEq p2 s} / {mask}.
    intros p1 p2 s p1Ep2.
    refine (
      equiveff_ind
        (fun (A : Type) (es : optags) (p1 p2 : eff A es) =>
                  forall (st : In (stNm, StateTag ty) es) (SEq : denoteTag ty = S)
                         (s : denoteTag ty),
                    {runState_impl st SEq p1 s ~~
                     runState_impl st SEq p2 s} / {mask})
        _ _ _ _ _ _ _ _ _ _ _ p1Ep2 st SEq s).
    (* Val *)
    intros. rewrite H. apply equiveff_refl.
    (* Call *)
    intros.
      unfold runState_impl.
      destruct (optag_eq_dec (stNm, StateTag ty) e).
        destruct e0.
        destruct op.
          apply (H0 tt st0 SEq0 d).
          apply (H0 _ st0 SEq0 s0).
        apply EqCall. apply (fun x => H0 x st0 SEq0 s0).
        
    (* Ignore *)
    intros.
    unfold runState_impl.
    destruct (optag_eq_dec (stNm, StateTag ty) e).
      exfalso. rewrite (eq_sym e0) in eMasked. apply (stateUnmasked eMasked).
      apply EqIgnore. assumption. apply (fun x => H0 x st0 SEq0 s0).

    (* Sym *)   intros. apply (EqSym (H0 st0 SEq0 s0)).
    (* Trans *) intros. apply (EqTrans (H0 st0 SEq0 s0) (H2 st0 SEq0 s0)).
        
    (* AskAsk *)
    intros.
    simpl.
    destruct (optag_eq_dec (stNm, StateTag ty) (nm, ReaderTag ty0)).
      discriminate.
      apply (equiveff_bind
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (AskAsk _ _ _ _ _)
               (fun x => equiveff_refl _ (eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0)))).
    
    (* GetQuery *)
    intros.
    unfold get, bind.
    unfold runState_impl at 2.
    destruct (optag_eq_dec (stNm, StateTag ty) (nm, StateTag ty0)).
      assert (nmEq : stNm = nm) by congruence. destruct nmEq.
      destruct (tag_eq_dec ty ty0).
        destruct e0. dependent destruction e. apply equiveff_refl.
        exfalso. congruence.
      apply (GetQuery _).

    (* GetGet *)
    intros.
    unfold get, bind, runState_impl.
    destruct (optag_eq_dec (stNm, StateTag ty) (nm, StateTag ty0)).
      assert (nmEq : stNm = nm) by congruence. destruct nmEq.
      assert (tyEq : ty = ty0) by congruence. destruct tyEq.
      dependent destruction e.
      destruct (optag_eq_dec (stNm, StateTag ty) (stNm, StateTag ty)).
        dependent destruction e; apply equiveff_refl.
        exfalso. apply (n eq_refl).
      apply (equiveff_bind
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (GetGet _ _ _ _ _)
               (fun x => equiveff_refl _ (eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0)))).

    (* PutPut *)
    intros.
    unfold put, bind, runState_impl.
    destruct (optag_eq_dec (stNm, StateTag ty) (nm, StateTag ty0)).
      assert (nmEq : stNm = nm) by congruence. destruct nmEq.
      assert (tyEq : ty = ty0) by congruence. destruct tyEq.
      dependent destruction e.
      destruct (optag_eq_dec (stNm, StateTag ty) (stNm, StateTag ty)).
        dependent destruction e; apply equiveff_refl.
        exfalso. apply (n eq_refl).
      apply (equiveff_bind
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (PutPut _ _ _ _ _ _ _)
               (fun x => equiveff_refl _ (eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0)))).

    (* PutGet *)
    intros.
    unfold runState_impl at 1.
    unfold put, get, eta, bind, runState_impl at 1.
    destruct (optag_eq_dec (stNm, StateTag ty) (nm, StateTag ty0)).
      assert (nmEq : stNm = nm) by congruence. destruct nmEq.
      assert (tyEq : ty = ty0) by congruence. destruct tyEq.
      dependent destruction e.
      destruct (optag_eq_dec (stNm, StateTag ty) (stNm, StateTag ty)).
        dependent destruction e. apply equiveff_refl.
        exfalso. apply (n eq_refl).
      apply (equiveff_bind
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (PutGet _ ty0 _ _ _ _)
               (fun x => equiveff_refl _ (eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0)))).

    (* GetPut *)
    intros.
    unfold put, get, bind, runState_impl, eta.
    destruct (optag_eq_dec (stNm, StateTag ty) (nm, StateTag ty0)).
      assert (nmEq : stNm = nm) by congruence. destruct nmEq.
      assert (tyEq : ty = ty0) by congruence; destruct tyEq.
      dependent destruction e.
      destruct (optag_eq_dec (stNm, StateTag ty) (stNm, StateTag ty)).
        dependent destruction e; apply equiveff_refl.
        exfalso. apply (n eq_refl).
      apply (equiveff_bind
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (fun x => eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0))
               (GetPut _ ty0 _ _ _)
               (fun x => equiveff_refl _ (eta (x, eq_rect (denoteTag ty) (fun T : Type => T) s0 S SEq0)))).
  Qed.

  Require Import Omega.
  Lemma tick_fusion :
    forall mask stNm (es : optags) (st : In (stNm, StateTag NatTag) es) n,
      {rep n (tick st) ~~ (get st >>= fun m => put st (m+n))} / {mask}.
    intros.
    induction n.
      unfold rep.
      assert ({(get st >>= put st) ~~ (get st >>= fun m => put st (m+0))} / {mask}).
        refine (equiveff_bind
                  (put st) (fun m => put st (m+0))
                  (equiveff_refl _ (get st))
                  _).
        assert (forall m, m = m + 0) by (intro; omega).
        intro. simpl. rewrite (H x) at 1.
        apply equiveff_refl.
      apply (EqTrans
               (EqSym (GetPut _ _ _ _ _))
               H).

      unfold rep.
      unfold tick at 1.
      refine (EqTrans
                (equiveff_bind
                   (fun _ => rep n (tick st)) (fun _ => get st >>= fun m => put st (m+n))
                   (equiveff_refl _ (get st >>= fun m => put st (m+1)))
                   (fun _ => IHn))
                _).
      refine (EqTrans
                (bind_assoc _ (get st)
                            (fun m => put st (m+1))
                            (fun _ => get st >>= fun m => put st (m+n)))
                _).
      refine (EqTrans
                (equiveff_bind
                   (fun m => put st (m+1) >> get st >>= fun m' => put st (m'+n))
                   (fun m => put st (m+1) >> eta (m+1) >>= fun m' => put st (m'+n))
                   (equiveff_refl _ (get st))
                   (fun m =>
                      equiveff_bind
                        (p1:=put st (m+1) >> get st) (p2:=put st (m+1) >> eta (m+1))
                        (fun m' => put st (m'+n)) (fun m' => put st (m'+n))
                        (PutGet _ _ _ _ _ _)
                        (fun m' => equiveff_refl _ (put st (m'+n)))))
                _).
      refine (EqTrans
                (equiveff_bind
                   (fun m => (put st (m+1) >> eta (m+1)) >>= fun m' => put st (m'+n))
                   (fun m => put st (m+1) >> put st (m+1+n))
                   (equiveff_refl _ (get st))
                   (fun _ => return_bind _ _ _))
                _).
      refine (EqTrans
                (equiveff_bind
                   (fun m => put st (m+1) >> put st (m+1+n))
                   (fun m => put st (m+1+n))
                   (equiveff_refl _ (get st))
                   (fun _ => EqSym (PutPut _ _ _ _ _ _ _)))
                _).
      refine (equiveff_bind (fun m => put st (m+1+n)) (fun m => put st (m + S n))
                            (equiveff_refl _ (get st))
                            _).
        intro.
        assert (x + 1 + n = x + S n) by omega.
        rewrite H.
        apply equiveff_refl.
  Qed.

  Lemma runCountReader_equiveff {mask}{ty : tag}{stNm rdrNm : label}{es : optags}{A S : Type}
    (st : In (stNm, StateTag NatTag) es)
    (maskState : In (stNm, StateTag NatTag) mask)
    (rdr : In (rdrNm, ReaderTag ty) es)
    (AEq : denoteTag ty = A)
    : forall (p1 p2 : eff A es) (ctx : denoteTag ty),
        {p1 ~~ p2} / {mask} ->
        {runCountReader rdr st AEq p1 ctx ~~ runCountReader rdr st AEq p2 ctx} / {mask}.
    intros p1 p2 ctx p1Ep2.
    induction p1Ep2.
      rewrite H. apply equiveff_refl.

      unfold runCountReader.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
        destruct e0.
        destruct op.
          apply (equiveff_bind
                   (fun (_ : unit) => runCountReader rdr st AEq (k1 ctx) ctx)
                   (fun (_ : unit) => runCountReader rdr st AEq (k2 ctx) ctx)
                   (equiveff_refl _ (tick _))
                   (fun _ => H0 ctx st rdr AEq)).
        apply EqCall. apply (fun x => H0 x st rdr AEq).

      (* Ignore *)
      unfold runCountReader.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) e).
        destruct e0.
        destruct op.
          apply EqIgnore. assumption.
          intro. apply EqIgnore. assumption.
          intro. apply (H0 ctx st rdr AEq).
        
        apply EqIgnore. assumption.
        apply (fun x => H0 x st rdr AEq).
        
      (* Sym *)   apply EqSym. apply (IHp1Ep2 st rdr AEq).
      (* Trans *) apply (EqTrans (IHp1Ep2_1 st rdr AEq)
                                 (IHp1Ep2_2 st rdr AEq)).

      (* AskAsk *)
      unfold ask, bind, runCountReader.
      destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, ReaderTag ty0)).
        assert (nmEq : rdrNm = nm) by congruence. destruct nmEq.
        assert (tyEq : ty = ty0) by congruence. destruct tyEq.
        dependent destruction e.
        destruct (optag_eq_dec (rdrNm, ReaderTag ty) (rdrNm, ReaderTag ty)).
          dependent destruction e.
          apply EqSym. apply EqIgnore. assumption. intro.
          apply EqIgnore. assumption. intro.
          apply equiveff_refl.

          exfalso. apply (n eq_refl).

        apply AskAsk.

      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetQuery _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetGet _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (PutPut _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (PutGet _).
      simpl. destruct (optag_eq_dec (rdrNm, ReaderTag ty) (nm, StateTag ty0)). discriminate.
        apply (GetPut _).
  Qed.

  (*
  Lemma runTraceState_equiveff {mask}{ty : tag}{stNm traceNm : label}{es : optags}{A S : Type}
    (trace : In (traceNm, StateTag (ListTag ty)) es)
    (maskTrace : In (traceNm, StateTag (ListTag ty)) mask)
    (st : In (stNm, StateTag ty) es)
    (SEq : denoteTag ty = S)
    : forall (p1 p2 : eff A es) (s : denoteTag ty),
        {p1 ~~ p2} / {mask} ->
        {runTraceState st trace SEq p1 s ~~ runTraceState st trace SEq p2 s} / {mask}.
    intros p1 p2 s p1Ep2.
    refine (
      equiveff_ind
        (fun (A : Type) (es : optags) (p1 p2 : eff A es) =>
                  forall (st : In (stNm, StateTag ty) es)
                         (trace : In (traceNm, StateTag (ListTag ty)) es)
                         (SEq : denoteTag ty = S)
                         (s : denoteTag ty),
                    {runTraceState st trace SEq p1 s ~~
                     runTraceState st trace SEq p2 s} / {mask})
        _ _ _ _ _ _ _ _ _ _ _ p1Ep2 st trace SEq s).
      intros. rewrite H. apply equiveff_refl.

      intros.
      unfold runTraceState.
      destruct (optag_eq_dec (stNm, StateTag ty) e).
        destruct e0.
        destruct op.
          apply (equiveff_bind
                   (fun (_ : unit) => runTraceState st0 trace0 SEq0 (k1 tt) d)
                   (fun (_ : unit) => runTraceState st0 trace0 SEq0 (k2 tt) d)
                   (equiveff_refl _ (note _ _))
                   (fun _ => H0 tt st0 trace0 SEq0 d)).
          apply (H0 s0 st0 trace0 SEq0 s0).
        fold (runTraceState (ty:=ty)(stNm:=stNm)(traceNm:=traceNm)(A:=A0)(S:=S)(es:=es0)).
        apply EqCall. apply (fun x => H0 x st0 trace0 SEq0 s0).
  Qed.
  *)
End Stuff.

End Effects.

Require Import String.
Open Scope string_scope.

Definition stEx1 : eff nat (("s", StateTag NatTag) :: nil).
  refine (get _ >>= fun (n : denoteTag NatTag) => eta (n + 2)).
  unfold In; auto.
Defined.
Definition runEx (ex : eff (denoteTag NatTag) (("s", StateTag NatTag) :: nil))
  : eff (denoteTag NatTag * nat) nil.
  assert (In ("s", StateTag NatTag) (("s", StateTag NatTag) :: nil)).
    unfold In. auto.
  refine (@runState_impl NatTag "s" _ (denoteTag NatTag) nat H _ ex 3).
  unfold In; auto.
  auto.
Defined.

Definition five_asks : eff unit (ReaderTag NatTag :: StateTag NatTag :: nil).
  refine (ask _ >>= fun _ =>
          ask _ >>= fun _ =>
          ask _ >>= fun _ =>
          ask _ >>= fun _ =>
          ask _ >>= fun ctx =>
          eta tt);
  simpl; auto.
Defined.

Definition ex1 : eff nat (ReaderTag NatTag :: nil).
  refine (ask _ >>= fun (n : denoteTag NatTag) => eta (n + 2)).
  unfold In; auto.
Defined.
Definition runRdrEx (ex : eff (denoteTag NatTag) (ReaderTag NatTag:: nil))
  : eff (denoteTag NatTag) nil.
  refine (@runReader_impl NatTag (ReaderTag NatTag :: nil) (denoteTag NatTag)
                          _ eq_refl ex 3).
  unfold In; auto.
Defined.
Eval compute in (runRdrEx ex1).
Eval compute in (runEmpty (runEx stEx1)).
Eval simpl in ((denoteTag NatTag * nat)%type).


Definition ex2 : eff (denoteTag NatTag) (ReaderTag NatTag :: nil).
  refine (local_impl _ (fun (n : denoteTag NatTag) => n + 3) ex1).
  unfold In; auto.
Defined.
Eval compute in (runRdrEx ex2).
