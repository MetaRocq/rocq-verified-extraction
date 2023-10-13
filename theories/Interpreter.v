Require Import ssreflect.

Require Import ZArith Array.PArray List Floats Lia.
Require Uint63.
Import ListNotations.

(*Require Import Malfunction.Malfunction Malfunction.Deserialize Malfunction.SemanticsSpec Malfunction.Serialize Ceres.Ceres.*)

Require Import Malfunction.Malfunction Malfunction.SemanticsSpec.
From MetaCoq Require Import bytestring.
Open Scope bs.

From Coq Require Import Uint63.

Class Heap := {
  pointer : Type;
  heapGen : forall (value : Type), Type;
  fresh : forall {value : Type}, heapGen value -> pointer * heapGen value;
  deref : forall {value : Type}, heapGen value -> pointer -> array value;
  update : forall {value : Type}, heapGen value -> pointer -> array value -> heapGen value
}.

Definition CanonicalHeap : Heap := 
{| pointer := int ;
   heapGen := fun value => (int * (int -> array value))%type;
   fresh :=  fun _ '(max_ptr , h) => let ptr := Int63.add max_ptr (int_of_nat 1) in (ptr ,(ptr, h));
   deref :=  fun _ '(_,h) ptr => h ptr;
   update := fun _ '(max_ptr , h) ptr arr => (max_ptr , fun ptr' => if Int63.eqb ptr ptr' then arr else h ptr) |}. 

Inductive rec_value `{Heap} := 
  | RFunc of Ident.t * t
  | RThunk of pointer
  | Bad_recursive_value.
 
Inductive value `{Heap} :=
  | Block of int * array value
  | Vec of vector_type * pointer
  | BString of vector_type * pointer
  | Func of @Ident.Map.t value * Ident.t *  t
  | RClos of @Ident.Map.t value * list Ident.t * list rec_value * nat
  | Lazy of @Ident.Map.t value * t
  | value_Int of inttype * Z
  | Float of float
  | Thunk of pointer
  | fail of string
  | not_evaluated.

Definition heap `{Heap} := heapGen value.

Definition is_not_evaluated `{Heap} : value -> bool := 
  fun v => match v with | not_evaluated => true | _ => false end. 

Definition add `{Heap} (x : string) (v : value) (locals : string -> value)  :=
  fun y =>
    if String.eqb y x then v else locals y.

Definition as_ty `{Heap} ty := fun ty2 =>
  match ty2 with
  | value_Int (ty', n) => if inttype_eqb ty ty' then n else fail_Z "integer type missmatch"
  | _ => fail_Z "expected integer"
  end.

Definition as_float `{Heap} x := match x with
  | Float f => f
  | _ => fail_float "expected float64"
end.

Definition RFunc_build `{Heap} recs := 
    map (fun t =>
      match t with 
      Mlambda ([x], e) => RFunc (x , e)
    | Mlambda (x :: xs , e) => RFunc (x , Mlambda (xs , e))
    | _ => Bad_recursive_value
    end) 
    recs.

Definition add_recs `{Heap} locals (self : list Ident.t) rfunc := 
  List.mapi (fun n x => (x , RClos (locals, self, rfunc, n))) self.

Definition add_self `{Heap} self rfunc locals := 
  List.fold_right (fun '(x,t) l => Ident.Map.add x t l) locals (add_recs locals self rfunc).

Definition cond `{Heap} scr case : bool := 
    (match case, scr with
      | Tag n, Block (n', _) => Int63.eqb n n'
      | Deftag, Block _ => true
      | Intrange (min, max), value_Int (Int, n) => Z.leb (Int63.to_Z min) n && Z.leb n (Int63.to_Z max)
      | _, _ => false end).
  
Definition find_match `{Heap} (interpret : heap -> @Ident.Map.t value -> @Ident.Map.t value -> t -> heap * value)
:= fun h iglobals ilocals scr => fix find_match x := match x with
| (cases, e) :: rest =>
    if List.existsb (cond scr)  cases then
      interpret h iglobals ilocals e
    else
      find_match rest
| [] => (h, fail "no case matches") end.

Definition truncate `{Heap} ty n :=
  value_Int (ty, match ty with
                 | Bigint => n
                 | ty =>
                     let width := bitwidth ty in
                     let range := Z.shiftl (Z.of_nat 1) width in
                     let masked := Z.land n (Z.sub range (Z.of_nat 1)) in
                     let min_int := Z.shiftr range 1 in
                     if Z.ltb masked min_int then masked else
                       Z.sub masked range
                 end).

(*                 
#[bypass_check(guard)]
Fixpoint to_sexp_value (a : value) : sexp :=
  match a with
  | Block (i, a) => @Serialize_product _ _ _ (@Serialize_list _ to_sexp_value) (i, List.map (fun j => a.[int_of_nat j]) (seq 0 (int_to_nat (PArray.length a))))
  | Vec x => Atom "TODO VEC"
  | Func x => Atom "FUNC"
  | value_Int x => Atom "TODO INT"
  | Float x => Atom "TODO FLOAT"
  | Thunk x => Atom "THUNK"
  | fail x => Atom ("fail" ++ String.to_string x)
  end%string.

#[export] Instance Serialize_value : Serialize value := to_sexp_value.
*)

#[bypass_check(guard)]
Fixpoint interpret `{Heap} (h : heap)
         (globals : @Ident.Map.t value)
         (locals : @Ident.Map.t value)
         (x : t) {struct x} : heap * value :=
  match x with
  | Mvar v => (h, Ident.Map.find v locals)
  | Mlambda (xs, e) =>
    (h, match xs with
    | [ ] => fail "assert false"
    | x :: xs => 
      let (x , e) := match xs with 
        | [] => (x , e)
        | _ :: _ => (x , Mlambda (xs, e)) end 
      in Func (locals, x , e)
    end)
  | Mapply (f_, vs) =>
     List.fold_left (fun f v => match f with
     | (h , Func (locals', x, e)) => 
        let (h' , v') := interpret h globals locals v 
        in interpret h' globals (Ident.Map.add x v' locals') e
     | (h , (RClos (locals', self, mfix , n))) =>
        let (h' , v') := interpret h globals locals v in
        match nth n mfix Bad_recursive_value with
        | RFunc (y , e) => 
          interpret h' globals (Ident.Map.add y v' (add_self self mfix locals')) e
        | _ => (h', fail "not a function") end
     | (h , _) => (h , fail ("not a function: " ++ " evaluated to: ")) end) vs 
      (interpret h globals locals f_)
   | Mlet (bindings, body) =>
     let bind :=
        fix bind (h : heap) (locals : @Ident.Map.t value) (bindings : list binding) : heap * value :=
        match bindings with
        | [] => interpret h globals locals body
        | Unnamed e :: bindings => 
          let (h' , _) := interpret h globals locals e in bind h' locals bindings
        | Named (x, e) :: bindings =>
          let (h' ,v) := interpret h globals locals e in
          bind h' (Ident.Map.add x v (locals)) bindings
        | Recursive recs :: bindings =>
          let self := map fst recs in
          let rfunc := RFunc_build (map snd recs) in
          bind h (add_self self rfunc locals) bindings 
        end
     in
      bind h locals bindings 
  | Mnum (numconst_Int n) => (h , value_Int (Int, Int63.to_Z n))
  | Mnum (numconst_Bigint n) => (h , value_Int (Bigint, n))
  | Mnum (numconst_Float64 f) => (h, Float f)

  | Mstring s =>
    let (ptr,h') := fresh h in
    let str := Array_init (Int63.of_Z (Z.of_nat (String.length s))) 
                      (fun i => value_Int (Int, (Z.of_nat (Byte.to_nat (option_def (Ascii.byte_of_ascii Ascii.Space) (get (Z.to_nat (Int63.to_Z i)) s)))))) in
     (update h' ptr str , Vec (Bytevec, ptr))
     
  | Mglobal v => (h , Ident.Map.find v globals)

  | Mswitch (scr, cases) => 
      let (h', scr') := interpret h globals locals scr in
      find_match interpret h' globals locals scr' cases

  | Mnumop1 (op, embed_inttype ty, e) =>
      let (h',v) := interpret h globals locals e in 
      let n := as_ty ty v in
      (h', truncate ty (match op with Malfunction.Neg => Z.mul (-1) n | Not => Z.lnot n end))

  | Mnumop2 (op, embed_inttype ty, e1, e2) =>
      let (h1 , e1) := interpret h globals locals e1 in
      let (h2 , e2) := interpret h1 globals locals e2 in
      (h2, match op with
      | embed_binary_arith_op op =>
          let f := match op with
                   | Add => Z.add | Sub => Z.sub
                   | Mul => Z.mul | Div => Z.div | Mod => Z.rem 
                   end in
          truncate ty (f (as_ty ty e1) (as_ty ty e2))
      | embed_binary_bitwise_op op =>
          let n := as_ty ty e1 in
          let c := as_ty Int e2 in
          (* TODO is this test necessary? *)
          truncate ty (match op with
          | And => Z.land (as_ty ty e1) (as_ty ty e2)
          | Or => Z.lor (as_ty ty e1) (as_ty ty e2)
          | Xor => Z.lxor (as_ty ty e1) (as_ty ty e2)
          | Lsl => Z.shiftl n c
          | Asr => Z.shiftr n c
          | Lsr => 
              let n := match ty with
                       | Bigint => n
                       | op =>
                           let w := bitwidth ty in
                           Z.land n (Z.sub (Z.shiftl (Z.of_nat 1) w) (Z.of_nat 1)) end in
              Z.shiftr n c end)
      | embed_binary_comparison op =>
          let cmp := Z.compare (as_ty ty e1) (as_ty ty e2) in
          let res := match op with
            | Lt => comparison_eqb cmp Datatypes.Lt
            | Gt => comparison_eqb cmp Datatypes.Gt
            | Lte => negb (comparison_eqb cmp Datatypes.Gt)
            | Gte => negb (comparison_eqb cmp Datatypes.Lt)
            | Eq => comparison_eqb cmp Datatypes.Eq
                     end in
          value_Int (Int, if res then 1%Z else 0%Z)
      end)
  | Mnumop1 (Malfunction.Neg, Float64, e) =>
    let (h' , v) := interpret h globals locals e in (h' , Float (- as_float v))
  | Mnumop1 (Not, Float64, _) 
  | Mnumop2 (embed_binary_bitwise_op _, Float64, _, _) =>
      (h , fail "invalid bitwise float operation")
  | Mnumop2 (embed_binary_arith_op op, Float64, e1, e2) =>
      let (h1,e1') := interpret h globals locals e1 in
      let (h2,e2') := interpret h1 globals locals e2 in
      let e1 := as_float e1' in
      let e2 := as_float e2' in
      (h2, Float (match op with
             | Add => e1 + e2
             | Sub => e1 - e2
             | Mul => e1 * e2
             | Div => e1 / e2
             | Mod => fail_float "mod on floats not supported" end))
  | Mnumop2 (embed_binary_comparison op, Float64, e1, e2) =>
      let (h1,e1') := interpret h globals locals e1 in
      let (h2,e2') := interpret h1 globals locals e2 in
      let e1 := as_float e1' in
      let e2 := as_float e2' in
      let res := match op with
             | Lt => PrimFloat.ltb e1 e2
             | Gt => PrimFloat.ltb e2 e2
             | Lte => PrimFloat.leb e1 e2
             | Gte => PrimFloat.leb e2 e1
             | Eq => PrimFloat.eqb e1 e2
                 end in
      (h2, value_Int (Int, if res then 1%Z else 0%Z))
  | Mconvert (embed_inttype src, embed_inttype dst, e) =>
      let (h',v) := interpret h globals locals e in
      (h', truncate dst (as_ty src v))
  | Mconvert (embed_inttype src, Float64, e) =>
      let (h',v) := interpret h globals locals e in
      (h',Float (PrimFloat.of_uint63 (Int63.of_Z (as_ty src v))))
  | Mconvert (Float64, Float64, e) =>
      let (h',v) := interpret h globals locals e in
      (h',Float (as_float v))
  | Mvecnew (ty, len, def) =>
      let (h1,len') := interpret h globals locals len in
      let (h2,def') := interpret h1 globals locals def in
      let (ptr,h3) := fresh h2 in
      match ty, len' , def' with
      | Array, value_Int (Int, len), v =>
          (update h3 ptr (PArray.make (Int63.of_Z len) v), Vec (Array, ptr))
      | Bytevec, value_Int (Int, len), (value_Int (Int, k)) as v =>
          if Z.leb 0%Z k && Z.ltb k 256 then
            (update h3 ptr (PArray.make (Int63.of_Z len) v), Vec (Bytevec, ptr))
          else
            (h3,fail "bad vector creation")
      | _, _, _ => (h2,fail "bad vector creation")
      end
  | Mvecget (ty, vec, idx) =>
      let (h1,vec') := interpret h globals locals vec in
      let (h2,idx') := interpret h1 globals locals idx in
      (h2, match vec', idx' with
       | Vec (ty', ptr), value_Int (Int,i) =>
           if vector_type_eqb ty ty' then
             if Z.leb 0 i && Z.ltb i (Int63.to_Z (PArray.length (deref h ptr))) then
               PArray.get (deref h ptr) (Int63.of_Z i)
             else
               fail "index out of bounds: %d"
           else
             fail "wrong vector type"
       | _, _ => fail "wrong vector type"
       end)      
  | Mvecset (ty, vec, idx, e) => 
      let (h1,vec') := interpret h globals locals vec in
      let (h2,idx') := interpret h1 globals locals idx in
      let (h3,v) := interpret h2 globals locals e in
      match vec', idx', v with 
        | Vec (ty', ptr), value_Int (Int, i), v => 
          if vector_type_eqb ty ty' then 
              let i' := Int63.of_Z i in 
              if Z.leb 0 i && Z.ltb i (Int63.to_Z (PArray.length (deref h ptr))) then 
                match ty, v with 
                | Array, _ => (update h3 ptr (PArray.set (deref h ptr) i' v), value_Int (Int, 0%Z))
                | Bytevec, value_Int (Int, val) => 
                  if (Z.leb 0 val) && (Z.ltb val 256)
                  then 
                    (update h3 ptr (PArray.set (deref h ptr) i' v), value_Int (Int, 0%Z))
                  else (h3, fail "not a byte")
                | Bytevec, _ => (h3, fail "not a byte")
                end 
              else (h3, fail "index out of bounds: %d")
          else (h3, fail "wrong vector type")
        | _ , _ , _ => (h3, fail "wrong vector type")
      end
  | Mveclen (ty, vec) =>
      let (h',vec') := interpret h globals locals vec in
      (h', match vec' with
      | Vec (ty', ptr) =>
          if vector_type_eqb ty ty' then value_Int (Int, Int63.to_Z (PArray.length (deref h ptr)))
                                    else fail "wrong vector type"
      | _ => fail "wrong vector type"
      end)
  | Mblock (tag, vals) =>
      let (h',vals') := map_acc (fun h e => interpret h globals locals e) h vals in
      (h', if (int_of_nat (Datatypes.length vals) ≤? max_length)%uint63 
           then Block (tag, Array_of_list (fail "") vals')
           else fail "vals is a too big array")
  | Mfield (idx, b) =>
      let (h',b') := interpret h globals locals b in
      (h', match b' with
      | Block (_, vals) => PArray.get vals idx
      | _ => fail "not a block"
      end)
  | Mlazy e => 
    let (ptr,h') := fresh h in
    let init := PArray.make (Int63.of_Z 2) not_evaluated in
    let arr := PArray.set init (Int63.of_Z 1) (Lazy (locals , e)) in
    (update h' ptr arr, Thunk ptr)
  | Mforce e =>
      let (h',v) := interpret h globals locals e in
      match v with
      | Thunk ptr => let arr := deref h' ptr in 
                     let lazy := PArray.get arr (Int63.of_Z 0) in
                     if is_not_evaluated lazy
                     then 
                        match PArray.get arr (Int63.of_Z 1) with 
                          | Lazy (locals , e) => 
                            let (h'' , v') := interpret h' globals locals e in
                           (update h'' ptr (PArray.set arr (Int63.of_Z 0) v'), v')
                          | _ => (h', fail "not a lazy value")
                        end
                     else (h', lazy)
      | _ => (h', fail "not a lazy value")
      end
  | _ => (h , fail "assert todo")
end. 

Class CompatiblePtr `{SemanticsSpec.Heap} `{Heap} :=  
{ R_ptr : SemanticsSpec.pointer -> pointer -> Prop }.

Inductive vrel `{CompatiblePtr} : SemanticsSpec.value -> value -> Prop :=
  | vBlock : forall tag vals vals', Forall2Array vrel vals vals' (SemanticsSpec.fail "") ->
      vrel (SemanticsSpec.Block (tag, vals)) (Block (tag, vals'))
  | vVec : forall ty ptr ptr', R_ptr ptr ptr' -> vrel (SemanticsSpec.Vec (ty, ptr)) (Vec (ty, ptr'))
  | vBString : forall ty ptr ptr', R_ptr ptr ptr' -> vrel (SemanticsSpec.BString (ty, ptr)) (BString (ty, ptr'))
  | vFunc : forall x locals locals' e,  
    (forall x, vrel (locals x) (locals' x)) ->
    vrel (SemanticsSpec.Func (locals,x,e)) (Func (locals',x,e))
  | vRClos : forall self mfix mfix' n locals locals',  
    (forall x, vrel (locals x) (locals' x)) ->
    (forall n y e,
      (nth n mfix SemanticsSpec.Bad_recursive_value = SemanticsSpec.RFunc (y, e)) 
      <-> 
      (nth n mfix' Bad_recursive_value = RFunc (y, e))) ->
    (*  (forall h v, interpret h globals (Ident.Map.add x v (add_all mfix E locals') locals') e = f h v) -> *)
    vrel (SemanticsSpec.RClos (locals,self,mfix,n)) (RClos (locals',self,mfix',n))
  | vInt : forall ty i , 
      vrel (SemanticsSpec.value_Int (ty, i)) (value_Int (ty, i))
  | vFloat : forall f, 
      vrel (SemanticsSpec.Float f) (Float f)
  | vThunk : forall ptr ptr', R_ptr ptr ptr' -> 
      vrel (SemanticsSpec.Thunk ptr) (Interpreter.Thunk ptr')
  | vLazy : forall e locals locals',  
    (forall x, vrel (locals x) (locals' x)) ->
    vrel (SemanticsSpec.Lazy (locals, e)) (Lazy (locals' , e))
  | vFail : forall s, 
      vrel (SemanticsSpec.fail s) (Interpreter.fail s)
  | vNot_evaluated : vrel SemanticsSpec.not_evaluated Interpreter.not_evaluated.

Definition vrel_locals `{CompatiblePtr} 
  : Ident.Map.t -> Ident.Map.t -> Prop := fun locals ilocals => forall x, vrel (locals x) (ilocals x).

Class CompatibleHeap `{CompatiblePtr} :=  
  { R_heap : SemanticsSpec.heap -> heap -> Prop;
    fresh_compat : forall h ptr h' ih, 
      R_heap h ih -> SemanticsSpec.fresh h ptr h' -> 
      let (iptr,ih') := fresh ih in R_ptr ptr iptr /\ R_heap h' ih';
    update_compat : forall default h ih ptr ptr' h' v v', 
      R_heap h ih -> SemanticsSpec.update h ptr v h' -> 
      R_ptr ptr ptr' -> Forall2Array vrel v v' default ->
      let ih' := Interpreter.update ih ptr' v' in R_heap h' ih';
    deref_compat : forall default h ih ptr ptr' vals, 
      R_heap h ih -> SemanticsSpec.deref h ptr vals -> 
      R_ptr ptr ptr' -> 
      let vals' := Interpreter.deref ih ptr' in 
      Forall2Array vrel vals vals' default 
   }.

Lemma cond_correct  `{CompatiblePtr} 
  scr scr' x : vrel scr scr' -> 
  SemanticsSpec.cond scr x = Interpreter.cond scr' x.
Proof.
  now destruct x as [ | | [] ]; destruct 1. 
Qed.

Lemma existsb_ext {A} (f g : A -> bool) l :
  (forall x, f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intros H; induction l; cbn; congruence.
Qed.

Lemma find_match_correct `{CompatiblePtr}  scr scr' cases e h iglobals ilocals :
  vrel scr scr' ->
  SemanticsSpec.find_match scr cases = Some e ->
  Interpreter.find_match Interpreter.interpret h iglobals ilocals scr' cases = interpret h iglobals ilocals e.
Proof.
  induction cases as [ | a cases IHcases ]; cbn [SemanticsSpec.find_match]; intros rel Eq.
  - inversion Eq.
  - destruct a. 
    cbn [find_match].
    destruct existsb eqn:E.
    * inversion Eq. erewrite existsb_ext. 
      2:{ intros. symmetry. eapply cond_correct. eauto.  }
      now rewrite E. 
    * erewrite existsb_ext.
      2:{ intros. symmetry. eapply cond_correct. eauto. }
      rewrite E. eauto.
Qed.

Lemma vrel_add `{CompatiblePtr} x v iv locals ilocals : vrel v iv -> vrel_locals locals ilocals -> 
  vrel_locals (Ident.Map.add x v locals) (Ident.Map.add x iv ilocals).
Proof.
  intros Hv Hlocals nm. unfold Ident.Map.add. now destruct Ident.eqb.
Qed.

Lemma isNotEvaluated_vrel `{CompatiblePtr} v v' b : 
  vrel v v' -> isNotEvaluated v = b <-> is_not_evaluated v' = b.
Proof.
  now destruct 1.
Qed.    

Ltac fail_case IHeval Hloc Hheap Heq := 
  let Hv := fresh "iv1" in cbn; specialize (IHeval _ _ Hloc Hheap); destruct interpret as [? ?];
  destruct IHeval as [? Hv]; destruct Hv; inversion Heq; split;eauto; econstructor.

Lemma vrel_locals_add_self `{CompatiblePtr}  locals' locals'0 mfix mfix' self :
  (forall x : Ident.t, vrel (locals' x) (locals'0 x)) ->
  (forall (n : nat) (y : Ident.t) (e : t),
     nth n mfix SemanticsSpec.Bad_recursive_value = SemanticsSpec.RFunc (y, e) <->
    nth n mfix' Bad_recursive_value = RFunc (y, e)) ->
  vrel_locals (SemanticsSpec.add_self self mfix locals') (add_self self mfix' locals'0).
Proof. 
  intros Hloc ?.
  unfold add_self, SemanticsSpec.add_self.
  unfold add_recs, SemanticsSpec.add_recs. unfold List.mapi.
  generalize 0. generalize self at 1 3. 
  pose proof (Hcopy := Hloc). revert Hcopy.  
  generalize locals' at 1 3. generalize locals'0 at 1 3.
  revert locals' locals'0 Hloc.     
  induction self; eauto; cbn; intros. 
  intro. unfold Ident.Map.add. case_eq (Ident.eqb x a); intro; eauto. 
  - now econstructor.
  - apply IHself; eauto.  
Qed. 


Lemma as_ty_vrel `{CompatibleHeap} ty v v' : 
  vrel v v' -> 
  SemanticsSpec.as_ty ty v = as_ty ty v'.
Proof. 
  inversion 1; destruct ty; cbn; try reflexivity.
Defined.

Lemma as_float_vrel `{CompatibleHeap} v v' : 
  vrel v v' -> 
  SemanticsSpec.as_float v = as_float v'.
Proof. 
  inversion 1; cbn; try reflexivity.
Defined.

Lemma truncate_vrel `{CompatibleHeap} ty z : 
  vrel (SemanticsSpec.truncate ty z) (truncate ty z).
  destruct ty; econstructor.
Qed. 

Lemma eval_correct `{CompatibleHeap} 
  globals locals ilocals iglobals e h h' ih v :
  (forall nm val, In (nm, val) globals -> vrel val (iglobals nm)) ->
  vrel_locals locals ilocals ->
  R_heap h ih ->
  eval _ globals locals h e h' v -> 
  let (ih',iv) := interpret ih iglobals ilocals e in R_heap h' ih' /\ vrel v iv.  
Proof.
  rename H into _Heap; rename H0 into _iHeap; rename H1 into _CPtr; rename H2 into _CHeap. 
  intros Hglob Hloc Hheap.
  induction 1 as [ (* lambda_sing *) locals h x e
                 | (* lambda *) locals h x ids e H
                 | (* app_sing *) locals h1 h2 h3 h4 x locals' e e2 v2 e1 v H IHeval1 H0 IHeval2 H1 IHeval3
                 | (* app_sing_Rec *) locals h1 h2 h3 h4 mfix n y e locals' self e2 v2 e1 v H IHeval1 H0 IHeval2 Hnth H1 IHeval3
                 | (* app_fail *) locals h h' e2 e v Heval IHeval Heq
                 | (* app *) locals h h' e2 e1 v vals tag IHeval 
                 | (* var *) 
                 | (* let_body *) | (* let_unnamed *) | (* let_named *) | (* let_rec *)
                 | (* switch *) 
                 | (* block *)  
                 | (* field *) locals h h' idx b vals tag H IHeval | | | | | | 
                 | | | | | | | | | | | | | | | | | | | ]
    in ih, Hheap, ilocals, Hloc |- *. 
  (* eval_lambda_sing *) 
  - split; eauto. econstructor; eauto.
  (* eval_lambda *)
  - split; eauto. 
    destruct ids as [ | t ids ]; cbn in H. 1:inversion H. clear H.
    econstructor; eauto.  
  (* eval_app_sing *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    specialize (IHeval2 _ _ Hloc Hheap1). destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2].
    inversion Hiv1 ; subst.
    specialize (IHeval3 (Ident.Map.add x iv2 locals'0) ih2). 
    destruct interpret as [ih3 iv3]; cbn in *.
    apply IHeval3; eauto. now apply vrel_add. 
  (* eval_app_sing_rec *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    specialize (IHeval2 _ _ Hloc Hheap1). destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2].
    inversion Hiv1 ; subst.
    edestruct H8. specialize (H2 Hnth). rewrite H2.
    specialize (IHeval3 (Ident.Map.add y iv2 (add_self self mfix' locals'0)) ih2). 
    destruct interpret as [ih3 iv3]; cbn in *.
    apply IHeval3; eauto. apply vrel_add; eauto.
    now apply vrel_locals_add_self. 
  (* eval_app_fail *)
  - fail_case IHeval Hloc Hheap Heq.
  (* eval_app *)
  - now apply IHeval.
  (* eval_var *)
  - cbn; eauto.
  (* eval_let_body *)
  - now eapply IHeval.
  (* eval_let_unnamed *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    now eapply IHeval2. 
  (* eval_let_named *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    eapply IHeval2; eauto. now apply vrel_add. 
  (* eval_let_rec *)
  - cbn; eapply IHeval; eauto. intros x. clear IHeval. subst.
    apply vrel_locals_add_self; eauto.
    intros. unfold rfunc. set (l := map snd recs). clearbody self l. split. 
    + revert n. induction l; cbn.
      * intros n H; destruct n; eauto; cbn in *; inversion H.
      * intros n H. destruct n; eauto. 
        destruct a; inversion H. destruct p. destruct l0 ; inversion H.
        destruct l0 ; now inversion H. 
    + revert n. induction l; cbn.
      * intros n H; destruct n; eauto; cbn in *; inversion H.
      * intros n H. destruct n; eauto. 
        destruct a; inversion H. destruct p. destruct l0 ; inversion H.
        destruct l0 ; now inversion H. 
  (* eval_switch *)
  - cbn.
    specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    erewrite find_match_correct; eauto. now apply IHeval2.
  (* eval_block *)
  - cbn. clear H. revert ih Hheap. induction H1. 
    + intros ih Hheap. split ; eauto. econstructor.
      split; [ reflexivity|]. cbn. lia.
    + intros ih Hheap. simpl. 
      specialize (H _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct H as [Hheap1  Hiv1]. 
      assert (Hlength: Datatypes.length l' < int_to_nat max_length) by (cbn in *; lia). 
      specialize (IHForall2_acc Hlength ih1 Hheap1).     
      unshelve epose proof (Forall2_acc_map R_heap vrel
                              (fun (h : Interpreter.heap) (e : t) => interpret h iglobals ilocals e) _ _ _ _ _ _ H1 _ Hheap1).
      { clear -Hloc. intros. cbn in *. specialize (H0 ilocals x'). destruct interpret. apply H0; eauto. }
      set (p := map_acc _ ih1 l) in *. destruct p. destruct H as [Heahp2 Hl0]. split; eauto. 
      destruct IHForall2_acc as [? IHForall2_acc]. 
      assert (Hl: (int_of_nat (Datatypes.length l) ≤? max_length)%uint63 = true).
      { apply leb_spec. rewrite Int63.of_Z_spec.
        rewrite (Forall2_acc_length H1). rewrite Z.mod_small; [lia_max_length |].
        unfold max_length in *. cbn in *. lia. }
      assert (Hl': (int_of_nat (S (Datatypes.length l)) ≤? max_length)%uint63 = true).
      { apply leb_spec. rewrite Int63.of_Z_spec. rewrite (Forall2_acc_length H1). 
        rewrite Z.mod_small; lia_max_length. }
      rewrite Hl in IHForall2_acc. rewrite Hl'. inversion IHForall2_acc; subst. clear IHForall2_acc.  
      econstructor. destruct H3. split.
      * simpl. rewrite Array_of_list_length.
        { cbn. rewrite <- (Forall2_length Hl0). clear - H0; cbn in *; lia. }
        now rewrite (Forall2_length Hl0).
      * intros idx Hidx. rewrite <- (int_of_to_nat idx) at 2.
        pose proof (Hbounded := to_Z_bounded idx).
        destruct (int_to_nat idx).
        ** simpl. pose Int63.wB_pos. rewrite Array_of_list_get; try (cbn; lia).
        ++ cbn in H0. rewrite (Forall2_length Hl0) in H0. clear - H0; lia_max_length. 
        ++ cbn in H0. rewrite (Forall2_length Hl0) in H0. clear - H0; lia_max_length. 
        ++ eauto.
           ** simpl. rewrite Array_of_list_S. 
        ++ cbn; cbn in Hidx. rewrite <- (Forall2_length Hl0). lia.
        ++ cbn; cbn in H0. rewrite <- (Forall2_length Hl0). lia.
        ++ specialize (H3 (int_of_nat n)). 
           rewrite int_to_of_nat in H3.
           { clear -Hidx H0; lia_max_length. }
           eapply H3. cbn in Hidx; lia.  
  (* eval_field *)    
  - cbn. specialize (IHeval _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto. inversion Hiv1; subst. clear Hiv1. destruct H5 as [? H5]. 
    now eapply (H5 idx).  
  (* eval_field_fail *)    
  - fail_case IHeval Hloc Hheap H0.
  (* eval_lazy *)  
  - cbn. pose proof (fresh_compat _ _ _ _ Hheap H).
    set (Interpreter.fresh ih) in *. destruct p.
    destruct H1; split; [| now econstructor].
    eapply update_compat with (default := SemanticsSpec.fail ""); eauto. 
    split; [reflexivity|].
    intros idx Hidx. rewrite <- (int_of_to_nat idx). destruct int_to_nat. 
    * cbn. econstructor; eauto.
    * cbn in Hidx. destruct n; [compute|lia].
      econstructor; eauto.
  (* eval_force_done *)  
  - cbn. specialize (IHeval _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1]. 
    inversion Hiv1; subst; clear Hiv1.
    pose proof (deref_compat (SemanticsSpec.fail "") _ _ _ _ _ Hheap1 H0 H5).
    destruct H2 as [? Hderef]. pose proof (Hderef (int_of_nat 0)).
    cbn in H4. rewrite isNotEvaluated_vrel in H3; eauto.
    + eapply H4. lia.
    + destruct is_not_evaluated; inversion H3.
      split; eauto. eapply H4. lia.
  (* eval_force *)  
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    inversion Hiv1; subst; clear Hiv1.
    pose proof (deref_compat (SemanticsSpec.fail "") _ _ _ _ _ Hheap1 H0 H7).
    destruct H6 as [? Hderef]. pose proof (Hderef (int_of_nat 0)).
    cbn in H8. rewrite isNotEvaluated_vrel in H2; [eapply H8; lia|]. 
    destruct is_not_evaluated; inversion H2. clear H2. 
    rewrite H1 in Hderef. 
    specialize (Hderef (int_of_nat 1) (ltac:(eauto))).
    rewrite H3 in Hderef. cbn in Hderef. set _.[1] in *. 
    inversion Hderef. subst. rewrite <- H11 in Hderef.
    specialize (IHeval2 _ _ H9 Hheap1). 
    destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2].
    split; eauto. 
    eapply update_compat with (default := SemanticsSpec.fail ""); eauto. split; cbn.   
    * rewrite PArray.length_set. lia.
    * intro i. pose proof (int_of_to_nat i). destruct (int_to_nat i); [| destruct  n].
    + subst. intros _. rewrite get_set_same; eauto.
      rewrite <- (int_of_to_nat (PArray.length _)). rewrite <- H6. 
      rewrite H1. cbn; lia.
    + subst; intros _. rewrite get_set_other; [now apply eqb_false_spec|]. cbn.
      fold y. rewrite <- H11. econstructor; eauto.
    + lia. 
  (* eval_force_fail *)  
  - fail_case IHeval Hloc Hheap H0.
  (* eval_global *)  
  - cbn. split; eauto.
  (* eval_num_int *)
  - cbn [interpret]; split; eauto; econstructor. 
  (* eval_num_bigint *)
  - cbn [interpret]; split; eauto; econstructor.
  (* eval_num_float *)
  - cbn [interpret]; split; eauto; econstructor.
  (* eval_string *)
  - cbn [interpret]. pose proof (fresh_compat _ _ _ _ Hheap H0).
    set (Interpreter.fresh ih) in *. destruct p.
    destruct H2; split; [| now econstructor].
    eapply update_compat with (default := SemanticsSpec.fail ""); eauto.
    apply Forall2Array_init; eauto.
    intros k Hk. pose (int_to_of_nat k). 
    unfold int_to_nat in e. rewrite e; [lia_max_length| econstructor].
  (* eval_numop1 *)
  - cbn [interpret]; destruct op; cbn [interpret];
      specialize (IHeval _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1];
      split; eauto; erewrite <- as_ty_vrel; eauto; eapply truncate_vrel.
  (* eval_numop2 *)
  - cbn [interpret]; destruct op; cbn [interpret];
      specialize (IHeval1 _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1];
      specialize (IHeval2 _ _ Hloc Hheap1); destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2];
      split; eauto.
    1-2: destruct b; repeat erewrite <- as_ty_vrel; eauto; eapply truncate_vrel.
    destruct b; repeat erewrite <- as_ty_vrel; eauto; econstructor. 
  (* eval_numop1_neg *)
  - cbn [interpret].
    specialize (IHeval _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto; erewrite as_float_vrel; eauto; econstructor.
  (* eval_numop1_float_fail *)
  - cbn [interpret]; split; eauto; econstructor. 
  (* eval_numop2_float_fail *)
  - cbn [interpret]; split; eauto; econstructor. 
  (* eval_numop2_float *)
  - cbn [interpret]; destruct op; cbn [interpret];
      specialize (IHeval1 _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1];
      specialize (IHeval2 _ _ Hloc Hheap1); destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2];
      split; eauto;cbn; repeat erewrite <- as_float_vrel; eauto; econstructor.
  (* eval_numop2_embed_float *)  
  - cbn [interpret]; destruct op; cbn [interpret];
      specialize (IHeval1 _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1];
      specialize (IHeval2 _ _ Hloc Hheap1); destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2];
      split; eauto;cbn; repeat erewrite <- as_float_vrel; eauto; econstructor.
  (* eval_convert_int *)
  - cbn [interpret].
    specialize (IHeval _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto. erewrite <- as_ty_vrel; eauto; eapply truncate_vrel.
  (* eval_convert_float *)
  - cbn [interpret].
    specialize (IHeval _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto. erewrite <- as_ty_vrel; eauto; econstructor.
  (* eval_convert_float_float *) 
  - cbn [interpret].
    specialize (IHeval _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto. erewrite <- as_float_vrel; eauto; econstructor.
  (* eval_vecnew_array *)
  - cbn [interpret];
      specialize (IHeval1 _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1];
      specialize (IHeval2 _ _ Hloc Hheap1); destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2];
      inversion Hiv1; subst; clear Hiv1.
    pose proof (fresh_compat _ _ _ _ Hheap2 H3).
    set (Interpreter.fresh ih2) in *. destruct p.
    destruct H5; split; [| now econstructor].
    eapply update_compat with (default := SemanticsSpec.fail ""); eauto.
    assert (Hlen' : Int63.of_Z len' = int_of_nat (Z.to_nat len')).
    { unfold int_of_nat. rewrite Z2Nat.id; eauto. }
    rewrite Hlen'. apply (Forall2Array_cst _ (Z.to_nat len') _ iv2); eauto.
  (* eval_vecnew_bytevec *)
  - cbn [interpret];
      specialize (IHeval1 _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1];
      specialize (IHeval2 _ _ Hloc Hheap1); destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2];
      inversion Hiv1; subst; clear Hiv1.
    inversion Hiv2; subst; clear Hiv2. rewrite H3. 
    pose proof (fresh_compat _ _ _ _ Hheap2 H4).
    set (Interpreter.fresh ih2) in *. destruct p.
    destruct H6; split; [| now econstructor].
    eapply update_compat with (default := SemanticsSpec.fail ""); eauto.
    unfold List.init. unfold Forall2Array.
    assert (Hlen' : Int63.of_Z len' = int_of_nat (Z.to_nat len')).
    { unfold int_of_nat. rewrite Z2Nat.id; eauto. }
    rewrite Hlen'. apply Forall2Array_cst; eauto.
    econstructor.
  (* eval_vecget *)
  - cbn [interpret];
      specialize (IHeval1 _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1];
      specialize (IHeval2 _ _ Hloc Hheap1); destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2];
      inversion Hiv1; subst; clear Hiv1.
    split; eauto.
    pose proof (deref_compat (SemanticsSpec.fail "") _ _ _ _ _ Hheap H1 H5).
    destruct H2 as [? Hderef].
    case (vector_type_eqb ty ty').
    2: {  
      destruct idx'; destruct iv2;  try (destruct p as [i0 ?]; destruct i0); 
      try (destruct p0 as [i1 ?]; destruct i1);  try econstructor. }
    destruct idx'; destruct iv2; 
      try (destruct p as [i0 n]; destruct i0); 
      try (destruct p0 as [i1 n']; destruct i1); try econstructor; 
      try inversion Hiv2. subst. 
    pose proof (leb_length _ (deref ih ptr')).
    case_eq ((0 <=? n')%Z); intro; simpl; try econstructor.
    case_eq (n' <? Z.of_nat (Datatypes.length arr))%Z;
      case_eq (n' <? φ (PArray.length (deref ih ptr'))%uint63)%Z; intros.
    + assert (Hn': (0 <= n' < Int63.wB)%Z).
      {split; [lia|]. clear -H3 H4 H6.
       apply leb_spec in H3. apply Z.ltb_lt in H6.
       set (PArray.length _) in *. clearbody i.
       clear H4. lia_max_length.  }
      assert (Heqn' : Z.to_nat n' = int_to_nat (Int63.of_Z n')).
      { unfold int_to_nat. f_equal. rewrite Int63.of_Z_spec.
        rewrite Z.mod_small; eauto. } 
      rewrite Heqn'. apply Hderef. unfold int_to_nat. rewrite Int63.of_Z_spec.
      rewrite Z.mod_small; eauto. apply Z.ltb_lt in H7.
      lia.
    + rewrite H2 in H7. unfold int_to_nat in H7.
      rewrite Z2Nat.id in H7. apply to_Z_bounded. 
      rewrite H7 in H6. inversion H6.
    + rewrite H2 in H7. unfold int_to_nat in H7.
      rewrite Z2Nat.id in H7. apply to_Z_bounded. 
      rewrite H7 in H6. inversion H6.
    + econstructor. 
  (* eval_vecset *)
  - cbn [interpret]; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    specialize (IHeval2 _ _ Hloc Hheap1).
    destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2].
    inversion Hiv1 ; subst. inversion Hiv2 ; subst. specialize (IHeval3 _ _ Hloc Hheap2). 
    destruct interpret as [ih3 iv3]. destruct IHeval3 as [Hheap3  Hiv3].
    case_eq  (vector_type_eqb ty ty'); [| repeat econstructor; eauto].
    pose proof (deref_compat (SemanticsSpec.fail "") _ _ _ _ _ Hheap H2 H7).
    destruct H4 as [Hsize Hderef]. 
    rewrite Hsize. unfold int_to_nat. rewrite Z2Nat.id.
    pose (to_Z_bounded (PArray.length (deref ih ptr'))); lia. 
    intro Htyty'. 
    case_eq (Z.leb 0 i && (Z.ltb i (Int63.to_Z (PArray.length (deref ih ptr')))))%bool;
      [| repeat econstructor; eauto].
    rename i into z. intro Harr. apply MCProd.andb_and in Harr.
    destruct Harr as [Hz0 Harr]. apply Z.leb_le in Hz0. 
    apply Z.ltb_lt in Harr.   
    pose proof (Hmax := leb_length _ (deref ih ptr')).
    apply leb_spec in Hmax.
    destruct ty. 
    + split; [| econstructor; eauto].       
      eapply update_compat with (default := SemanticsSpec.fail ""); eauto. 
      split. now rewrite List.length_set PArray.length_set.
      intros i Hi. set (arr' := deref _ _) in *. clearbody arr'.
      case_eq (i =? Int63.of_Z z)%uint63. 
      * intro eq; apply eqb_correct in eq. subst. 
        unfold int_to_nat. rewrite Int63.of_Z_spec Z.mod_small; 
          [ lia_max_length |].
        rewrite get_set_same; eauto.
        apply ltb_spec. 
        rewrite Int63.of_Z_spec Z.mod_small; lia_max_length.  
        pose (Hnth := List.nth_set_same). rewrite Hnth; eauto.
        rewrite Hsize. unfold int_to_nat. apply Z2Nat.inj_lt; cbn in *; lia.
      * rewrite eqb_false_spec. intro Hneq. rewrite get_set_other; eauto.
        rewrite List.nth_set_other. intro Hneq'; apply Hneq.
        assert (int_of_nat (Z.to_nat z) = int_of_nat (int_to_nat i)) by now f_equal.
        rewrite int_of_to_nat in H4. unfold int_of_nat in H4.
        rewrite Z2Nat.id in H4; [lia | eauto].
        eapply Hderef. now rewrite List.length_set in Hi.         
    + destruct iv3; inversion Hiv3; try repeat econstructor; eauto.
      destruct ty; try repeat econstructor; eauto.
      case_eq ((0 <=? i)%Z && (i <? 256)%Z)%bool; try repeat econstructor; eauto.
      eapply update_compat with (default := SemanticsSpec.fail ""); eauto. 
      split. now rewrite List.length_set PArray.length_set. rename i into z'. 
      intros i Hi. set (arr' := deref _ _) in *. clearbody arr'.
      case_eq (i =? Int63.of_Z z)%uint63. 
      * intro eq; apply eqb_correct in eq. subst. 
        unfold int_to_nat. rewrite Int63.of_Z_spec Z.mod_small; [lia_max_length |].
        rewrite get_set_same; eauto.
        apply ltb_spec. rewrite Int63.of_Z_spec Z.mod_small; lia_max_length.  
        pose (Hnth := List.nth_set_same). rewrite Hnth; eauto.
        rewrite Hsize. unfold int_to_nat. apply Z2Nat.inj_lt; cbn in *; lia.
      * rewrite eqb_false_spec. intro Hneq. rewrite get_set_other; eauto.
        rewrite List.nth_set_other. intro Hneq'; apply Hneq.
        assert (int_of_nat (Z.to_nat z) = int_of_nat (int_to_nat i)) by now f_equal.
        rewrite int_of_to_nat in H8. unfold int_of_nat in H8.
        rewrite Z2Nat.id in H8; [lia | eauto].
        eapply Hderef. now rewrite List.length_set in Hi.         
  (* eval_vec_length *)     
  - cbn [interpret].
    specialize (IHeval _ _ Hloc Hheap); destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto. inversion Hiv1; subst.  
    destruct (vector_type_eqb ty ty'); try econstructor.
    pose proof (deref_compat (SemanticsSpec.fail "") _ _ _ _ _ Hheap H0 H4).
    destruct H1 as [Hsize Hderef]. rewrite Hsize.
    unfold int_to_nat. rewrite Z2Nat.id. 
    pose (to_Z_bounded (PArray.length (deref ih ptr'))); lia.        
    econstructor. 
Qed.
