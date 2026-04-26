(*
This Coq script is made for Coq 8.5 and coq-mathcomp-ssreflect 1.6
Both available on opam with repository https://coq.inria.fr/opam/released

For Coq 8.4, it should work by just changing the first line to
Require Import ssreflect.
 *)

>From mathcomp Require Import ssreflect.

(*****************************)
(* INDUCTIVE TYPES: Examples *)
(*****************************)

(* Enumerated types *)

Inductive color : Type :=
| blue : color
| green : color
| magenta : color
| yellow : color.

Print bool.

Definition is_blue x :=
  match x with
    | blue => true
    | _ => false
  end.

(* With an actual inductive structure *)

Print nat.
Print Nat.pred.
Print Nat.add.

Lemma half: forall x, exists y, x=y+y \/ x=1+y+y.
  elim.
    exists 0.
    by left.
  move => n [y ih].
  case:ih => ih.
    exists y.
    right.
    simpl.
    by rewrite ih.
  exists (1+y).
  left.
  rewrite ih.
  simpl.
  by rewrite <- plus_n_Sm.
Defined.

Check (half 25).
Compute (half 25).

(* Inductive types used for logical connectives *)

Print and.

Lemma AndCom: forall A B, A /\ B -> B /\ A.
Proof.
  move => A.
  move => B.
  move => H.
  case: H.
  move => HA.
  move => HB.
  split.
  exact HB.
  exact HA.
Qed.

Print AndCom.

Check (fun A B (H: A /\ B) =>
         match H with
           | conj x1 x2 => conj x2 x1
         end
      ).

Print or.

Check (fun A B (H: A \/ B) =>
         match H with
           | or_introl x => or_intror x
           | or_intror x => or_introl x
         end
      ).

Print False.

Definition abort (A:Prop) (H:False)
  := match H return A with
    end.

Check abort.

Print True.

(*********************************)
(* Not presented during lecture: *)
(* Why is Prop not just Bool ??? *)

Definition prop_degeneracy := forall A : Prop, A = True \/ A = False.

(** [prop_extensionality] asserts that equivalent formulas are equal *)
Definition prop_extensionality := forall A B : Prop, (A <-> B) -> A = B.

(** [excluded_middle] asserts that we can reason by case on the truth
    or falsity of any formula *)
Definition excluded_middle := forall A : Prop, A \/ ~ A.

(** We can show

Lemma prop_ext_em_degen :
  prop_degeneracy <-> (prop_extensionality /\ excluded_middle).

Would be degenerating a lot of the structure given by intuitionistic logic
**)


(*********************************)
(* Not presented during lecture: *)
(* Existential quantification    *)
(*********************************)

Print ex.
Print sigT.

(* Same thing, but the former operates in Prop (i.e. Type_0 in the
slides), while the latter operates in Type (i.e. Type_1 in the
slides).  In other words, the former is really the existential
quantification to build formulae, while the latter is the type of
dependent pairs. As we will be using them below, we introduce a
convenient notation for dependent pairs:
 *)

Notation "{{ p , v }} " := (existT _ p v).

(*************************)
(* EQUALITY *)
(*************************)

Print eq.

Lemma Leibniz: forall A (x:A) (P: A -> Prop), P x -> forall y:A, x = y -> P y.
Proof.
  move => A x P H y Heq.
  rewrite <- Heq.
  exact H.
Qed.

(******************************)
(* Unicity of Identity Proofs *)
(******************************)

Section UnicityIdentityProofs.

  Variable A: Type.

  Definition UIP_refl :=
    forall (x:A) (p: x=x), p = eq_refl x.

  Definition K :=
    forall (x:A) (P: x=x -> Prop),
      P (eq_refl x) -> forall p:(x=x), P p.

  Definition J :=
    forall (x:A) (P: forall y:A, x=y -> Prop),
      P x (eq_refl x) -> forall p:(x=x), P x p.

  (* UIP_refl and K are NOT provable in the calculus of constructions *)
  (* K integrated to Agda, Epigram. Can be added as axiom to Coq (could also
relax typing rule for match so that it holds natively) *)

  (* On the other hand, J is provable! Here is how it goes *)

  (* For a fixed x of type A, we define the space of power cord as
  follows (end point y together with a path from x to y *)

  Definition vacuum_cleaner_power_cord (x : A) := {y : A & x=y}.

  (* The trivial power cord with endpoint x itself, together with the
  trivial path from x to x, is in that space *)

  Check ((fun x => {{ x , eq_refl }}) : forall x, vacuum_cleaner_power_cord x).

  (* Every power cord based on a fixed x, is retractable to the
  trivial path *)

  Remark power_cord_retraction :
    forall x:A, forall (z : vacuum_cleaner_power_cord x), z = {{ x , eq_refl }}.
  Proof.
    move=> x z.
    case: z => y p.
    (* The 'destruct' tactic realizes the 'retraction' of the path *)
    destruct p.
    apply: eq_refl.
  Qed.

  (* J becomes an easy corollary *)

  Theorem J_proof: J.
  Proof.
    rewrite/J.
    intros.
    move:(power_cord_retraction x {{ x, p }}).
    rewrite <- p.
    elim.
    exact H.
  Qed.


  (* For the record, here's why K implies UIP_refl. The converse also
  holds *)

  Lemma y: K -> UIP_refl.
    rewrite /K /UIP_refl.
    intros.
    move : (H x (fun q => q = eq_refl) eq_refl) => H0.
    apply H0.
  Qed.


  (* Another version equivalent to K *)

  Definition UIP (A:Type) :=
    forall (x y:A) (p1 p2:x = y), p1 = p2.

  (* A consequence of K, also not provable in just the calculus of
  constructions *)

  Definition Inj_dep_pair (A:Type) :=
    forall (B :A -> Type) (x:A) (p1 p2: B x), {{ x, p1 }} = {{ x, p2 }} -> p1 = p2.

End UnicityIdentityProofs.

(* We have seen that UIP and K are not provable in general.  However,
for certain types, it is. A sufficient condition is the following one:
if equality on type A is decidable, then UIP and K hold (Hedberg
theorem). *)

Check (forall (A:Type)(x:A)(e: x=x), e = eq_refl x).

Section Hedberg.

  Variable A : Type.
  (* Assume we have a function d that decides equality *)
  Variable d: A -> A -> bool.
  Hypothesis Hd: forall x y: A, true = d x y <-> x = y.

  Definition comp {a b : A} (p : a = b) {c : A} (q : b = c) : a = c.
  Proof.
    destruct p.
    exact: q.
  Defined.

  Lemma comp_simpl {a b} (r : a = b) {c : A} (p q : b = c) :
    comp r p = comp r q ->  p = q.
    destruct r.
    compute.
    apply.
  Qed.

  Lemma comp_f (f : forall x y : A, x = y -> x = y) (x y : A) (p : x = y) :
    f _ _ p = comp (f _ _ eq_refl) p.
  Proof.
    destruct p.
    destruct (f x x eq_refl).
    apply: eq_refl.
  Qed.

  (* We need a little tool *)

  Definition aux (y0:bool) (e:true=y0)
    := match e in (_ = y0) return (if y0 then True else False) with
        | eq_refl => I
      end.

  Check aux.

  Definition distinct := aux false.

  Definition elect_eq_proof (x y:A) (e: x=y) : x=y
    :=
      let inhabit test :=
          match test
                return (true = test -> x = y)
                       -> (x = y -> true = test)
                       -> x = y
          with
            | true => fun h3 _ => h3 eq_refl
            | false => fun _ h4 => abort _ (distinct (h4 e))
          end
      in
      let (h1,h2) := Hd x y in
      inhabit (d x y) h1 h2
  .

  Definition has_singleton_image {C : Type} (f : C -> C) :=  forall x y : C, f x = f y.

  Lemma elect_has_singleton_image:
    forall x y:A, has_singleton_image (elect_eq_proof x y).
  Proof.
    move => x y.
    rewrite /has_singleton_image  => e1 e2.
    rewrite /elect_eq_proof.
    case: (Hd x y).
    case: (d x y).
    move => h3 _.
    exact eq_refl.
    move => _ h4.
    case: (distinct (h4 e1)).
  Qed.

  Theorem Hedberg : forall (x y : A), forall (p q : x = y), p = q.
  Proof.
    move => x y p q.
    suff e : comp (elect_eq_proof x x eq_refl) p = comp (elect_eq_proof x x eq_refl) q.
    apply: comp_simpl e.
    have hg1 := (comp_f elect_eq_proof x y p). rewrite -hg1.
    have hg2 := (comp_f elect_eq_proof x y q). rewrite -hg2.
    apply: elect_has_singleton_image.
  Qed.

End Hedberg.

(*************)
(* UIP for bool *)
(*************)

(* We can decide the equality on the boolean, so UIP should hold for
them *)

Definition bool_eq (b1 b2:bool)
  := match b1, b2 with
      | true, true => true
      | false, false => true
      | _ , _ => false
    end.

Lemma bool_eq_decide: forall (b1 b2: bool), true = bool_eq b1 b2 <-> b1 = b2.
Proof.
  case; case => //.
Qed.

Definition UIP_bool := Hedberg bool bool_eq bool_eq_decide.

Check UIP_bool.

(**********************)
(* PredicateSubtyping *)
(**********************)

(* If UIP holds on the boolean, we can use functions to bool in order to
emulate predicate subtyping, as is used for instance in PVS. *)

Section PredicateSubtyping.

  Variable A:Type.
  Variable f: A -> bool.

  Record A_sub_f :=
    {
      element : A;
      satisfying : true = f element
    }.

  (* We show that equality does not depend on the satisfying component
  *)

  Lemma proj_inj : forall (u v: A_sub_f), u.(element) = v.(element) -> u = v.
  Proof.
    case => ue us /=.
    case => ve vs /=.
    move => H.
    move : us.
    rewrite H => us.
    rewrite (UIP_bool true (f ve) us vs).
    exact eq_refl.
  Qed.

End PredicateSubtyping.

(*************)
(* UIP for nat *)
(*************)

(* We can decide the equality on the natural numbers, so UIP should hold for
them. *)

Fixpoint nat_eq (n1 n2:nat)
  := match n1, n2 with
      | 0, 0 => true
      | S n1', S n2' => nat_eq n1' n2'
      | _ , _ => false
    end.

Lemma nat_eq_decide: forall (n1 n2: nat), true = nat_eq n1 n2 <-> n1 = n2.
Proof.
  induction n1.
  induction n2; simpl.
  split; done.
  split; [done | discriminate].
  induction n2; simpl.
  split; [done | discriminate].
  case: (IHn1 n2) => H0 H1.
  split.
  move => H2.
  rewrite H0 => //.
  move => H.
  injection H => H2.
  apply H1.
  done.
Qed.

Definition UIP_nat := Hedberg nat nat_eq nat_eq_decide.

Check UIP_nat.


(**************)
(* Univalence *)
(**************)

(* This is a concept that topologist like to have. *)

Record is_contr (T : Type) := IsContr {
  contr_elt : T;
  contr_eltE : forall x y : T, x = y}.

Definition fiber {A B : Type} (f : A -> B) (b : B) := {x : A & f x = b}.

Definition is_equiv {A B : Type} (f : A -> B) :=
  forall b : B, is_contr (fiber f b).

Definition equiv (A B : Type) := {f : A -> B & is_equiv f}.

Lemma id_is_equiv (A : Type) : is_equiv (fun x : A => x).
Proof.
move=> a.
apply: IsContr.
- exact: {{ a, eq_refl }}.
- move=> p q. case: p => x pax. case: q => y pay.
  destruct pax. destruct pay. apply: eq_refl.
Qed.

Definition univalence_fun {A B : Type} (p : A = B) : equiv A B.
Proof.
destruct p.
exists (fun x : A => x).
exact: id_is_equiv.
Defined.

Definition univalence (A B : Type) := is_equiv (@univalence_fun A B).

(************************************)
(* Univalence incompatible with UIP *)
(************************************)

Definition negation (b: bool) :=
  match b with
    | true => false
    | false => true
  end.

Lemma negneg: forall b, b = negation (negation b).
Proof.
  case => //.
Qed.

Lemma neg_is_equiv : is_equiv negation.
Proof.
move => b.
apply: IsContr.
- refine ({{ negation b, _ }}).
  case b => //.
- move=> p q.
  case: p => x pax. case: q => y pay.
  have H : (x=y).
  rewrite (negneg x) (negneg y) pax pay => //.
  move : pax pay.
  rewrite H => pax pay.
  rewrite (UIP_bool (negation y) b pax pay) => //.
Qed.

Lemma idEquiv: equiv bool bool.
Proof.
  exact {{ (fun x : bool => x), id_is_equiv bool }}.
Defined.

Lemma negEquiv: equiv bool bool.
Proof.
  exact {{ negation, neg_is_equiv }}.
Defined.

Theorem UniUIP: (UIP Type) -> (univalence bool bool) -> False.
Proof.
  move => UIPA.
  rewrite /univalence /is_equiv => H.
  move: (H idEquiv)(H negEquiv).
  case => u _ ; case => v _.
  case u => x.
  case v => y Hy.
  have H0:(x=y).
  apply UIPA.
  rewrite H0 Hy.
  rewrite /negEquiv /idEquiv.
  injection.
  intros.
  have J: true=false.
  rewrite (negneg false).
  rewrite{1} H2 => //.
  apply distinct => //.
Qed.



(**********************************************************)
(* Now let's point out some subtleties of Dependent types *)
(**********************************************************)

Print list.

(* Most natural example of a dependent type: a type for lists of
length n *)

Inductive nlist (A:Type) : nat -> Type :=
| nnil: nlist A 0
| ncons: forall n, A -> nlist A n -> nlist A (S n)
.

Print plus.
Compute (fun n => plus 0 n).
Check (fun A n (l : nlist A (plus 0 n)) => (l : nlist A n) ).

(* Try this: *)
(* Check (fun A n (l : nlist A (plus n 0)) => (l : nlist A n) ). *)
(* Why does it complain? *)

Compute (fun n => plus n 0).

(* It's not the identity, but a fixpoint! It's because the way
addition is define is NOT symmetric in its 2 arguments. The following
lemma does require an induction (while the other way around was a
simple computation). *)

Lemma plus_n0: forall n, plus n 0 = n.
Proof.
  induction n.
  apply eq_refl.
  simpl.
  rewrite IHn.
  apply eq_refl.
Qed.

Print plus_n0.

Lemma nlist_n0: forall {A n}, nlist A (plus n 0) = nlist A n.
Proof.
  move => A n.
  rewrite plus_n0.
  apply eq_refl.
Qed.

(* If two types are equal, I can export the inhabitants of one as inhabitants of the other. *)

Lemma duh: forall A B:Type, A=B -> A -> B.
Proof.
  move => A B e x.
  rewrite <- e.
  exact x.
Qed.

(* But the export function is not the identity! *)

Print duh.

(* Let us redefine the export function manually: *)

Definition export {A B: Type} (e: A=B) (x:A)
  := match e in (_ = C) return C with
      | eq_refl => x
    end.

Check @export.

Print eq_sym.
Definition import {A B: Type} (e: A=B) := export (eq_sym e).
Check @import.

Section Export.
  Variable A:Type.
  Variable x:A.
  Compute (export eq_refl x).

  Variable n: nat.
  Variable l: nlist A (plus n 0).
  Compute (export nlist_n0 l).

  (* This time, the result of the export is not the identity, it's a
proper cast of the list l in the type (nlist A n) *)

End Export.

(* Is it a bug or a feature?
Answer: a feature.
The trouble with equalities is that you are free to assume that they
hold, as in the following example where we assume the absurd equality
AT = (AT -> AT) *)

Section UntypedLambdaCalculus.
  Variable AT : Type.
  Variable e: AT = (AT -> AT).
  (* Assuming this stupid equality, we try to emulate the non-terminating untyped lambda-term
  (lambda x.x x) (lambda x.x x) *)
  Definition delta: AT := import e (fun x: AT => (export e x) x).
  Check delta.
  Check ((export e delta) delta).
  Compute ((export e delta) delta).

  (* Fortunately for us, the simulation of the infinite reduction of
(lambda x.x x) (lambda x.x x) blocks on the pattern-matching of the free
variable e, the assumed proof of the stupid equality. Computation is
blocked until we provide a proof of that equality (which will never
happen). *)

End UntypedLambdaCalculus.

(* Still, this feature may be frustrating: *)

Section Frustration.

  Variable A: Type.

  Record nList :=
    {
      length : nat;
      actual_list : nlist A length
    }.

  Variable l1 l2: nList.
  Hypothesis H : l1 = l2.

  Theorem list_eq_length: l1.(length) = l2.(length).
  Proof.
    rewrite H.
    exact eq_refl.
  Qed.

  (* Let's try to prove: *)
  (* Theorem list_eq: l1.(actual_list) = l2.(actual_list). *)
  (* We can't even state it! The two sides of the equality live in
  different types! *)

  Lemma types_eq : nlist A l1.(length) = nlist A l2.(length).
  Proof.
    rewrite H.
    exact eq_refl.
  Defined.

  Check l1.(actual_list) = import types_eq (l2.(actual_list)).


  (* We would like to be able to state an equality between two
  elements living in different types, even though the equality may
  only hold / be provable in the case the types are the same. This
  equality is called the John Major equality. *)

  Section JMEq.

    Print eq.

    Inductive JMeq {A : Type} (x : A) : forall {B : Type}, B -> Prop :=
    | JMeq_refl : JMeq x x.

    Theorem list_eq: JMeq l1.(actual_list) l2.(actual_list).
    Proof.
      rewrite H.
      apply JMeq_refl.
    Defined.

    (* When the two types are the same, we would like John Major
    equality to behave like the standard equality. *)

    Theorem JMeq_eq : forall (B:Type)(x y:B), JMeq x y -> x = y.
    Proof.
      move => B x y H0.
      (* rewrite H0.  *)
      (* case H0.  *)
      (* destruct H0.   *)
      Abort.

    (* Bad news: the above theorem is equivalent to K, so it is not
    provable in the Calculus of Constructions *)

  End JMEq.

End Frustration.
