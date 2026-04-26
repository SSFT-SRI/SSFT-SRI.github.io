(*
This Coq script is made for Coq 8.5 and coq-mathcomp-ssreflect 1.6
Both available on opam with repository https://coq.inria.fr/opam/released

For Coq 8.4, it should work by just changing the first line to
Require Import ssreflect ssrbool eqtype ssrnat.
 *)

>From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
Require Import List.

(* Code we would write in ML:

   let rec insert n l =
     match l with
       | [] -> [n]
       | head::tail -> if n <= head then n::head::tail
                       else head::(insert n tail)

   let rec sort l =
     match l with
       | [] -> []
       | head::tail -> insert head (sort tail)
*)

(* Programming by proving. Simple version. *)

Definition insert (n:nat) (l:list nat) : list nat.
Proof.
  elim:l => [|head tail rec_res].
    exact (n::nil).
  case h:(n <= head).
    exact (n::head::tail).
  exact (head::rec_res).
Defined.

Compute (insert 5 (1::2::3::4::6::7::8::9::nil)).
Compute (insert 5 (1::2::3::4::nil)).

Definition sort (l:list nat) : list nat.
Proof.
  elim:l => [|head tail rec_res].
    exact nil.
  exact (insert head rec_res).
Defined.

Compute (sort (7::9::5::3::0::4::2::1::8::6::nil)).


(* Programming by proving. This time with full specs.

We need to express what it means for a list to be sorted and to be a
permutation of another list. The corresponding functions sorted and
permutation, together with the two functions smaller and remove on
which they rely, will not be used for the sorting computation, but
just to write down the specifications. They constitute is "ghost
code". *)



(* First, we need to define for a list of integers what it means to be
   sorted: each element is smaller than all the following elements *)

Fixpoint smaller n l : Prop :=
  match l with
    | nil => true
    | head::tail => n <= head /\ smaller n tail
  end.

Lemma smaller_trans n a l :
  smaller a l -> n <= a -> smaller n l.
Proof.
  elim:l => /=.
    done.
  move => b l ih [h1 h2] h3.
  split.
    move/(_ a n b):leq_trans => h4.
    by apply:h4.
  by apply:ih.
Defined.

Fixpoint sorted l : Prop :=
  match l with
    | nil => true
    | head::tail => smaller head tail /\ sorted tail
  end.

Fixpoint remove a (l:list nat) :=
  match l with
    | nil => None
    | head::tail =>
      if a == head then
        Some tail
      else
        match remove a tail with
          | Some tail' => Some (head::tail')
          | None => None
        end
  end.

Fixpoint permutation l1 l2 : Prop :=
  match l1, l2 with
    | nil, nil => true
    | nil, _ => false
    | head::tail, _ =>
      match remove head l2 with
        | Some l2' => permutation tail l2'
        | None => false
      end
  end.

Lemma permutation_refl l: permutation l l.
Proof.
  elim:l => [|head tail ihtail].
  simpl.
  done.
  simpl.
  rewrite eq_refl.
  done.
Defined.


Definition insert_fullspecs n l :
  {l' |
    (forall a, smaller a l -> a <= n -> smaller a l') /\
    (remove n l' = Some l) /\
    (sorted l -> sorted l' /\ permutation (n::l) l')}.
Proof.
  elim:l => [|head tail [l4 [ih1 [ih2 ih3]]]].
  exists (n::nil) => /=.
    split.
      done.
    rewrite eq_refl =>/=.
    done.
  case h:(n <= head).
    exists (n::head::tail).
    split => /=.
    done.
    do ? (rewrite ?eq_refl=>/=).
    split => //=.
    move => [h1 h2].
    split.
      do 2 (split => //).
      apply:(smaller_trans _ _ _ h1 h).
    apply:permutation_refl.
  exists (head::l4).
  split.
    move => a [h1 h2] h3.
    by split ; [ | apply:ih1 ].
  split => /=.
    rewrite gtn_eqF.
      by rewrite ih2.
    by rewrite ltnNge h.
  move => [h1 h2].
  split.
    move/(_ h2):ih3 => /= [h3 _].
    split => //.
    apply:ih1 => //.
    move:(leq_total n head).
    by rewrite h.
  rewrite gtn_eqF.
    rewrite ih2 /= eq_refl.
    apply:permutation_refl.
  by rewrite ltnNge h.
Defined.


Definition sort_fullspecs (l:list nat) :
  {l' | sorted l' /\ permutation l l'}.
Proof.
  elim:l => [|head tail [rec_res [ih1 ih2]]] /=.
    exists nil => //.
  Check (insert_fullspecs head rec_res).
  case:(insert_fullspecs head rec_res)
  => [insert_result [_ [h2 h3]]].
  exists insert_result.
  move/(_ ih1):h3 => [h4 _].
  split => //.
  rewrite h2.
  apply:ih2.
Defined.

(* Now we can extract OCaml code out of the proof-terms *)

Extraction Language Ocaml.
Set Extraction AccessOpaque.


Extraction "insert_sort.ml" sort_fullspecs.
