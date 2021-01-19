
(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool List.

Set Implicit Arguments.

Axiom todo : forall {A}, A.
Ltac todo := by apply: todo.

(* ==================================================================== *)
(* This template contains incomplete definitions that you have to       *)
(* fill. We always used the keyword `Definition` for all of them but    *)
(* you are free to change for a `Fixpoint` or an `Inductive`.           *)
(*                                                                      *)
(* If needed, it is perfectly fine to add intermediate definitions and  *)
(* local lemmas.                                                        *)

(* ==================================================================== *)
(* In this project, we are going to develop and prove correct an        *)
(* algorithm for deciding the membership of a word w.r.t. a given       *)
(* regular language - all these terms are going to be defined below     *)

(* This project lies in the domain of *formal languages*. The study     *)
(* of formal languages is a branch of theoretical computer science and  *)
(* is about that is interested in the purely syntactical aspects of     *)
(* of languages and as applications in different domains, ranging from  *)
(* the definition of  the grammar of programming languages to the field *)
(* of automated translation.                                            *)

(* As with natural languages, we first need to fix an alphabet. In our  *)
(* case, we are simply going to declare a type `A : Type` - i.e. we     *)
(* will use the same alphabet for all the formal languages we are going *)
(* to study. Inhabitants of `A` are called `letters`.                   *)

Parameter (A : Type).

(* -------------------------------------------------------------------- *)
(* A `word` is then simply a finite sequence of letters of `A`. We      *)
(* denote by A* the set of words over `A`. In Coq, we are going to      *)
(* represent words as lists whose elements are inhabitants of `A`. This *)
(* naturally leads to the following definition:                         *)

Notation word := (list A).

(* -------------------------------------------------------------------- *)
(* You can get an overview of the List library at the following URL:    *)
(* https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html      *)

(* -------------------------------------------------------------------- *)
(* In this setting, a `language` is simply a subset of A*. Assuming     *)
(* that `x` & `y` are letters of A, we can define the following         *)
(* languages:                                                           *)
(*                                                                      *)
(*  - the empty language: `L = ∅`;                                      *)
(*                                                                      *)
(*  - the language that contains only the empty word ε (i.e. the only   *)
(*    (word of length 0): L = {ε}`;                                     *)
(*                                                                      *)
(*  - the language that contains all the words solely composed of the   *)
(*    letter `x`: L = { ε, x, xx, xxx, ... } = { xⁿ | n ∈ ℕ } (here,    *)
(*    xⁿ stands for the word x…x, where x is repeated n times);         *)
(*                                                                      *)
(*  - the language that contains all the words of the form xⁿyⁿ:        *)
(*    L = { xⁿyⁿ | n ∈ ℕ };                                             *)
(*                                                                      *)
(*  - if we assume that A contains the letter '[' & ']', we can         *)
(*    define the language of well-balanced words for '[' & ']':         *)
(*    L = { w ∈ { [, ] }* | s.t. P(w) && Q(w) }, where                  *)
(*      - P(w) = any prefix of w contain no more ]'s then ['s           *)
(*      - Q(w) = the number of ['s and ]'s of w are equal.              *)

(* --------------------------------------------------------------------      *)
(* We can also combine languages to form other languages. For example,       *)
(* if L and G are languages, we can define:                                  *)
(*                                                                           *)
(*  - the union of L & G            L ∪ G                                    *)
(*  - the concatenation of L & G    { w1 · w2 | w1 ∈ L, w2 ∈ G }             *)
(*  - the intersection of L & G     L ∩ G                                    *)
(*  - the complement of L           A* \ L                                   *)
(*  - the Kleene closure of L       L* = { w_1 ... w_n | n \in ℕ, w_i ∈ L }  *)
(*  - the mirror of L               rev(L) = { rev(w) | w ∈ L }              *)

(* -------------------------------------------------------------------- *)
(* To define languages in Coq, we need a way to represent subsets       *)
(* of A*, i.e. subsets of the set of `word`'s. To that end, we are      *)
(* going to represent a set using its indicator function. (We remind    *)
(* that, given a subset F of an ambient set E, the indicator function   *)
(* of F is the function f_E from E to { ⊤, ⊥ } s.t.                     *)
(*                                                                      *)
(*                     f_E(x) = ⊤ iff x ∈ E                             *)

(* In Coq, the codomain of its indicator function is going to be a      *)
(* proposition: given a function `F : E -> Prop`, we say that x belongs *)
(* to `x` iff `f x` holds.                                              *)

Notation language := (word -> Prop).


(* -------------------------------------------------------------------- *)
(* From now use, we assume that L, G, H denote languages, x, y denote   *)
(* letters and that and w denotes a word.                               *)

Implicit Types (L G H : language) (x y : A) (w : word).

(* -------------------------------------------------------------------- *)
(* From there, we can define the following languages                    *)

(* The empty language: no words belong to it.                           *)
(* (its indicator function always return `False`)                       *)
Definition lang0 : language :=
  fun w => False.

(* The language that only contains the empty word.                      *)
Definition lang1 : language :=
  fun w => w = nil.

(* Q1. We now ask you to define the following languages                 *)

(*  Given a word `w0`, the language that only contains the word `w0`.   *)
(* EXPL: you check if the input word is exactly w0 *)
Definition langW w0 : language := 
  fun w => w = w0.

(* Given a sequence `ws` of words, the language that contains all the   *)
(* the words `ws` and only these words.                                 *)

(* EXPL: for all the words you check if they are in the desired ws list *)
Definition langF (ws : list word) : language := 
  fun w => In w ws.

(* Given a letter `x`, the language that only contains the letter `x`   *)
(* seen as a word of length 1.                                          *)

(* EXPL: since x is an input letter, you check if the word w is equal to
x in word form. But x is not in word form yet, so you append it to an
empty list (nil) and check*)
Definition langA x : language := 
  fun w => w = (cons x nil).

(* The union of the two languages `L` and `G`.                          *)
(* EXPL: if w is in L or in G then it is in their union *)
Definition langU L G : language := 
  fun w => L w \/ G w.

(* The intersection of the two languages `L` and `G`.                   *)
(* EXPL: if w is in L and G then it is in their intersection *)
Definition langI L G : language := 
  fun w => L w /\ G w.

(* The concatenation of the two languages `L` and `G`.                  *)
(* the concatenation of L & G    { w1 · w2 | w1 ∈ L, w2 ∈ G }           *)
(* EXPL: check if w = w1 + w2 and check the condition on the right (shown above) *)
Definition langS L G : language := 
  fun w => exists w1 w2, (app w1 w2) = w /\ L w1 /\ G w2.

(* The Kleene closure of the language `L`                               *)
(* the Kleene closure of L       L* = { w_1 ... w_n | n \in ℕ, w_i ∈ L }  *)
(* EXPL: the nicest way to do this is with an inductive def. Conceptually,
 the closure is all possible concatenations, so for instance if I have 
 L = {a} then L* = nil, a, aa, aaa, aaaa, etc, for all n. Then the stuff
 below can be deduced intuitively. Another example, if L = {a,b} then 
 a is clearly in the closure, b is clearly in the closure, then ab is also
 clearly in the closure (as it is a concatenation of two words in l, of 
 total length 2. *)
Inductive langK L : language := 
  | langK_nil : langK L nil (* the empty word is in the closure *)
  | langK_one : forall w, L w -> langK L w (* if w is in L then it is in the closure *)
(* if w1 is in the closure then [ if w2 is in the closure, then the concatenation of them
  is in the closure] *)
  | langK_two : forall w1 w2, langK L w1 -> langK L w2 -> langK L (w1 ++ w2). 

(* The mirror of the language `L` (You can use the `rev`, that reversed *)
(* a list, from the standard library. *)
(*  - the mirror of L               rev(L) = { rev(w) | w ∈ L } *)
(* EXPL: to check if a word is in the reverse language, we can check if its reverse 
(kinda like the reverse of the reverse) is in the "original" language. Eg: if 
L = {"apple"} and M (the reverse) = {"elppa"}, to check if "elppa" is in M we 
check if "apple" is in L *)
Definition langM L : language := 
  fun w => L (rev w).

(* -------------------------------------------------------------------- *)
(* Given two languages, we will consider `L` & `G` equal iff they       *)
(* contain the same words:                                              *)

Definition eqL L G := forall w, L w <-> G w.

Infix "=L" := eqL (at level 90).

(* Q2. Prove the following equivalances:                                *)

Lemma concat0L L : langS lang0 L =L lang0.
(* concatenation, empty lang, L = L, empty lang *)
Proof.
split.
unfold lang0. unfold langS. (* write according to definition *)
move => [w1 [w2 h]]. (*says that (_:word) and w2 are words, and sets False /\ L w2 as the hyp *)
apply h. (* false is not provable alone, so we use h1. this works because false -> false and false -> true *)
(* i.e. prop starting w false is always true *)
unfold lang0. done. (* done tries to solve by trivial means, which works because we have false -> false *)
Qed.

Lemma concatL0 L : langS L lang0 =L lang0.
Proof. 
(* follows the same logic as the one above.*)
split.
unfold lang0. unfold langS.
move => [w1 [w2 h]]. apply h. 
(*h is now the other way around but we will either get true /\ false or false /\ false which are both false*)
(* so we can still use h*)
unfold lang0. done.
Qed.

Lemma concat1L L : langS lang1 L =L L.
Proof.
split.
unfold lang1. unfold langS.
move => [w1 [w2 [h1 [h2 h3]]]].
rewrite h2 in h1. simpl in h1. rewrite h1 in h3.
apply h3.
unfold lang1. unfold langS.
move => h.
exists nil. exists w.
done.
Qed.

(*************************** TO FINISH ********************)
Lemma concatL1 L : langS L lang1 =L L.
Proof. 
split.
unfold lang1. unfold langS.
move => [w1 [w2 [h1 [h2 h3]]]].
rewrite h3 in h1. rewrite app_nil_r in h1. rewrite h1 in h2.   (* app_nil_r says that l ++ [] = l *)
apply h2.
unfold lang1. unfold langS.
move => h.
exists nil. exists w.
split. trivial. (*to be continued*)
Admitted.
(* ---------------------------------------------------------- *)

(************************* TO DO ****************************)
Lemma concatA L G H : langS (langS L G) H =L langS L (langS G H).
Proof.
split.
(* TO DO *)
Admitted.
(* ---------------------------------------------------------- *)

Lemma unionC L G : langU L G =L langU G L.
Proof.
split. unfold langU.
case. (* because of the "or" *)
move => h1. right. apply h1.
move => h2. left. apply h2.
unfold langU.
case.
move => h3. right. apply h3.
move => h4. left. apply h4.
Qed.


Lemma interC L G : langI L G =L langI G L.
Proof.
split.
unfold langI.
split. (* because of the "and" *)
apply H. apply H.
unfold langI.
split.
apply H. apply H.
Qed.

Lemma langKK L : langK (langK L) =L langK L.
Proof.
split.
move => h. induction h. (* so we can use the inductive def from earlier!! *)
apply langK_nil. apply H.
apply langK_two. apply IHh1. apply IHh2. (* both apply and assumption would work here *)
apply langK_one.
Qed.

(* Note that, since languages are represented as indicator functions    *)
(* over `Prop`, we cannot assess that `L =L G` implies `L = G`.         *)

(* ==================================================================== *)
(*                          REGULAR LANGUAGES                           *)

(* We are now interested in a subclass of languages called "regular     *)
(* languages": a language `L` is said to be regular iff one of the      *)
(* following holds:                                                     *)
(*                                                                      *)
(*  - L = ∅ or L = {ε} or L = {x} for some x ∈ A ;                      *)
(*  - L = L1 ∪ L2 for L1, L2 regular languages ;                        *)
(*  - L = L1 · L2 for L1, L2 regular languages ;                        *)
(*  - L = G* for G a regular language.                                  *)

(* This kind of inductive definitions can be encoded in Coq using       *)
(* an inductive predicate `regular : language -> Prop` s.t.             *)
(*                                                                      *)
(*             L is regular iff `regular L` holds                       *)

(* Q3. complete the following definition of the predicate `regular`:    *)

Inductive regular : language -> Prop :=
  (* Any language equivalent to a regular language is regular *)
| REq L G of regular L & G =L L : regular G

  (* The empty language is regular *)
| REmpty : regular lang0
| RVoid : regular lang1

(* TODO: to be completed *)
.

(* -------------------------------------------------------------------- *)
(* Q4. prove that `langW w` is regular.                                 *)
Lemma regularW w : regular (langW w).
Proof. todo. Qed.

(* -------------------------------------------------------------------- *)
(* Q5. prove that `langM L` is regular, given that L is regular.        *)
Lemma regularM L : regular L -> regular (langM L).
Proof. todo. Qed.

(****************** CAROLINA WILL DO THE SECTION ABOVE ******************************)
(* I figured it was better if we split in half so we don't end up redoing the same 
things twice or accidentally overwriting each other's code*)

(* ==================================================================== *)
(*                        REGULAR EXPRESSIONS                           *)

(* Related to regular languages is the notion of regular expressions.   *)
(* A regular expression is a formal, syntactic expression that can      *)
(* latter be interpreted as a regular language. Regular expressions are *)
(* pervasive in computer science, e.g. for searching for some text in   *)
(* a file, as it is possible with the `grep` command line tool.         *)
(*                                                                      *)
(* For instance, the command:                                           *)
(*                                                                      *)
(*    grep -E 'ab*a' foo.txt                                            *)
(*                                                                      *)
(* is going to print all the lines of `foo.txt` that contains a word    *)
(* of the form ab⋯ba (where the letter b can be repeated 0, 1 or more   *)
(* time. I.e., grep is going to find all the lines of `foo.txt` that    *)
(* contains a word that belongs in the formal language:                 *)
(*                                                                      *)
(*    L = { abⁿa | n ∈ ℕ }                                              *)
(*                                                                      *)
(* If you need to convince yourself that L is regular, note that:       *)
(*                                                                      *)
(*    L = { a } ∪ { b }* ∪ { a }                                        *)
(*                                                                      *)
(* In some sense, a regular expression is just a compact way to         *)
(* represent a regular language, and its definition is going to be      *)
(* close to the one of regular languages.                               *)
(*                                                                      *)
(* A regular expression is either:                                      *)
(*                                                                      *)
(*  - the constant ∅ or the constant ε or one letter from A             *)
(*  - the disjunction r1 | r2 of two regular expressions                *)
(*  - the concatenation r1 · r2 of two regular expressions              *)
(*  - the Kleene r* of some regular expression                          *)

(* We can represent regular expressions as a inductive type in Coq.     *)

(* Q6. complete the following definition:                               *)

Inductive regexp : Type :=
| RE_Empty : regexp
| RE_Void  : regexp
| RE_Atom  : A -> regexp
| RE_Disjunction : regexp -> regexp -> regexp
| RE_Concat  : regexp -> regexp -> regexp
| RE_Kleene  : regexp -> regexp
  (* TO BE COMPLETED *)
.

Implicit Types (r : regexp).

(* We now have to formally related regular expressions to regular       *)
(* languages. For that purpose, we are going to interpret a regular     *)
(* expression as a languages. If r is a regular expression, then we     *)
(* denote by language [r] as follows:                                   *)
(*                                                                      *)
(*   - [∅]       = ∅                                                    *)
(*   - [ε]       = ε                                                    *)
(*   - [a]       = { a } for a ∈ A                                      *)
(*   - [r₁ ∪ r₂] = [r₁] ∪ [r₂]                                          *)
(*   - [r₁ · r₂] = [r₁] · [r₂]                                          *)
(*   - [r*]      = [r]*                                                 *)

(* Q7. implement the Coq counterpart of the above definition:           *)

Fixpoint interp (r : regexp) {struct r} : language :=
  match r with
  | RE_Empty => lang0
  | RE_Void => lang1
  | RE_Atom A => langA A
  | RE_Disjunction r1 r2 => langU (interp r1) (interp r2)
  | RE_Concat r1 r2 => langS (interp r1) (interp r2)
  | RE_Kleene regexp => langK (interp regexp)
  end.

(* Q8. show that the interpretation of a regular expression is a        *)
(*     regular language:                                                *)

Lemma regular_regexp r : regular (interp r).
Proof. case r. simpl. apply REmpty. simpl. apply RVoid. todo. todo. todo. todo. Qed.

(* Q9. show that any regular language can be interpreted as a           *)
(*     regular expression:                                              *)

Lemma regexp_regular L : regular L -> exists r, L =L interp r.
Proof. todo. Qed.

(* Of course, it may happen that two regular expressions represent      *)
(* the same language: r1 ~ r2 iff [r1] = [r2].                          *)

(* Q10. write a binary predicate eqR : regexp -> regexp -> Prop s.t.    *)
(*      eqR r1 r2 iff r1 and r2 are equivalent regexp.                  *)

Definition eqR (r1 r2 : regexp) : Prop := 
  forall w, (interp r1) w <-> (interp r2) w.

Infix "~" := eqR (at level 90).

(* Q11. state and prove the following regexp equivalence:               *)
(*           (a|b)* ~ ( a*b* )*                                         *)
Lemma Q11 (a b: regexp) : RE_Kleene (RE_Disjunction a b) ~ RE_Kleene( RE_Concat (RE_Kleene (a)) (RE_Kleene (b))).
Proof. todo. Qed.

(* ==================================================================== *)
(*                          REGEXP MATCHING                             *)

(* We now want to write a algorithm for deciding if a given word `w`    *)
(* matches a regular expression `r`, i.e. for deciding wether `w ∈ [r]` *)
(*                                                                      *)
(* For that purpose, we are going to use Brzozowski's derivatives.      *)
(*                                                                      *)
(* The idea of the algorithm is the following:                          *)
(*                                                                      *)
(* Given a letter `x` and an regular expression `r`, the Brzozowski's   *)
(* derivatives of `x` w.r.t. `r` is a regular expression x⁻¹·r s.t.     *)
(*                                                                      *)
(*    x · w ∈ [r] ⇔ w ∈ [x⁻¹·r]                                         *)
(*                                                                      *)
(* Assuming that we can compute a Brzozowski's derivative for any       *)
(* letter `x` and regular expression `r`, one can check that a word `w` *)
(* matches a regexp `r` as follows:                                     *)
(*                                                                      *)
(*   - if w = x · w' for some letter x and word w', we recursively      *)
(*     check that `w` matches `x⁻¹·r`; otherwise                        *)
(*   - if w = ε, then we directly check that [r] contains the empty     *)
(*     word - a property that is deciable.                              *)

(* Q12. write a nullity test `contains0` : regexp -> bool s.t.          *)
(*                                                                      *)
(*      ∀ r, contains0 r ⇔ ε ∈ [e]                                      *)

Fixpoint contains0 (r : regexp) : Prop :=
  match r with
  | RE_Void => true
  | RE_Empty => false
  | RE_Atom A => false
  | RE_Kleene r1 => contains0 r1
  | RE_Disjunction r1 r2 => contains0 r1 \/ contains0 r2
  | RE_Concat r1 r2 => contains0 r1 \/ contains0 r2
  end.
  
(* Q13. prove that your definition of `contains0` is correct:           *)


Lemma contains0_ok r : contains0 r <-> interp r nil.
Proof. case r. simpl. split. discriminate. todo. simpl. split. todo. todo. todo. todo. todo. todo. Qed.

(* We give below the definition of the Brzozowski's derivative:         *)
(*                                                                      *)
(*   - x⁻¹ · x         = ε                                              *)
(*   - x⁻¹ · y         = ∅ if x ≠ y                                     *)
(*   - x⁻¹ · ε         = ∅                                              *)
(*   - x⁻¹ · ∅         = ∅                                              *)
(*   - x⁻¹ · (r₁ | r₂) = (x⁻¹ · r₁) | (x⁻¹ · r₂)                        *)
(*   - x⁻¹ · (r₁ · r₂) = (x⁻¹ · r₁) · r₂ | E(r₁) · (x⁻¹ · r₂)           *)
(*   - x⁻¹ · r*        = (x⁻¹ · r) · r*                                 *)
(*                                                                      *)
(* where E(r) = ε if ε ∈ [r] & E(r) = ∅ otherwise.                      *)

(* Q14. write a function `Brzozowski` that computes a Brzozowski's      *)
(*      derivative as defined above.                                    *)
(*                                                                      *)
(* For that purpose, you may need to have a decidable equality over     *)
(* `A`. The parameter `Aeq` along with the axioms `Aeq_dec` give        *)
(* you such a decidable equality.                                       *)

Parameter Aeq : A -> A -> bool.

(* Here, `Aeq x y` has to be read as `Aeq x y = true`                   *)
Axiom Aeq_dec : forall (x y : A), Aeq x y <-> x = y.

Definition Brzozowski (x : A) (r : regexp) : regexp := todo.

(* Q15. write a function `rmatch` s.t. `rmatch r w` checks wether a     *)
(*      word `w` matches a given regular expression `r`.                *)

Definition rmatch (r : regexp) (w : word) : bool := todo.

(* Q16. show that the `Brzozowski` function is correct.                 *)

Lemma Brzozowski_correct (x : A) (w : word) (r : regexp) :
  interp (Brzozowski x r) w -> interp r (x :: w).
Proof. todo. Qed.

(* Q17. show that `rmatch` is correct.                                  *)

Lemma rmatch_correct (r : regexp) (w : word):
  rmatch r w -> interp r w.
Proof. todo. Qed.

(* Q18. (HARD - OPTIONAL) show that `rmatch` is complete.               *)

Lemma rmatch_complete (r : regexp) (w : word):
  interp r w -> rmatch r w.
Proof. todo. Qed.
