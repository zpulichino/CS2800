
/- Problem 1: Append and Reverse -/

/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

/- Note that we again define our own append reverse, 
this time using the built in types -/

-- part p1
def app : List Nat -> List Nat -> List Nat
  | List.nil,       bs => bs
  | List.cons a as, bs => List.cons a (app as bs)

def rev : List Nat -> List Nat 
  | List.nil => List.nil
  | List.cons a L => app (rev L) (List.cons a List.nil) 

-- 6 lines
theorem app_nil : forall (l : List Nat), app l [] = l := 
  by intros l 
     induction l
     case nil => rfl
     case cons x xs ih =>
     simp only [app]
     rw [ih]

-- 6 lines
theorem app_assoc : forall (l1 l2 l3 : List Nat),
  app (app l1 l2) l3 = app l1 (app l2 l3) := 
 by intros l3
    induction l3
    case nil =>
      intros l1 l2
      rfl 
    case cons l3 IH =>
      intros l1 l2
      simp only [app]
      rw [IH]

-- 8 lines
theorem rev_app_distr: forall l1 l2 : List Nat,
  rev (app l1 l2) = app (rev l2) (rev l1) := 
 by intros l1 l2
    induction l1
    case nil => 
      simp only [app]
      simp only [rev]
      rw [app_nil]
    case cons h t IH =>
      simp only [rev]
      rw [IH]
      rw [app_assoc]

-- 8 lines
theorem rev_involutive : forall l : List Nat,
  rev (rev l) = l := 
 by intros l
    induction l
    case nil => rfl
    case cons h t IH => 
      simp only [rev]
      rw [rev_app_distr]
      rw [IH]
      rfl
-- part p1


/- Problem 2: Evenness (and Relations) -/

/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

-- part p2
inductive ev : Nat -> Prop 
| O : ev 0
| SS (n : Nat) (H : ev n) : ev (Nat.succ (Nat.succ n))

def double : Nat -> Nat
| 0 => 0
| Nat.succ n => Nat.succ (Nat.succ (double n))

-- 5 lines
theorem ev_double : forall n, ev (double n) := 
 by intro n
    induction n <;> simp only [double]
    constructor
    apply ev.SS
    assumption


-- 15 lines
theorem ev_sum : forall n m, ev n -> ev m -> ev (Nat.add n m) := 
 by intros n m evn evm
    induction evm 
    case O => 
      simp only [Nat.add] 
      assumption
    case SS =>
    apply ev.SS
    assumption

-- 3 lines
theorem three_not_ev : Not (ev 3) := 
 by intro n
    cases n
    contradiction

inductive ev' : Nat -> Prop :=
  | O : ev' 0
  | SSO : ev' 2
  | sum n m (Hn : ev' n) (Hm : ev' m) : ev' (Nat.add n m)

-- 21 lines
theorem ev'_ev : forall n, ev' n <-> ev n := 
 by intro n
    constructor
    case mp =>
      intros ev'n
      induction ev'n
      case O => 
        apply ev.O 
      case SSO =>
        apply ev.SS
        apply ev.O
      case sum =>
      apply ev_sum
      assumption
      assumption
    case mpr =>
      intros evn
      induction evn
      case O => 
        apply ev'.O
      case SS =>
        rw [Nat.succ_eq_add_one]
        rw [Nat.add_assoc]
        apply ev'.sum
        assumption
        apply ev'.SSO

-- part p2

/- Problem 3: Subsequences -/

/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

-- part p3
inductive subseq : List Nat -> List Nat -> Prop
| empty : subseq [] []
| include x l1 l2 (H : subseq l1 l2) : subseq (x::l1) (x::l2)
| skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x::l2)

-- 6 lines
theorem subseq_refl : forall (l : List Nat), 
  subseq l l :=
 by intros l
    induction l
    case nil => apply subseq.empty
    case cons x xs IH => apply subseq.include x xs xs IH

-- 5 lines
theorem subseq_empty : forall l, subseq [] l := 
 by intros l
    induction l
    case nil => apply subseq.empty
    case cons x xs IH => apply subseq.skip x [] xs IH

-- 13 lines
theorem subseq_app : forall (l1 l2 l3 : List Nat),
  subseq l1 l2 ->
  subseq l1 (List.append l2 l3) :=
 by intros l1 l2 l3 IH 
    induction IH 
    case empty => apply subseq_empty l3
    case include x l1' _ H' =>
      apply subseq.include
      apply H'
    case skip x l1' _ H' =>
      apply subseq.skip
      apply H'
-- part p3

/- Problem 4: Insertion Sort -/


/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

-- part p4
def insert : Nat -> List Nat -> List Nat
| y, [] => [y]
| y, x::xs => if Nat.ble y x 
              then y :: x :: xs 
              else x :: insert y xs

def isort : List Nat -> List Nat
| []      => []
| x :: xs => insert x (isort xs) 

inductive All : {T : Type} -> (T -> Prop) -> List T -> Prop
| nil : All P []
| cons : forall x L, P x -> All P L -> All P (x :: L)

inductive Sorted : List Nat -> Prop
| nil : Sorted []
| cons : forall n l, Sorted l -> 
                     All (Nat.le n) l ->
                     Sorted (n :: l)


theorem all_trans : forall (P : T -> Prop) (Q : T -> Prop) L,
  All P L ->
  (forall x, P x -> Q x) ->
  All Q L := 
 by intros P Q L Hall PtoQ
    induction Hall
    case nil => constructor
    case cons HL =>
      constructor
      apply PtoQ
      assumption
      assumption

-- 23 lines
theorem insert_le : forall n x l,
  All (Nat.le n) l ->
  Nat.le n x ->
  All (Nat.le n) (insert x l) := 
 by intros n x l alen nlex 
    induction alen
    case nil =>
      simp only [insert]
      constructor
      assumption
      constructor
    case cons  =>
      simp only [insert]
      generalize hyp : Nat.ble x ‹Nat› = B
      cases B
      case false =>
        simp only [ite_false]
        constructor
        assumption
        assumption
      case true =>
        simp only [ite_true]
        constructor
        assumption
        constructor
        assumption
        assumption


theorem ble_inv : forall a b, 
                  Nat.ble a b = false
               -> Nat.ble b a = true := 
 by intros a b H
    rw [Nat.ble_eq]
    cases (Nat.le_total b a)
    assumption
    rw [<- Nat.not_lt_eq]
    rw [<- Bool.not_eq_true] at H
    rw [Nat.ble_eq] at H
    contradiction

-- 37 lines
theorem insert_sorted : forall x l, 
  Sorted l ->
  Sorted (insert x l) := 
 by intros x l sortedl 
    induction sortedl
    case nil =>
      constructor
      constructor
      constructor
    case cons x' l' sortedl' IH1 IH2 =>
      simp only [insert]
      generalize Hyp : Nat.ble x x' = B
      cases B
      case false =>
        simp only [ite_false]
        constructor
        assumption
        apply insert_le
        assumption
        apply Nat.le_of_ble_eq_true
        apply ble_inv
        assumption
      case true =>
        simp only [ite_true]
        constructor
        constructor
        assumption
        assumption
        constructor
        apply Nat.le_of_ble_eq_true
        assumption
        apply all_trans
        assumption
        intros x1 nle
        induction nle
        case a.a.a.refl =>
          apply Nat.le_of_ble_eq_true
          assumption
        case a.a.a.step nle2 =>
          constructor
          assumption

-- 8 lines
theorem isort_sorted : forall l, Sorted (isort l) :=
 by intros l
    induction l
    case nil => constructor 
    case cons ht ln H => rw[isort]
                         apply insert_sorted
                         assumption

inductive Permutation : {T : Type} -> List T -> List T -> Prop
| nil   : Permutation [] []
| skip  : forall (x : A) (l l' : List A),
          Permutation l l' ->
          Permutation (x :: l) (x :: l')
| swap  : forall (x y : A) (l : List A),
          Permutation (y :: x :: l) (x :: y :: l)
| trans : forall l l' l'' : List A,
          Permutation l l' ->
          Permutation l' l'' ->
          Permutation l l''

example : Permutation [true,true,false] [false,true,true] :=
 by apply Permutation.trans (l' := [true,false,true])
    . apply Permutation.skip
      apply Permutation.swap
    . apply Permutation.swap

-- 6 lines
theorem perm_refl : forall {T : Type} (l : List T), 
  Permutation l l := 
 by intros t l 
    induction l
    case nil =>
     apply Permutation.nil
    case cons x xs ih =>
    constructor 
    assumption

-- 10 lines
theorem perm_length : forall {T : Type} (l1 l2 : List T), 
  Permutation l1 l2 -> l1.length = l2.length :=
 by intros t l1 l2 Perml1l2
    induction Perml1l2
    case nil => constructor
    case skip p l => 
      simp
      assumption
    case swap => constructor 
    case trans p1 p2 => 
      rw [p1]
      assumption

-- 12 lines
theorem perm_sym : forall {T : Type} (l1 l2 : List T), 
  Permutation l1 l2 -> Permutation l2 l1 :=
 by intros t L1 L2 Perm
    induction Perm
    case nil =>
      constructor
    case skip =>
      constructor
      assumption
    case swap =>
      constructor
    case trans =>
      constructor
      assumption
      assumption

-- 18 lines
theorem insert_perm : forall x l, 
  Permutation (x :: l) (insert x l) :=
 by intros x l 
    induction l
    case nil => simp only[insert]
                constructor
                constructor
    case cons f r ih => simp only [insert]
                        generalize H : Nat.ble x f = Z
                        cases Z
                        case true => simp
                                     apply perm_refl
                        case false => simp 
                                      apply Permutation.trans (l' := (f :: x :: r))
                                      apply Permutation.swap
                                      apply Permutation.skip
                                      assumption

-- 10 lines
theorem isort_perm : forall l, Permutation l (isort l) :=
 by intros l
    induction l
    case nil => 
      simp only [isort]
      constructor
    case cons h t IH =>
      constructor
      apply Permutation.skip
      assumption
      simp only [isort]
      apply insert_perm

-- part p4
