namespace HW7

/-
Your task in this HW is to replace all instances of `sorry` with proofs without errors. If you aren't able to complete a proof, get as much done as you can, and leave `sorry` in the cases you cannot finish. Partial work is better than nothing!

For this assignment, we redefine the inductive types we will use, and the operations on them, in order to not have standard library automation & already proved theorems get in the way of the assignment. Later on, we will _use_ this automation, but for now, it will get in the way of learning how to prove theorems.

NOTE: For this HW, you cannot use the special List syntax: you must use List.nil & List.cons. You _can_ use number literals (0,1,2, etc) for Nat. 
-/

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

def natOfNat : _root_.Nat -> Nat
| _root_.Nat.zero => Nat.zero
| _root_.Nat.succ n => Nat.succ (natOfNat n)
-- N.B.: this is the magic that allows us to write numerals
-- instead of Nat.succ (Nat.succ ...). 
instance (n : _root_.Nat) : OfNat Nat n where
  ofNat := natOfNat n

def Nat.sub : Nat → Nat → Nat
  | a, 0      => a
  | 0, _      => 0 
  | Nat.succ a, Nat.succ b => Nat.sub a b

def Nat.add : Nat → Nat → Nat
  | Nat.zero, b   => b
  | Nat.succ a, b => Nat.succ (Nat.add a b)

def Nat.mul : Nat → Nat → Nat
  | _, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

def List.append : List α → List α → List α
  | List.nil,       bs => bs
  | List.cons a as, bs => List.cons a (List.append as bs)

def List.length : List α → Nat
  | List.nil       => 0
  | List.cons _ as => Nat.add (List.length as) 1

def List.reverse : List Nat -> List Nat 
  | List.nil => List.nil
  | List.cons a L => List.append (List.reverse L) (List.cons a List.nil) 

def List.filter (p : α → Bool) : List α → List α
  | List.nil => List.nil
  | List.cons a as => match p a with
    | true => List.cons a (filter p as)
    | false => filter p as

/- BEGIN PROOFS -/

-- First, redo proofs that you did in HW5, but this time, using tactics. 
-- Note that `variable`s do not need to be introduced!

-- part p1
variable (P Q R S : Prop)

theorem t1 : P -> P := 
 by intros p
    assumption

theorem t2 : P -> Q -> P := 
 by intros P _
    apply P

theorem t3 : (P -> Q) -> (Q -> R) -> P -> R := 
 by intros PQ QR P
    apply (QR (PQ P))

theorem t4 : P -> Q -> (Q -> P -> R) -> R := 
 by intros P Q QPR
    apply (QPR Q P)

theorem t5 : (P -> Q) -> (P -> R) -> (R -> Q -> S) -> P -> S := 
 by intros PQ PR RQS P
    apply (RQS (PR P) (PQ P))

theorem t6 : (P -> Q -> R) -> (P -> Q) -> P -> R := 
 by intros PQR PQ P
    apply PQR P (PQ P)


theorem p3 : P ∧ Q -> (Q -> R) -> R ∧ P := 
 by intros PandQ QR
    apply (And.intro (QR PandQ.right) PandQ.left)

theorem p4 : P ∨ Q -> (P -> R) -> (Q -> R) -> R := 
 by intros PorQ Hpr Hqr
    cases PorQ with
      | inl p => apply Hpr p
      | inr q => apply Hqr q 

theorem p5 : P ∨ Q -> (P -> R) -> R ∨ Q := 
 by intros pq Hpr
    cases pq with
    | inl P => apply Or.inl (Hpr P)
    | inr Q => apply Or.inr (Q)

theorem p6 : ¬ Q -> (R -> Q) -> (R ∨ ¬ S) -> S -> False := 
 by intros NotQ RQ RnotS S
    cases RnotS with
    | inl R => apply absurd (RQ R) NotQ
    | inr NotS => apply absurd S NotS
-- part p1

-- Now, some new proofs

-- part p2
theorem and_distrib_or: ∀ A B C : Prop, 
  A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  by intros A B C 
     apply Iff.intro
     . intro 
     | ⟨a, Or.inl b⟩ => apply Or.inl (And.intro a b)
     | ⟨a, Or.inr c⟩ => apply Or.inr (And.intro a c)
     . intro
     | Or.inl ⟨a, b⟩ => apply And.intro a (Or.inl b)
     | Or.inr ⟨a, c⟩ => apply And.intro a (Or.inr c)

theorem or_distrib_and: ∀ A B C : Prop, 
  A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) := 
  by intros A B C 
     apply Iff.intro
     . intro
       | Or.inl a => apply And.intro (Or.inl a) (Or.inl a)
       | Or.inr ⟨b, c⟩ => apply And.intro (Or.inr b) (Or.inr c)
     . intro
       | ⟨Or.inr b, Or.inr c⟩ => apply Or.inr (And.intro b c)
       | ⟨Or.inl a, _⟩ => apply Or.inl a
       | ⟨_, Or.inl a⟩ => apply Or.inl a

-- part p2

-- Now, some proofs that will (likely) require induction, on 
-- either Nat(ural number)s or Lists.

-- part p3
def addtail (n m : Nat) : Nat :=
  match n, m with
  | Nat.zero, m => m
  | Nat.succ n', m => addtail n' (Nat.succ m)

-- 8 lines
theorem addtail_succ : forall n m, 
  Nat.succ (addtail n m) = addtail (Nat.succ n) m :=
 by sorry

-- 10 lines
theorem add_eq : forall n m, Nat.add n m = addtail n m := 
 by sorry

-- 9 lines
theorem app_associative: ∀ L1 L2 L3 : List Nat, 
    List.append L1 (List.append L2 L3) = 
    List.append (List.append L1 L2) L3 := 
 by sorry

-- 7 lines
theorem minus_x_x: ∀ x : Nat, Nat.sub x x = 0
:= 
 by sorry

-- 5 lines
theorem add_n_1 : ∀ x : Nat, Nat.add x 1 = Nat.succ x :=
 by sorry

-- 9 lines
theorem mult_1_x: ∀ x : Nat, Nat.mul 1 x = x := 
 by sorry

-- 7 lines
theorem add_assoc: ∀ x y z : Nat, 
  Nat.add x (Nat.add y z) = Nat.add (Nat.add x y) z := 
 by sorry

-- 6 lines
theorem add_x_Sy : forall x y, 
  Nat.add x (Nat.succ y) = Nat.succ (Nat.add x y) :=
 by sorry

-- 4 lines
theorem add_n_0 : forall n, Nat.add n Nat.zero = n :=
 by sorry

-- 13 lines
theorem mult_2_x: ∀ x : Nat, Nat.mul 2 x = Nat.add x x := 
 by sorry

-- 10 lines
theorem length_append : forall (T : Type) (L1 L2 : List T), 
  List.length (List.append L1 L2) = Nat.add (List.length L1) (List.length L2) :=
 by sorry

-- 8 lines
theorem rev_length: ∀ L : List Nat, 
  List.length (List.reverse L) = List.length L := 
 by sorry


-- Consider the following pair of definitions
def even : Nat -> Bool 
| 0 => true
| 1 => false
| Nat.succ (Nat.succ n) => even n

def double : Nat → Nat 
    | 0 => 0
    | (Nat.succ x) => Nat.succ (Nat.succ (double x))

-- 5 lines
theorem even_double: ∀ x : Nat, even (double x) = true := 
 by sorry

-- part p3
end HW7
