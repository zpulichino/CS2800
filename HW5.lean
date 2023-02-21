/- Problem 1: Programming in Lean -/

/-
Define the following list functions. Example uses are given via
example. Once you have defined the function (replaced the _ with
an implementation), the examples will work (the red highlighting
will go away).
-/

-- part p1-a
def nonzeros : List Nat -> List Nat := 
fun list => match list with
  | [] => []
  | 0::rest => nonzeros rest
  | first::rest => first::nonzeros rest
example : nonzeros [0,1,0,2,3,0,0] = [1,2,3] := by rfl

def oddmembers : List Nat -> List Nat := 
fun list => match list with
  | [] => []
  | first::rest => if (first % 2 == 1) 
             then first::oddmembers rest 
             else oddmembers rest
example : oddmembers [0,1,0,2,3,0,0] = [1,3] := by rfl

def countoddmembers : List Nat -> Nat := 
fun list => match list with
  | [] => 0
  | first::rest => if (first % 2 == 1)
             then 1 + countoddmembers rest
             else countoddmembers rest
example : countoddmembers [1,0,3,1,4,5] = 4 := by rfl
example : countoddmembers [0,2,4] = 0 := by rfl
example : countoddmembers [] = 0 := by rfl

-- part p1-a


/- A bag (or multiset) is like a set, except that each element
can appear multiple times rather than just once. One possible
representation for a bag of numbers is as a list.
-/

-- part p1-b
def Bag := List Nat
-- part p1-b

/- Complete the following definitions for the functions count,
union, add, and member for bags.
-/

-- part p1-c
def count : Nat -> Bag -> Nat := 
fun n b => match b with
  | [] => 0
  | first::rest => if (first == n)
             then 1 + count n rest
             else count n rest
example : count 1 [1,2,3,1,4,1] = 3 := by rfl
example : count 6 [1,2,3,1,4,1] = 0 := by rfl

def union : Bag -> Bag -> Bag := 
fun b0 b1 => match b1 with 
  | [] => b0
  | first::rest => first::(union b0 rest)
example : count 1 (union [1,2,3] [1,4,1]) = 3 := by rfl

def add : Nat -> Bag -> Bag := 
fun n b => match b with 
  | [] => b 
  | _ => n::b 
example : count 1 (add 1 [1,4,1]) = 3 := by rfl
example : count 5 (add 1 [1,4,1]) = 0 := by rfl


def member : Nat -> Bag -> Bool := 
fun n b => match b with 
  | [] => false
  | first::rest => if (first != n)
                   then member n rest
                   else true 
example : member 1 [1,4,1] = true := by rfl
example : member 2 [1,4,1] = false := by rfl

def remove_one : Nat -> Bag -> Bag := 
fun n b => match b with 
  | [] => []
  | first::rest => if (first == n) 
                   then rest
                   else first::(remove_one n rest)
example : count 5 (remove_one 5 [2,1,5,4,1]) = 0 := by rfl
example : count 5 (remove_one 5 [2,1,4,1]) = 0 := by rfl
example : count 4 (remove_one 5 [2,1,4,5,1,4]) = 2 := by rfl
example : count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1 := by rfl

def remove_all : Nat -> Bag -> Bag := 
fun n b => match b with 
  | [] => []
  | first::rest => if (first == n) 
                   then remove_all n rest
                   else first::(remove_all n rest)
example : count 5 (remove_all 5 [2,1,5,4,1]) = 0 := by rfl
example : count 5 (remove_all 5 [2,1,4,1]) = 0 := by rfl
example : count 4 (remove_all 5 [2,1,4,5,1,4]) = 2 := by rfl
example : count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0 := by rfl

def subset : Bag -> Bag -> Bool := 
fun b0 b1 => match b0 with 
  | [] => true 
  | first::rest => if (member first b1)
                   then subset rest (remove_one first b1)
                   else false 
example : subset [1,2] [2,1,4,1] = true := by rfl
example : subset [1,2,2] [2,1,4,1] = false := by rfl

-- part p1-c

/- Proofs in minimal propositional logic -/

-- part p1-d

variable (P Q R S : Prop)

theorem t1 : P -> P := fun P => P

theorem t2 : P -> Q -> P := fun p _ => p

theorem t3 : (P -> Q) -> (Q -> R) -> P -> R := fun PQ QR p => QR (PQ p)

theorem t4 : P -> Q -> (Q -> P -> R) -> R := fun p q PR => PR q p

theorem t5 : (P -> Q) -> (P -> R) -> (R -> Q -> S) -> P -> S := 
  fun PQ PR RQS p => RQS (PR p) (PQ p) 

theorem t6 : (P -> Q -> R) -> (P -> Q) -> P -> R := 
  fun PQR PQ p => PQR p (PQ p)

-- part p1-d

/- Proofs in propositional logic -/

-- part p1-e

theorem p1 : P ∧ Q -> Q ∧ P := 
  fun PQ => And.intro PQ.right PQ.left

theorem p2 : P ∧ Q -> P := 
  fun PQ => PQ.left

theorem p3 : P ∧ Q -> (Q -> R) -> R ∧ P := 
  fun PQ QR => And.intro (QR PQ.right) PQ.left

theorem p4 : P ∨ Q -> (P -> R) -> (Q -> R) -> R := 
  fun PQ PR QR => match PQ with
                  | Or.inl p => PR p
                  | Or.inr q => QR q

theorem p5 : P ∨ Q -> (P -> R) -> R ∨ Q := 
  fun PQ PR => match PQ with
              | Or.inl p => Or.inl (PR p)
              | Or.inr q => Or.inr q

theorem p6 : ¬ Q -> (R -> Q) -> (R ∨ ¬ S) -> S -> False := 
  fun NQ RQ RNS S => match RNS with
                    | Or.inl r => False.elim (NQ (RQ r))
                    | Or.inr NS => False.elim (NS S)

-- part p1-e
