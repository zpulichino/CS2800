/- PROBLEM 1: Classical logic 

In this problem, we will prove various theorems, some that 
require classical logic (e.g., Classical.em).
-/
-- part 0

-- 12 lines: does this need Classical.em?
theorem p_iff_false: ∀ P : Prop, (P ↔ False) ↔ ¬ P :=
 by intros P 
    constructor 
    case mp => 
      simp 
      cases (Classical.em P) 
      intros np p 
      contradiction 
      intros np p 
      contradiction
    case mpr => 
      simp 
      cases (Classical.em P) 
      intros np p 
      contradiction 
      intros np p 
      contradiction

-- 9 lines: does this need Classical.em?
theorem p_and_not_p_eq_false: ∀ P : Prop, (P ∧ ¬ P) ↔ False :=
 by intros P
    constructor
    case mp =>
      intros pnp
      cases pnp
      case intro l r =>
        contradiction
    case mpr =>
      intros 
      contradiction

-- 21 lines: does this need Classical.em?
theorem or_absorb_and_or: ∀ P Q : Prop, P ∨ (¬ P ∧ Q) ↔ (P ∨ Q) :=
  by intros P Q 
     constructor
     case mp =>
      intros pnpq
      cases pnpq
      case inl p =>
        apply Or.inl
        assumption
      case inr npq =>
        cases npq
        case intro l r =>
          apply Or.inr
          assumption
     case mpr =>
      intros pnpq
      cases pnpq
      case inl p =>
        apply Or.inl
        assumption
      case inr q =>
        cases (Classical.em P)
        case inl P' =>
          apply Or.inl P'
        case inr np =>
          apply Or.inr
          apply And.intro <;> assumption

-- 11 lines: does this need Classical.em?
theorem redundant_and: ∀ P Q : Prop, (P ∨ Q) ∧ (P ∨ ¬ Q) ↔ P :=
 by intros P Q
    constructor
    case mp =>
      intros pqpnq
      cases pqpnq
      case intro l r =>
        cases l <;> cases r <;> try assumption
        contradiction
    case mpr =>
      intros p
      constructor
      apply Or.inl
      assumption
      apply Or.inl
      assumption 

-- 10 lines: does this need Classical.em?
theorem exportation: ∀ A B C : Prop, (A → B → C) ↔ (A ∧ B → C) :=
 by intros A B C 
    constructor
    case mp => 
      intros abc ab 
      cases ab 
      case intro l r => 
        cases (Classical.em A)
        case inl A' => 
          simp [*]
        case inr A'' => 
          simp [*]
    case mpr => 
      intros abc a b 
      simp [*]
    
-- part 0

-- THE REMAINING PROBLEMS INVOLVING WRITING TYPES, THEOREMS,
-- BUT NO PROOFS. WE ARE MOVING BACK FROM THE WORLD OF PROOF 
-- INTO THE WORLD OF SPECIFICATION, WHERE WE BEGAN.

/- PROBLEM 2: Binary Trees

A red-black balanced binary search tree is described as the following:

- Each node has a color (red or black) associated with it (in addition to its value and left and right children)
- A node can be "null": these will form the leaves of the tree.

The following 3 properties hold:
- (root property) The root of the red-black tree is black
- (red property) The children of a red node are black.
- (black property) For each node with at least one null child, the number of black nodes on the path from the root to the null child is the same.

As a binary search tree, all left children are _less_ than right children. 

Your task is to:
1. Design an inductive type RedBlackTree. It should have Nat's as values. Use the empty inductive type below to start.
2. Given the (blank) definitions for empty (to create an empty tree), insert (to insert a new Nat to the tree) & delete (to remove a number), write theorems that ensure that the properties hold. Note that you do not need to _prove_ the theorems, just write down what they are.
-/

/-
NOTE: If you write recursive functions that Lean cannot show
 to be terminating, you are welcome to add `decreasing_by sorry` after them: this means you are giving up on showing that they terminate, which for this assignment, is fine.

e.g., 

def my_function : ArgType -> ArgType -> RetType
| patterns => body
| patterns => body
decreasing_by sorry
-/

-- part 1
inductive Color : Type where
| Red : Color
| Black : Color

/-
Checks if the two colors are a valid color pattern for RBT, 
Only invalid is Red Red, parent child respectively
The Color order is parent first child next.
-/
def Color.RBTcompare : Color -> Color -> Prop
| Color.Red, Color.Red => false
| _, _ => true

-- If the color is black return 1 if not return 0
def Color.plusOneBlack : Color -> Nat
| Color.Black => 1
| Color.Red => 0

-- I'll shorten RedBlackTree to RBT
inductive RedBlackTree : Type where 
| Leaf : RedBlackTree
| Node (val : Nat) (Left : RedBlackTree) (Right : RedBlackTree) (c : Color) : RedBlackTree

-- returns the color of a leaf or node, leaf is assumed to be black, getter method
def RedBlackTree.Color :  RedBlackTree -> Color 
| Leaf => Color.Black
| Node _ _ _ color => color

-- checks if the root of the tree is black or a leaf
def RedBlackTree.BlackRootProp : RedBlackTree -> Prop 
| Leaf => true
| Node _ _ _ color => (color.RBTcompare Color.Black) 

-- checks if the colors are correctly 
def RedBlackTree.checkColorProp : RedBlackTree -> Prop 
| Leaf => true
| Node _ left right color => 
  (left.Color.RBTcompare color) ∧ 
  (right.Color.RBTcompare color) ∧
  left.checkColorProp ∧ 
  right.checkColorProp 

-- returns the max number of black nodes in any path of the RBT
def RedBlackTree.maxBlackCount : RedBlackTree -> Nat
| Leaf => 0
| Node _ left right Color =>
  Color.plusOneBlack + (Nat.max left.maxBlackCount right.maxBlackCount)

-- checks if the black property holds.
def RedBlackTree.checkBlackProp : RedBlackTree -> Prop
| Leaf => true
| Node _ left right _ =>
  (left.maxBlackCount == right.maxBlackCount) ∧
  left.checkBlackProp ∧ 
  right.checkBlackProp

-- part 1

/- PROBLEM 3: Information flow

In this problem, you will write a theorem statement that ensures 
that a (unspecified) function `process` does not leak any private 
information. Private information, in this case, is the first 
argument to the function (`private_inputs`); the function also has 
another argument, `public_inputs`, that does not need to remain 
private. 

Note that you need to think about _how_ the private inputs could 
potentially leak: you don't know what the definition of the function 
is, so what theorem can you write about it that nonetheless ensures 
that if users see the _output_ of it they cannot determine anything 
about the private inputs.
-/

-- part 2
def process (private_inputs : List Nat) (public_inputs : List Nat) : Nat := by sorry

theorem no_leak_process : forall public_inputs private_inputs1 private_inputs2,
   process private_inputs1 public_inputs = process private_inputs2 public_inputs -> 
   private_inputs1 = private_inputs2 := 
 by sorry

-- part 2

/- PROBLEM 4: Algorithmic Fairness

In this problem you are tasked with  writing a theorem that _proves_ 
that there is no bias in a particular function that decides whether 
to give mortgages. It's up to you both to decide _what that means_ 
and how to ensure it.

Consider that you have a function, `give_mortgage` that takes
as input `income` (a list of yearly income, going back several 
years), `assets` (number), `race`, `gender`, `age`, 
`zipcode` (where they currently live), and returns a boolean 
of whether or not to give a mortgage.

Write theorem(s) that ensures that `give_mortgage` does not 
encode bias. Think about how you might express that? How is this 
similar or different from, e.g., the information flow problem above?
 -/


-- part 3
def give_mortgage : List Nat -- income
                 -> Nat      -- assets
                 -> String   -- race
                 -> String   -- gender
                 -> Nat      -- age
                 -> String   -- zipcode
                 -> Bool := by sorry

theorem mortgage_bias : forall (inc: List Nat) (assets : Nat) (zip : String),
  exists (b : Bool) , forall (race : String) (gender : String) (age : Nat), 
  give_mortgage inc assets race gender age zip = b := by sorry

-- part 3
