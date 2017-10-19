/- This file is a tutorial for Coq users getting started
   with Lean. They are quite similar systems, so picking
   up Lean should not be too difficult.

   I highly recommend consulting the Coq-Lean cheatsheet
   that Joey Dodds and I made this summer:
   https://jldodds.github.io/coq-lean-cheatsheet/
-/

/- I'm a big fan of using Unicode while writing Lean.
   It's similar to Clément's company-coq mode, 
   using LaTeX-like style, except one completes writing
   a Unicode symbol with the "space" key, rather than
   "Enter".
   
   To discover how to type a Unicode symbol, simply
   hover your mouse over it in VSCode.
-/

universes u v w
/- Just like there is Coq Vernacular, there are Lean
   directives like the one above. However, unlike Coq,
   where we need to separate Vernacular with periods,
   we don't need to separate Lean directives with any
   separator. -/
/- Whereas Coq has both universe polymorphism (if you
   turn it on) and cumulativity, Lean only has
   universe polymorphism (but cumulativity can be
   achieved manually: see `plift` and `ulift`)
-/

/-- Vectors are an inductive family that represents
    lists indexed by their length -/
inductive vector (A : Type u) : ℕ → Type u
| nil {} : vector 0
| cons {} : ∀ {n : ℕ}, A → vector n → vector n.succ
/- The purpose of the empty braces after the constructor names
   is to make the parametric arguments (in this case, `A : Type u`)
   implicit. -/
/- Because parametric variables are automatically determined,
   we don't need to put them in when defining the types of the
   constructors, e.g., we write `vector 0` instead of `vector A 0`.
-/

notation x :: xs := vector.cons x xs

/- The `n.succ` in the index of the result type of `cons` is
   our first example of Lean's interesting namespacing
   functionality, that allows one to program in Lean with a
   sort of object-oriented style. In effect, we see that this
   is just syntactic sugar:
-/
lemma nat_succ_equiv (n : ℕ) : n.succ = nat.succ n := rfl

#check nat.succ
/- Every constructor is automatically put into the
   namespace of the name of its datatype. -/
#check vector.cons
/- Green underlines may show up for a few reasons:
   - There is printing output, as in the case above.
     To view the printing output in VSCode, either mouse over
     the green underlined text, or put your text cursor
     over it and read the text in the `Lean Messages` view
     (which is opened/closed with Ctrl-Shift-Enter.)
  - There is a use of `sorry`.
-/
#check sorry

namespace vector
/- We enter the `vector` namespace with the above command, 
   and leave it with `end vector`, seen later.

   Once we leave this block, every definition will be
   in the namespace `vector`, hence prefixed with
   `vector.`. Additionally, within this block, all
   preexisting definitions in the namespace are
   brought into the local namespace, so for instance,
   we can just say `nil` rather than `vector.nil`.
-/

def zip_with {A : Type u} {B : Type v} {C : Type w} 
  (f : A → B → C)
  : ∀ {n : ℕ}, vector A n → vector B n → vector C n
| 0 nil nil := nil
| (nat.succ n) (x :: xs) (y :: ys) := f x y :: zip_with xs ys
/- There are two ways to create recursive definitions in Lean.
   One is with the equations compiler, shown above, and the other
   is by applying recursors directly. Whenever a datatype is defined,
   recursors are automatically created. For instance:
-/
#check @nat.rec
#check @nat.cases_on

end vector

/-- The reflexive-transitive closure of a relation -/
inductive RTclosure {A : Type u} (R : A → A → Prop)
  : A → A → Prop
| refl {} : ∀ x, RTclosure x x
| extend {} : ∀ {x y z}, R x y → RTclosure y z → RTclosure x z

namespace RTclosure

/-- An example where the equations compiler cannot
    handle primitive recursion for some reason.
-/
def trans {A : Type u} {R : A → A → Prop}
  : ∀ {x y z : A}, 
   RTclosure R x y → RTclosure R y z → RTclosure R x z
| x ._ z (refl ._) xz := xz
| x y z (@extend ._ ._ ._ w ._ xw wy) yz := extend xw (trans wy yz)
/- Red underlining indicates an error. -/

def trans' {A : Type u} {R : A → A → Prop}
  {x y z : A} (xy : RTclosure R x y)
  (yz : RTclosure R y z) : RTclosure R x z
:= begin
induction xy,
{ assumption },
{ apply extend, 
  { assumption },
  { apply ih_1, assumption }
}
end
/- Above is our first look at Lean's Proof mode!
   To see the current state of your proof in VSCode,
   hit Ctrl-Shift-Enter (on Mac, Cmd-Shift-Enter)
   to open up the Lean Messages view.

   What the Lean Messages view tab displays depends
   on the current position of your text cursor in the
   buffer that you are editing. -/

#print trans'

end RTclosure

/- We have definitional proof irrelevance-/
#print proof_irrel

/- That implies UIP -/
lemma UIP (A : Sort u) (x y : A) (p q : x = y) : p = q := rfl

/- There are quotient types in Lean as well,
   which implies functional extensionality:
-/
#check @funext
#print funext

/- For an introduction to the tactic system, let's write a reified
   tactic that solves goals in intuitionistic propositional logic.
-/