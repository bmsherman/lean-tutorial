
/- For an introduction to the tactic system, let's write a reflective
   tactic that solves goals in intuitionistic propositional logic.
-/

reserve infixl ` ⇒ `:60
reserve infixl ` ⊢ `:25
reserve infixl ` & `:70

universes u v

inductive rlist (A : Type u) : Type u
| nil {} : rlist
| snoc {} : rlist → A → rlist

infix & := rlist.snoc

namespace rlist

def map {A : Type u} {B : Type v} (f : A → B) : rlist A → rlist B
| nil := nil
| (xs & x) := map xs & f x

inductive mem {A : Type u} : A → rlist A → Prop
| here : ∀ x xs, mem x (xs & x)
| there : ∀ x y ys, mem x ys → mem x (ys & y)

instance has_mem (A : Type u) : has_mem A (rlist A)
:= ⟨ mem ⟩

instance mem_decidable (A : Type u) [decidable_eq A]
  (x : A) (xs : rlist A) : decidable (x ∈ xs)
:= begin
induction xs,
{ apply decidable.is_false, intros contra, cases contra, },
{ induction ih_1,
  { apply (if H : x = a_1 then _ else _),
    subst a_1, apply decidable.is_true, constructor,
    apply decidable.is_false, intros contra,
    cases contra, cc, apply a_2, assumption,
  },
  { apply decidable.is_true, constructor, assumption }
}
end

lemma map_mem {A : Type u} {B : Type v} (f : A → B) (x : A)
  (xs : rlist A)
  (H : x ∈ xs) : f x ∈ xs.map f
:= begin
induction H; dsimp [map], constructor, constructor, assumption,
end

end rlist

namespace sequent

def conjunction  : rlist Prop → Prop
| rlist.nil := true
| (Ps & P) := conjunction Ps ∧ P

def entails (Γ : rlist Prop) (A : Prop)
  := conjunction Γ → A

infix ⊢ := entails

def assumption {Γ : rlist Prop} {P : Prop} (H : P ∈ Γ)
  : Γ ⊢ P
:= begin
unfold entails,
induction H; dsimp [conjunction],
{ intros H, induction H, assumption },
{ intros H, induction H, apply ih_1, assumption, }
end

def intro {Γ : rlist Prop} {P Q : Prop}
  (H : (Γ & P) ⊢ Q)
     : Γ ⊢ (P → Q)
:= begin
dsimp [entails, conjunction] at H,
intros H1 H2, apply H, split; assumption,
end

def revert {Γ : rlist Prop} {P Q : Prop}
  (H : Γ ⊢ (P → Q))
  : Γ & P ⊢ Q
:= begin
dsimp [entails, conjunction],
intros H', induction H', apply H; assumption
end

def entails_top {Γ : rlist Prop}
  : Γ ⊢ true
:= begin
simp [entails], 
end

def split {Γ : rlist Prop} {P Q : Prop}
  (HP : Γ ⊢ P)
  (HQ : Γ ⊢ Q)
  : Γ ⊢ P ∧ Q
:= begin
dsimp [entails] at *,
intros, split, apply HP, assumption,
apply HQ, assumption,
end

def left {Γ : rlist Prop} {P Q : Prop}
  (HP : Γ ⊢ P)
  : Γ ⊢ P ∨ Q
:= begin
dsimp [entails] at *,
intros, left, apply HP, assumption,
end

def right {Γ : rlist Prop} {P Q : Prop}
  (HP : Γ ⊢ Q)
  : Γ ⊢ P ∨ Q
:= begin
dsimp [entails] at *,
intros, right, apply HP, assumption,
end

def apply_lemma_conj {Γ Δ : rlist Prop} {P : Prop}
   (H : Δ ⊢ P)
   (Hassumptions : Γ ⊢ conjunction Δ)
   : Γ ⊢ P
:= begin
intros H1, apply H, apply Hassumptions,
assumption,
end

def prove_conjunction_helper (Γ : rlist Prop)
  : rlist Prop → Prop
| rlist.nil := true
| (xs & x) := prove_conjunction_helper xs ∧ (Γ ⊢ x)

def prove_conjunction {Γ Δ : rlist Prop}
  (H : prove_conjunction_helper Γ Δ)
  : Γ ⊢ conjunction Δ
:= begin
induction Δ;
  dsimp [prove_conjunction_helper] at H;
  dsimp [conjunction],
apply entails_top, induction H with H1 H2,
apply split, apply ih_1, assumption, assumption,
end

def apply_lemma (Γ : rlist Prop) (P : Prop)
   {Δ : rlist Prop}
   (H : Δ ⊢ P)
   (Hassumptions : prove_conjunction_helper Γ Δ)
   : Γ ⊢ P
:= begin
apply apply_lemma_conj, assumption,
apply prove_conjunction, assumption,
end

def cut (Γ : rlist Prop) (Q : Prop) (P : Prop)
  (HP : Γ ⊢ P)
  (H : Γ & P ⊢ Q)
  : Γ ⊢ Q
:= begin
apply apply_lemma_conj H,
dsimp [conjunction], apply split,
intros H', assumption, assumption
end

inductive formula (vTy : Type) : Type
| var {} : vTy → formula
| top {} : formula
| bot {} : formula
| and {} : formula → formula → formula
| or {} : formula → formula → formula

namespace formula
def interp{vTy : Type} (ctxt : vTy → Prop)
  : formula vTy → Prop
| (var x) := ctxt x
| top := true
| bot := false
| (and P Q) := interp P ∧ interp Q
| (or P Q) := interp P ∨ interp Q
end formula

instance formula_decidable_eq {vTy : Type}
  [decidable_eq vTy] : decidable_eq (formula vTy)
  := by tactic.mk_dec_eq_instance

def formula_entails {vTy : Type}
  (Γ : rlist (formula vTy)) (A : formula vTy)
  := ∀ ctxt, Γ.map (formula.interp ctxt) ⊢ A.interp ctxt

def interp_impl {vTy : Type}
  (Γ : rlist (formula vTy)) (A : formula vTy) (ctxt : vTy → Prop)
  : formula_entails Γ A → Γ.map (formula.interp ctxt) ⊢ A.interp ctxt
:= begin
intros H, apply H,
end

def formula_entails_auto {vTy : Type}
  [decidable_eq vTy]
  (Γ : rlist (formula vTy))
  : ∀ A : formula vTy, option (plift (formula_entails Γ A))
| formula.top := some (plift.up
  begin
  dsimp [formula_entails, formula.interp], intros ctxt,
  apply entails_top,
   end)
| formula.bot := none
| (formula.and P Q) := do
  plift.up HP ← formula_entails_auto P,
  plift.up HQ ← formula_entails_auto Q,
  some (plift.up begin
  unfold formula_entails, intros,
  dsimp [formula.interp],
  apply split, apply HP, apply HQ,
  end)
| (formula.or P Q) := (do
  plift.up HP ← formula_entails_auto P,
  some (plift.up (begin
     intros x, dsimp [formula.interp],
     apply left, apply HP
     end)))
  <|>
  (do
  plift.up HQ ← formula_entails_auto Q,
  some (plift.up (begin
     intros x, dsimp [formula.interp],
     apply right, apply HQ
     end)))
| x := if H : x ∈ Γ then some (plift.up begin
     intros ctxt, apply assumption,
     apply rlist.map_mem, assumption
  end) else none

meta def intern_var (xs : list expr) (e : expr) : list expr × ℕ
  := (if e ∈ xs then xs else xs ++ [e], xs.index_of e)

meta def reify_helper
  : list expr → expr → tactic (expr ff × list expr)
| xs `(true) := pure (``(formula.top), xs)
| xs `(false) := pure (``(formula.bot), xs)
| xs `(%%P ∧ %%Q) := do
    (P', xs') ← reify_helper xs P,
    (Q', xs'') ← reify_helper xs' Q,
    pure (``(formula.and %%P' %%Q'), xs'')
| xs `(%%P ∨ %%Q) := do
    (P', xs') ← reify_helper xs P,
    (Q', xs'') ← reify_helper xs' Q,
    pure (``(formula.or %%P' %%Q'), xs'')
| xs P := let (xs', n) := intern_var xs P in pure (``(formula.var %%(n.reflect)), xs')

meta def reify_all_helper (e : expr)
  : list expr → list expr → tactic (list (expr ff) × expr ff × list expr)
| ctxt [] := do
  (e', ctxt') ← reify_helper ctxt e,
  pure ([], e', ctxt')
| ctxt (x :: xs) := do
  (x', ctxt') ← reify_helper ctxt x,
  (xs', e', ctxt'') ← reify_all_helper ctxt' xs,
  pure (x' :: xs', e', ctxt'')

meta def reify (es : list expr) (e : expr)
  : tactic (list (expr ff) × expr ff × list expr)
  := reify_all_helper e [] es

end sequent

namespace tactic.interactive
namespace sequent

open tactic lean.parser
open interactive interactive.types

meta def get_rlist : expr → tactic (list expr)
| `(rlist.snoc %%xs %%x) := do
   xs' ← get_rlist xs,
   pure (x :: xs')
| `(rlist.nil) := pure []
| _ := tactic.fail "uh-oh"

meta def make_list : list expr → expr ff
| [] := ``(list.nil)
| (x :: xs) := ``(list.cons %%x %%(make_list xs))

meta def make_rlist : list (expr ff) → expr ff
| [] := ``(rlist.nil)
| (x :: xs) := ``(rlist.snoc %%(make_rlist xs) %%x)

def list.nth_def (xs : list Prop) (default : Prop) (n : ℕ) : Prop
:= match xs.nth n with
| (some x) := x
| none := default
end

meta def on_sequent_goal {A} (f : expr → expr → tactic A)
  : tactic A := do
  tgt ← target,
  tgt' ← instantiate_mvars tgt,
  match tgt' with
  | `(%%Γ ⊢ %%P) := f Γ P
  | _ := tactic.fail "not a logical entailment"
  end

meta def reify_goal : tactic unit :=
  on_sequent_goal $ λ xs P, do
    ty ← infer_type P >>= whnf,
    xs' ← get_rlist xs,
    (xs', P', ctxt) ← sequent.reify xs' P,
    let ctxt' := make_list ctxt,
    let xs'' := make_rlist xs',
    xs''' ← i_to_expr xs'',
    P'' ← i_to_expr P',
    ctxtf ← i_to_expr ``(list.nth_def %%ctxt' false),
    e ← i_to_expr ``(sequent.interp_impl %%xs''' %%P'' %%ctxtf),
    tactic.apply e

meta def entails_tactic (e : parse texpr) : tactic unit := do
  tgt ← target,
  tgt' ← instantiate_mvars tgt,
  match tgt' with
  | `(sequent.formula_entails %%Γ %%A) := do
    e' ← i_to_expr ``(%%e %%Γ %%A) >>= whnf,
    match e' with
    | `(some (plift.up %%x)) := tactic.apply x
    | _ := tactic.fail "Didn't get some"
    end
  | _ := tactic.fail "not a formula entailment"
  end

meta def intros := repeat (apply ``(sequent.intro _))
meta def revert := apply ``(sequent.revert _)
meta def left := apply ``(sequent.left _)
meta def right := apply ``(sequent.right _)
meta def split := apply ``(sequent.split _ _)
meta def prove_mem :=
  apply ``(rlist.mem.here) <|> (do apply ``(rlist.mem.there), prove_mem)
meta def assumption := do
  apply ``(sequent.assumption _),
  prove_mem
meta def apply (e : parse texpr) := do
  on_sequent_goal $ λ Γ P, do
    tactic.interactive.apply ``(sequent.apply_lemma %%Γ %%P %%e),
    repeat tactic.constructor

meta def assert (e : parse texpr) := do
  on_sequent_goal $ λ Γ P, do
    tactic.interactive.apply ``(sequent.cut %%Γ %%P %%e)

end sequent
end tactic.interactive

/- examples -/

lemma example1 {A B C D : Prop}
  (H : rlist.nil & A & B & A & C ⊢ D)
  : rlist.nil & A & B & C ⊢ D
:= begin
sequent.apply H; sequent.assumption
end

lemma example2 {P Q R : Prop} :
  rlist.nil & P & Q ⊢ ((R ∧ P) ∨ (Q ∧ P))
:= begin
sequent.right, sequent.split, sequent.assumption,
sequent.assumption,
end

lemma example3 {P Q R : Prop} :
 rlist.nil & P & Q ⊢ ((R ∧ P) ∨ (Q ∧ P))
:= begin
sequent.reify_goal, sequent.entails_tactic sequent.formula_entails_auto,
end