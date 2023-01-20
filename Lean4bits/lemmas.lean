import Mathlib.Data.Fintype.Card
import Lean4bits.defs

open Sum

variable {α β α' β' : Type} {γ : β → Type}

def propagateAux (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (x : β → ℕ → Bool) : ℕ → (α → Bool) × Bool
  | 0 => next_bit init_carry (fun i => x i 0)
  | n+1 => next_bit (propagateAux init_carry next_bit x n).1 (fun i => x i (n+1))

def propagate (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (x : β → ℕ → Bool) (i : ℕ) : Bool :=
  (propagateAux init_carry next_bit x i).2

@[simp] def propagateCarry (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool))
    (x : β → ℕ → Bool) : ℕ → (α → Bool)
  | 0 => next_bit init_carry (fun i => x i 0)
  | n+1 => next_bit (propagateCarry init_carry next_bit x n) (fun i => x i (n+1))

@[simp] def propagateCarry2 (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool))
    (x : β → ℕ → Bool) : ℕ → (α → Bool)
  | 0 => init_carry
  | n+1 => next_bit (propagateCarry2 init_carry next_bit x n) (fun i => x i n)

lemma propagateCarry2_succ (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool))
    (x : β → ℕ → Bool) : ∀ (n : ℕ),
    propagateCarry2 init_carry next_bit x (n+1) =
    propagateCarry init_carry next_bit x n
  | 0 => rfl
  | n+1 => by rw [propagateCarry2, propagateCarry2_succ _ _ _ n, propagateCarry]

@[simp] lemma propagateAux_fst_eq_carry (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (x : β → ℕ → Bool) : ∀ n : ℕ,
    (propagateAux init_carry next_bit x n).1 =
    propagateCarry init_carry (fun c b => (next_bit c b).1) x n
  | 0 => rfl
  | n+1 => by rw [propagateAux, propagateCarry, propagateAux_fst_eq_carry _ _ _ n]

@[simp] lemma propagate_zero (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
    (α → Bool) × Bool)
    (x : β → ℕ → Bool) :
    propagate init_carry next_bit x 0 = (next_bit init_carry (fun i => x i 0)).2 :=
  rfl

lemma propagate_succ (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (x : β → ℕ → Bool) (i : ℕ) :
    propagate init_carry next_bit x (i+1) = (next_bit
      (propagateCarry init_carry (fun c b => (next_bit c b).1) x i)
      (λ j => x j (i+1))).2 :=
  by rw [← propagateAux_fst_eq_carry]; rfl

lemma propagate_succ2 (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (x : β → ℕ → Bool) (i : ℕ) :
    propagate init_carry next_bit x (i+1) = (next_bit
      (propagateCarry2 init_carry (λ c b => (next_bit c b).1) x (i+1))
      (λ j => x j (i+1))).2 :=
  by rw [propagateCarry2_succ, ← propagateAux_fst_eq_carry]; rfl

lemma propagateCarry_propagate {δ : β → Type} {β' : Type}
      (f : ∀ a, δ a → β') : ∀ (n : ℕ) (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool))
    (init_carry_x : ∀ a, γ a → Bool)
    (next_bit_x : ∀ a (_carry : γ a → Bool) (_bits : δ a → Bool),
      (γ a → Bool) × Bool)
    (x : β' → ℕ → Bool),
    propagateCarry init_carry next_bit (λ a => propagate (init_carry_x a)
      (next_bit_x a) (λ d => x (f a d))) n =
    propagateCarry
      (λ a : α ⊕ (Σ a, γ a) => Sum.elim init_carry (λ b : Σ a, γ a =>
        init_carry_x b.1 b.2) a)
      (λ (carry : (α ⊕ (Σ a, γ a)) → Bool) (bits : β' → Bool) =>
    -- first compute (propagate (init_carry_x a) (next_bit_x a) (x a) n)
        let f : ∀ (a : β), (γ a → Bool) × Bool := λ a => next_bit_x a
          (λ d => carry (inr ⟨a, d⟩)) (λ d => bits (f a d))
        let g : (α → Bool) := (next_bit (carry ∘ inl) (λ a => (f a).2))
        Sum.elim g (λ x => (f x.1).1 x.2))
      x n ∘ inl
  | 0, init_carry, next_bit, init_carry_x, next_bit_x, x => rfl
  | n+1, init_carry, next_bit, init_carry_x, next_bit_x, x => by
    have := propagateCarry_propagate f n
    simp only [propagateCarry, propagate_succ, elim_inl, Nat.add] at *
    conv_lhs => simp only [this]
    clear this
    dsimp
    congr
    ext a
    dsimp
    congr
    ext b
    dsimp [propagateCarry, propagate_succ, elim_inl, Nat.add]
    congr
    dsimp
    induction' n with n ih
    . simp
    . simp [ih]

lemma propagate_propagate {δ : β → Type} {β' : Type}
      (f : ∀ a, δ a → β') : ∀ (n : ℕ) (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (init_carry_x : ∀ a, γ a → Bool)
    (next_bit_x : ∀ a (_carry : γ a → Bool) (_bits : δ a → Bool),
      (γ a → Bool) × Bool)
    (x : β' → ℕ → Bool),
    propagate init_carry next_bit (λ a => propagate (init_carry_x a)
      (next_bit_x a) (λ d => x (f a d))) n =
    propagate
      (λ a : α ⊕ (Σ a, γ a) => Sum.elim init_carry (λ b : Σ a, γ a =>
        init_carry_x b.1 b.2) a)
      (λ (carry : (α ⊕ (Σ a, γ a)) → Bool) (bits : β' → Bool) =>
        -- first compute (propagate (init_carry_x a) (next_bit_x a) (x a) n)
        let f : ∀ (a : β), (γ a → Bool) × Bool := λ a => next_bit_x a (λ d =>
          carry (inr ⟨a, d⟩)) (λ d => bits (f a d))
        let g : (α → Bool) × Bool := (next_bit (carry ∘ inl) (λ a => (f a).2))
        (Sum.elim g.1 (λ x => (f x.1).1 x.2), g.2)
      )
    x n
  | 0, init_carry, next_bit, init_carry_x, next_bit_x, x => rfl
  | n+1, init_carry, next_bit, init_carry_x, next_bit_x, x => by
    simp only [propagate_succ]
    rw [propagateCarry_propagate]
    congr
    ext
    congr
    induction' n with n ih
    . simp
    . simp [ih]

lemma propagateCarry_changeVars {β' : Type}
    (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool))
    (x : β' → ℕ → Bool) (i : ℕ)
    (changeVars : β → β') :
    propagateCarry init_carry next_bit (λ b => x (changeVars b)) i =
    propagateCarry init_carry (λ (carry : α → Bool) (bits : β' → Bool) =>
      next_bit carry (λ b => bits (changeVars b))) x i := by
  induction i
  . simp
  . simp [*]

lemma propagate_changeVars {β' : Type}
    (init_carry : α → Bool)
    (next_bit : ∀ (_carry : α → Bool) (_bits : β → Bool),
      (α → Bool) × Bool)
    (x : β' → ℕ → Bool) (i : ℕ)
    (changeVars : β → β') :
    propagate init_carry next_bit (λ b => x (changeVars b)) i =
    propagate init_carry (λ (carry : α → Bool) (bits : β' → Bool) =>
      next_bit carry (λ b => bits (changeVars b))) x i := by
  induction' i with i ih
  . rfl
  . simp only [propagate_succ, propagateCarry_changeVars, ih]

open Term

@[simp] def arity : Term → ℕ
| (var n) => n+1
| zero => 0
| one => 0
| neg_one => 0
| Term.and t₁ t₂ => max (arity t₁) (arity t₂)
| Term.or t₁ t₂ => max (arity t₁) (arity t₂)
| Term.xor t₁ t₂ => max (arity t₁) (arity t₂)
| Term.not t => arity t
| ls t => arity t
| add t₁ t₂ => max (arity t₁) (arity t₂)
| sub t₁ t₂ => max (arity t₁) (arity t₂)
| neg t => arity t
| incr t => arity t
| decr t => arity t

@[simp] def Term.evalFin : ∀ (t : Term) (_vars : Fin (arity t) → ℕ → Bool), ℕ → Bool
| var n, vars => vars (Fin.last n)
| zero, _vars => zeroSeq
| one, _vars => oneSeq
| neg_one, _vars => negOneSeq
| Term.and t₁ t₂, vars =>
  andSeq (Term.evalFin t₁
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
  (Term.evalFin t₂
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
| Term.or t₁ t₂, vars =>
  orSeq (Term.evalFin t₁
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
  (Term.evalFin t₂
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
| Term.xor t₁ t₂, vars =>
  xorSeq (Term.evalFin t₁
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
  (Term.evalFin t₂
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
| not t, vars => notSeq (Term.evalFin t vars)
| ls t, vars => lsSeq (Term.evalFin t vars)
| add t₁ t₂, vars =>
  addSeq (Term.evalFin t₁
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
  (Term.evalFin t₂
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
| sub t₁ t₂, vars =>
  subSeq (Term.evalFin t₁
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
  (Term.evalFin t₂
    (fun i => vars (Fin.castLe (by simp [arity]) i)))
| neg t, vars => negSeq (Term.evalFin t vars)
| incr t, vars => incrSeq (Term.evalFin t vars)
| decr t, vars => decrSeq (Term.evalFin t vars)

lemma evalFin_eq_eval (t : Term) (vars : ℕ → ℕ → Bool) :
    Term.evalFin t (fun i => vars i) = Term.eval t vars := by
  induction t <;>
  dsimp [Term.evalFin, Term.eval, arity] at * <;> simp [*]


lemma id_eq_propagate (x : ℕ → Bool) :
    x = propagate Empty.elim (λ _ (y : Unit → Bool) => (Empty.elim, y ())) (λ _ => x) := by
  ext n; cases n <;> rfl

lemma zero_eq_propagate :
    zeroSeq = propagate Empty.elim (λ (_ _ : Empty → Bool) => (Empty.elim, false)) Empty.elim := by
  ext n; cases n <;> rfl

lemma one_eq_propagate :
    oneSeq = propagate (λ _ : Unit => true)
      (λ f (_ : Empty → Bool) => (λ _ => false, f ())) Empty.elim := by
  ext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | n+2 => simp [oneSeq, propagate_succ]

lemma and_eq_propagate (x y : ℕ → Bool) :
    andSeq x y = propagate Empty.elim
      (λ _ (y : Bool → Bool) => (Empty.elim, y true && y false)) (λ b => cond b x y) := by
  ext n; cases n <;> simp [propagate, propagateAux, andSeq]

lemma or_eq_propagate (x y : ℕ → Bool) :
    orSeq x y = propagate Empty.elim
      (λ _ (y : Bool → Bool) => (Empty.elim, y true || y false)) (λ b => cond b x y) := by
  ext n; cases n <;> simp [propagate, propagateAux, orSeq]

lemma xor_eq_propagate (x y : ℕ → Bool) :
    xorSeq x y = propagate Empty.elim
      (λ _ (y : Bool → Bool) => (Empty.elim, xor (y true) (y false))) (λ b => cond b x y) := by
  ext n; cases n <;> simp [propagate, propagateAux, xorSeq]

lemma not_eq_propagate (x : ℕ → Bool) :
    notSeq x = propagate Empty.elim (λ _ (y : Unit → Bool) => (Empty.elim, !(y ()))) (λ _ => x) := by
  ext n; cases n <;> simp [propagate, propagateAux, notSeq]

lemma ls_eq_propagate (x : ℕ → Bool) :
  lsSeq x = propagate (λ _ : Unit => false) (λ (carry x : Unit → Bool) => (x, carry ())) (λ _ => x) :=
begin
  ext n,
  cases n with n,
  { refl },
  { cases n,
    { simp [lsSeq, propagate_succ] },
    { simp [lsSeq, propagate_succ] } }
end

lemma add_seqAux_eq_propagateCarry (x y : ℕ → Bool) (n : ℕ) :
  (add_seqAux x y n).2 = propagateCarry (λ _, false)
    (λ (carry : Unit → Bool) (bits : Bool → Bool),
      λ _, (bits true && bits false) || (bits false && carry ()) || (bits true && carry ()))
  (λ b, cond b x y) n () :=
begin
  induction n,
  { simp [add_seqAux] },
  { simp [add_seqAux, *] }
end

lemma add_eq_propagate (x y : ℕ → Bool) :
  add_seq x y = propagate (λ _, false)
    (λ (carry : Unit → Bool) (bits : Bool → Bool),
      (λ _, (bits true && bits false) || (bits false && carry ()) || (bits true && carry ()),
        bxor (bits true) (bxor (bits false) (carry ()))))
  (λ b, cond b x y) :=
begin
  ext n,
  cases n with n,
  { simp [add_seq, add_seqAux] },
  { cases n,
    { simp [add_seq, add_seqAux, propagate_succ] },
    { simp [add_seq, add_seqAux, add_seqAux_eq_propagateCarry,
        propagate_succ] } }
end

lemma sub_seqAux_eq_propagateCarry (x y : ℕ → Bool) (n : ℕ) :
  (sub_seqAux x y n).2 = propagateCarry (λ _, false)
    (λ (carry : Unit → Bool) (bits : Bool → Bool),
      λ _, (bnot (bits true) && (bits false)) ||
        (bnot (bxor (bits true) (bits false))) && carry ())
  (λ b, cond b x y) n () :=
begin
  induction n,
  { simp [sub_seqAux] },
  { simp [sub_seqAux, *] }
end

lemma sub_eq_propagate (x y : ℕ → Bool) :
  sub_seq x y = propagate (λ _, false)
    (λ (carry : Unit → Bool) (bits : Bool → Bool),
      (λ _, (bnot (bits true) && (bits false)) ||
        ((bnot (bxor (bits true) (bits false))) && carry ()),
        bxor (bits true) (bxor (bits false) (carry ()))))
  (λ b, cond b x y) :=
begin
  ext n,
  cases n with n,
  { simp [sub_seq, sub_seqAux] },
  { cases n,
    { simp [sub_seq, sub_seqAux, propagate_succ] },
    { simp [sub_seq, sub_seqAux, sub_seqAux_eq_propagateCarry,
        propagate_succ] } }
end

lemma negSeqAux_eq_propagateCarry (x : ℕ → Bool) (n : ℕ) :
  (negSeqAux x n).2 = propagateCarry (λ _, true)
    (λ (carry : Unit → Bool) (bits : Unit → Bool),
      λ _, (bnot (bits ())) && (carry ()))
  (λ _, x) n () :=
begin
  induction n,
  { simp [negSeqAux] },
  { simp [negSeqAux, *] }
end

lemma neg_eq_propagate (x : ℕ → Bool) :
  negSeq x = propagate (λ _, true)
    (λ (carry : Unit → Bool) (bits : Unit → Bool),
      (λ _, (bnot (bits ())) && (carry ()), bxor (bnot (bits ())) (carry ())))
  (λ _, x) :=
begin
  ext n,
  cases n with n,
  { simp [negSeq, negSeqAux] },
  { cases n,
    { simp [negSeq, negSeqAux, propagate_succ] },
    { simp [negSeq, negSeqAux, negSeqAux_eq_propagateCarry,
        propagate_succ] } }
end

lemma incrSeqAux_eq_propagateCarry (x : ℕ → Bool) (n : ℕ) :
  (incrSeqAux x n).2 = propagateCarry (λ _, true)
    (λ (carry : Unit → Bool) (bits : Unit → Bool),
      λ _, (bits ()) && carry ())
  (λ _, x) n () :=
begin
  induction n,
  { simp [incrSeqAux] },
  { simp [incrSeqAux, *] }
end

lemma incr_eq_propagate (x : ℕ → Bool) :
  incrSeq x = propagate (λ _, true)
    (λ (carry : Unit → Bool) (bits : Unit → Bool),
      (λ _, (bits ()) && carry (), bxor (bits ()) (carry ())))
  (λ _, x) :=
begin
  ext n,
  cases n with n,
  { simp [incrSeq, incrSeqAux] },
  { cases n,
    { simp [incrSeq, incrSeqAux, propagate_succ] },
    { simp [incrSeq, incrSeqAux, incrSeqAux_eq_propagateCarry,
        propagate_succ] } }
end

lemma decrSeqAux_eq_propagateCarry (x : ℕ → Bool) (n : ℕ) :
  (decrSeqAux x n).2 = propagateCarry (λ _, true)
    (λ (carry : Unit → Bool) (bits : Unit → Bool),
      λ _, (bnot (bits ())) && carry ())
  (λ _, x) n () :=
begin
  induction n,
  { simp [decrSeqAux] },
  { simp [decrSeqAux, *] }
end

lemma decr_eq_propagate (x : ℕ → Bool) :
  decrSeq x = propagate (λ _, true)
    (λ (carry : Unit → Bool) (bits : Unit → Bool),
      (λ _, (bnot (bits ())) && carry (), bxor (bits ()) (carry ())))
  (λ _, x) :=
begin
  ext n,
  cases n with n,
  { simp [decrSeq, decrSeqAux] },
  { cases n,
    { simp [decrSeq, decrSeqAux, propagate_succ] },
    { simp [decrSeq, decrSeqAux, decrSeqAux_eq_propagateCarry,
        propagate_succ] } }
end

structure propagate_struc (arity : Type) : Type 1 :=
( α  : Type )
[ i : Fintype α ]
( init_carry : α → Bool )
( next_bit : ∀ (carry : α → Bool) (bits : arity → Bool),
    (α → Bool) × Bool )

atrueribute [instance] propagate_struc.i

namespace propagate_struc

variables {arity : Type} (p : propagate_struc arity)

def eval : (arity → ℕ → Bool) → ℕ → Bool :=
propagate p.init_carry p.next_bit

def changeVars {arity2 : Type} (changeVars : arity → arity2) :
  propagate_struc arity2 :=
{ α := p.α,
  i := p.i,
  init_carry := p.init_carry,
  next_bit := λ carry bits, p.next_bit carry (fun i => bits (changeVars i)) }

def compose [fintype arity]
  (new_arity : Type)
  (q_arity : arity → Type)
  (vars : ∀ (a : arity), q_arity a → new_arity)
  (q : ∀ (a : arity), propagate_struc (q_arity a)) :
  propagate_struc (new_arity) :=
{ α := p.α ⊕ (Σ a, (q a).α),
  i := by letI := p.i; apply_instance,
  init_carry := Sum.elim p.init_carry (λ x, (q x.1).init_carry x.2),
  next_bit := λ carry bits,
    let f : ∀ (a : arity), ((q a).α → Bool) × Bool := λ a, (q a).next_bit (λ d,
        carry (inr ⟨a, d⟩)) (λ d, bits (vars a d)) in
    let g : (p.α → Bool) × Bool := (p.next_bit (carry ∘ inl) (λ a, (f a).2)) in
    (Sum.elim g.1 (λ x, (f x.1).1 x.2), g.2) }

lemma eval_compose [fintype arity]
  (new_arity : Type)
  (q_arity : arity → Type)
  (vars : ∀ (a : arity), q_arity a → new_arity)
  (q : ∀ (a : arity), propagate_struc (q_arity a))
  (x : new_arity → ℕ → Bool):
  (p.compose new_arity q_arity vars q).eval x =
  p.eval (λ a, (q a).eval (fun i => x (vars _ i))) :=
begin
  ext n,
  simp only [eval, compose, propagate_propagate]
end

def and : propagate_struc Bool :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, bits true && bits false) }

@[simp] lemma eval_and (x : Bool → ℕ → Bool) : and.eval x = andSeq (x true) (x false) :=
by ext n; cases n; simp [and, andSeq, eval, propagate_succ]

def or : propagate_struc Bool :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, bits true || bits false) }

@[simp] lemma eval_or (x : Bool → ℕ → Bool) : or.eval x = orSeq (x true) (x false) :=
by ext n; cases n; simp [or, orSeq, eval, propagate_succ]

def xor : propagate_struc Bool :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, bxor (bits true) (bits false)) }

@[simp] lemma eval_xor (x : Bool → ℕ → Bool) : xor.eval x = xorSeq (x true) (x false) :=
by ext n; cases n; simp [xor, xorSeq, eval, propagate_succ]

def add : propagate_struc Bool :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, false,
  next_bit := λ (carry : Unit → Bool) (bits : Bool → Bool),
      (λ _, (bits true && bits false) || (bits false && carry ()) || (bits true && carry ()),
        bxor (bits true) (bxor (bits false) (carry ()))) }

@[simp] lemma eval_add (x : Bool → ℕ → Bool) : add.eval x = add_seq (x true) (x false) :=
begin
  dsimp [add, eval],
  rw [add_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def sub : propagate_struc Bool :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, false,
  next_bit := λ (carry : Unit → Bool) (bits : Bool → Bool),
      (λ _, (bnot (bits true) && (bits false)) ||
        ((bnot (bxor (bits true) (bits false))) && carry ()),
        bxor (bits true) (bxor (bits false) (carry ()))) }

@[simp] lemma eval_sub (x : Bool → ℕ → Bool) : sub.eval x = sub_seq (x true) (x false) :=
begin
  dsimp [sub, eval],
  rw [sub_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def neg : propagate_struc Unit :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, true,
  next_bit := λ (carry : Unit → Bool) (bits : Unit → Bool),
    (λ _, (bnot (bits ())) && (carry ()), bxor (bnot (bits ())) (carry ())) }

@[simp] lemma eval_neg (x : Unit → ℕ → Bool) : neg.eval x = negSeq (x ()) :=
begin
  dsimp [neg, eval],
  rw [neg_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def not : propagate_struc Unit :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, bnot (bits ())) }

@[simp] lemma eval_not (x : Unit → ℕ → Bool) : not.eval x = notSeq (x ()) :=
by ext n; cases n; simp [not, notSeq, eval, propagate_succ]

def zero : propagate_struc (fin 0) :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, false) }

@[simp] lemma eval_zero (x : Fin 0 → ℕ → Bool) : zero.eval x = zeroSeq :=
by ext n; cases n; simp [zero, zeroSeq, eval, propagate_succ]

def one : propagate_struc (fin 0) :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, true,
  next_bit := λ carry bits, (λ _, false, carry ()) }

@[simp] lemma eval_one (x : Fin 0 → ℕ → Bool) : one.eval x = oneSeq :=
by ext n; cases n; simp [one, oneSeq, eval, propagate_succ2]

def neg_one : propagate_struc (fin 0) :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, true) }

@[simp] lemma eval_neg_one (x : Fin 0 → ℕ → Bool) : neg_one.eval x = neg_oneSeq :=
by ext n; cases n; simp [neg_one, neg_oneSeq, eval, propagate_succ2]

def ls : propagate_struc Unit :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, false,
  next_bit := λ carry bits, (bits, carry ()) }

@[simp] lemma eval_ls (x : Unit → ℕ → Bool) : ls.eval x = lsSeq (x ()) :=
by ext n; cases n; simp [ls, lsSeq, eval, propagate_succ2]

def var (n : ℕ) : propagate_struc (fin (n+1)) :=
{ α := empty,
  i := by apply_instance,
  init_carry := Empty.elim,
  next_bit := λ carry bits, (Empty.elim, bits (Fin.last n)) }

@[simp] lemma eval_var (n : ℕ) (x : Fin (n+1) → ℕ → Bool) : (var n).eval x = x (Fin.last n) :=
by ext m; cases m; simp [var, eval, propagate_succ]

def incr : propagate_struc Unit :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, true,
  next_bit := λ carry bits, (λ _, bits () && carry (), bxor (bits ()) (carry ())) }

@[simp] lemma eval_incr (x : Unit → ℕ → Bool) : incr.eval x = incrSeq (x ()) :=
begin
  dsimp [incr, eval],
  rw [incr_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def decr : propagate_struc Unit :=
{ α := Unit,
  i := by apply_instance,
  init_carry := λ _, true,
  next_bit := λ carry bits, (λ _, bnot (bits ()) && carry (), bxor (bits ()) (carry ())) }

@[simp] lemma eval_decr (x : Unit → ℕ → Bool) : decr.eval x = decrSeq (x ()) :=
begin
  dsimp [decr, eval],
  rw [decr_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

end propagate_struc

structure propagate_solution (t : Term) extends propagate_struc (fin (arity t)) :=
( good : t.evalFin = to_propagate_struc.eval )

def compose_unary
  (p : propagate_struc Unit)
  {t : Term}
  (q : propagate_solution t) :
  propagate_struc (fin (arity t)) :=
p.compose
  (fin (arity t))
  _
  (λ _ , id)
  (λ _, q.to_propagate_struc)

def compose_binary
  (p : propagate_struc Bool)
  {t₁ t₂ : Term}
  (q₁ : propagate_solution t₁)
  (q₂ : propagate_solution t₂) :
  propagate_struc (fin (max (arity t₁) (arity t₂))) :=
p.compose (fin (max (arity t₁) (arity t₂)))
  (λ b, fin (cond b (arity t₁) (arity t₂)))
  (λ b i, Fin.castLe (by cases b; simp) i)
  (λ b, Bool.rec q₂.to_propagate_struc q₁.to_propagate_struc b)

@[simp] lemma compose_unary_eval
  (p : propagate_struc Unit)
  {t : Term}
  (q : propagate_solution t)
  (x : Fin (arity t) → ℕ → Bool) :
  (compose_unary p q).eval x = p.eval (λ _, t.evalFin x) :=
begin
  rw [compose_unary, propagate_struc.eval_compose, q.good],
  refl
end

@[simp] lemma compose_binary_eval
  (p : propagate_struc Bool)
  {t₁ t₂ : Term}
  (q₁ : propagate_solution t₁)
  (q₂ : propagate_solution t₂)
  (x : Fin (max (arity t₁) (arity t₂)) → ℕ → Bool) :
  (compose_binary p q₁ q₂).eval x = p.eval
    (λ b, cond b (t₁.evalFin (fun i => x (Fin.castLe (by simp) i)))
                 (t₂.evalFin (fun i => x (Fin.castLe (by simp) i)))) :=
begin
  rw [compose_binary, propagate_struc.eval_compose, q₁.good, q₂.good],
  congr,
  ext b,
  cases b; refl
end

instance {α β : Type*} [fintype α] [fintype β] (b : Bool) :
  fintype (cond b α β) :=
by cases b; dsimp; apply_instance

lemma cond_propagate {α α' β β' : Type}
  (init_carry : α → Bool)
  (next_bit : ∀ (carry : α → Bool) (bits : β → Bool),
    (α → Bool) × Bool)
  (init_carry' : α' → Bool)
  (next_bit' : ∀ (carry : α' → Bool) (bits : β' → Bool),
    (α' → Bool) × Bool)
  {γ : Type} (fβ : β → γ) (fβ' : β' → γ)
  (x : γ → ℕ → Bool) (b : Bool) :
  cond b (propagate init_carry next_bit (λ b, (x (fβ b))))
    (propagate init_carry' next_bit' (λ b, (x (fβ' b)))) =
  propagate (show cond b α α' → Bool, from Bool.rec init_carry' init_carry b)
    (show ∀ (carry : cond b α α' → Bool) (bits : cond b β β' → Bool),
        (cond b α α' → Bool) × Bool,
      from Bool.rec next_bit' next_bit b)
    (show cond b β β' → ℕ → Bool, from Bool.rec (λ b, (x (fβ' b))) (λ b, (x (fβ b))) b) :=
by cases b; refl

def term_eval_eq_propagate : ∀ (t : Term),
  propagate_solution t
| (var n) :=
  { to_propagate_struc := propagate_struc.var n,
    good := by ext; simp [Term.evalFin] }
| zero :=
  { to_propagate_struc := propagate_struc.zero,
    good := by ext; simp [Term.evalFin] }
| one :=
  { to_propagate_struc := propagate_struc.one,
    good := by ext; simp [Term.evalFin] }
| neg_one :=
  { to_propagate_struc := propagate_struc.neg_one,
    good := by ext; simp [Term.evalFin] }
| (and t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.and q₁ q₂,
    good := by ext; simp; refl }
| (or t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.or q₁ q₂,
    good := by ext; simp; refl }
| (xor t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.xor q₁ q₂,
    good := by ext; simp; refl }
| (ls t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.ls q,
    good := by ext; simp; refl }
| (not t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.not q,
    good := by ext; simp; refl }
| (add t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.add q₁ q₂,
    good := by ext; simp; refl }
| (sub t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.sub q₁ q₂,
    good := by ext; simp; refl }
| (neg t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.neg q,
    good := by ext; simp; refl }
| (incr t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.incr q,
    good := by ext; simp; refl }
| (decr t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.decr q,
    good := by ext; simp; refl }

variable
  (init_carry : α → Bool)
  (next_carry : ∀ (carry : α → Bool) (bits : β → Bool), (α → Bool))
  (next_bit : ∀ (carry : α → Bool) (bits : β → Bool), (α → Bool) × Bool)

variables [fintype α] [fintype α']

open fintype

lemma exists_repeat_carry (seq : β → ℕ → Bool) :
  ∃ n m : Fin (2 ^ (card α) + 1),
    propagateCarry2 init_carry next_carry seq n =
    propagateCarry2 init_carry next_carry seq m ∧
    n < m :=
begin
  by_contra h,
  letI : decidable_eq α := classical.dec_eq α,
  push_neg at h,
  have := λ a b hab, (le_antisymm (h a b hab) (h b a hab.symm)).symm,
  simpa using fintype.card_le_of_injective _ this
end

lemma propagateCarry2_eq_of_seq_eq_lt (seq₁ seq₂ : β → ℕ → Bool)
  (init_carry : α → Bool)
  (next_carry : ∀ (carry : α → Bool) (bits : β → Bool), (α → Bool))
  (i : ℕ) (h : ∀ (b) j < i, seq₁ b j = seq₂ b j) :
  propagateCarry2 init_carry next_carry seq₁ i =
    propagateCarry2 init_carry next_carry seq₂ i :=
begin
  induction i with i ih,
  { simp [propagateCarry2] },
  { simp [propagateCarry2, h _ i (nat.lt_succ_self i)],
    rw ih,
    exact λ b j hj, h b j (nat.lt_succ_of_lt hj) }
end

lemma propagate_eq_of_seq_eq_le (seq₁ seq₂ : β → ℕ → Bool)
  (init_carry : α → Bool)
  (next_bit : ∀ (carry : α → Bool) (bits : β → Bool), (α → Bool) × Bool)
  (i : ℕ) (h : ∀ (b) j ≤ i, seq₁ b j = seq₂ b j) :
  propagate init_carry next_bit seq₁ i =
    propagate init_carry next_bit seq₂ i :=
begin
  cases i,
  { simp [propagate_zero, h _ 0 (le_refl _)] },
  { simp only [propagate_succ2, propagate_succ2, h _ _ (le_refl _)],
    congr' 2,
    apply propagateCarry2_eq_of_seq_eq_lt,
    exact λ b j hj, h b j (le_of_lt hj) }
end

lemma propagateCarry2_eq_of_carry_eq (seq₁ seq₂ : β → ℕ → Bool)
  (m n : ℕ)
  (h₁ : propagateCarry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ m =
       propagateCarry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ n) (x : ℕ)
  (h₃ : ∀ y b, y ≤ x → seq₁ b (m + y) = seq₂ b (n + y))  :
  propagateCarry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ (m + x) =
  propagateCarry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ (n + x) :=
begin
  induction x with x ih generalizing seq₁ seq₂,
  { simp * at * },
  { simp only [h₃ x _ (nat.le_succ _),
      nat.add_succ, propagateCarry2, add_zero] at *,
    rw [ih],
    assumption,
    exact λ y b h, h₃ y b (nat.le_succ_of_le h) }
end

lemma propagate_eq_of_carry_eq (seq₁ seq₂ : β → ℕ → Bool)
  (m n : ℕ)
  (h₁ : propagateCarry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ m =
       propagateCarry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ n) (x : ℕ)
  (h₃ : ∀ y b, y ≤ x → seq₁ b (m + y) = seq₂ b (n + y))  :
  propagate init_carry next_bit seq₁ (m + x) =
  propagate init_carry next_bit seq₂ (n + x) :=
begin
  cases x,
  { cases m,
    { cases n,
      { simp [h₃ 0 _ (le_refl _), propagateCarry2, *] at * },
      { simp [*, h₃ 0 _ (le_refl _), propagate_succ2] at *,
        rw [← h₁] } },
    { cases n,
      { simp [*, propagate_succ2] at *,
        simp [← h₃ 0 _ rfl] },
      { rw [propagate_succ2, h₁, propagate_succ2],
        have := h₃ 0,
        simp * at * } } },
  { simp only [nat.add_succ, propagate_succ2, add_zero],
    simp [← nat.add_succ, h₃ _ _ (le_refl _)],
    congr' 2,
    apply propagateCarry2_eq_of_carry_eq,
    assumption,
    assumption }
end

lemma propagateCarry_propagateCarry_add (x : β → ℕ → Bool) :
  ∀ (init_carry : α → Bool)
    (next_carry : ∀ (carry : α → Bool) (bits : β → Bool), (α → Bool)),
  ∀ n i : ℕ,
  propagateCarry2 (propagateCarry2 init_carry next_carry x n)
    next_carry (λ b k, x b (k + n)) i =
  propagateCarry2 init_carry next_carry x (i + n)
| init_carry next_carry 0 0 := by simp [propagateCarry2]
| init_carry next_carry (n+1) 0 :=
  by simp [propagateCarry, propagateCarry2_succ]
| init_carry next_carry n (i+1) := begin
  rw [propagateCarry2, add_assoc,
    propagateCarry_propagateCarry_add],
  simp only [nat.one_add, nat.add_one, nat.succ_add, nat.add_succ,
    add_zero, propagateCarry2, zero_add]
end

lemma exists_repeat : ∀ (seq : β → ℕ → Bool)
  (n : ℕ),
  ∃ (m < 2 ^ (card α)) (seq2 : β → ℕ → Bool),
    propagate init_carry next_bit seq2 m = propagate init_carry next_bit seq n
| seq n :=
begin
  by_cases hn2 : n < 2 ^ card α,
  { exact ⟨n, hn2, seq, rfl⟩ },
  { rcases exists_repeat_carry (propagateCarry2 init_carry (λ c b, (next_bit c b).1) seq
        (n - 2 ^ card α))
      (λ carry bits, (next_bit  carry bits).1)
      (λ b i, seq b (i + (n - 2^ (card α)))) with ⟨a, b, h₁, h₂⟩,
    simp only [propagateCarry_propagateCarry_add] at h₁,
    rcases have wf : n - (b - a) < n,
        from nat.sub_lt (lt_of_lt_of_le (pow_pos two_pos _) (le_of_not_gt hn2))
          (nat.sub_pos_of_lt h₂),
      exists_repeat (λ c i, if i < a + (n - 2 ^ card α) then seq c i else
        seq c (i + (b - a))) (n - (b - a)) with ⟨m, hmle, seq2, hm⟩,
    use [m, hmle, seq2],
    rw [hm], clear hm,
    have h1 : n - (b - a) = (a + (n - 2 ^ (card α))) + (2 ^ card α - b),
    { zify,
      rw [nat.cast_sub, nat.cast_sub, nat.cast_sub, nat.cast_sub],
      ring,
      exact nat.le_of_lt_succ b.2,
      simp * at *,
      exact le_of_lt h₂,
      exact le_trans (nat.sub_le _ _) (le_trans (nat.le_of_lt_succ b.2)
        (by simp * at *)) },
    rw h1,
    have h2 : n = (b + (n - 2 ^ card α)) + (2 ^ card α - b),
    { zify,
      rw [nat.cast_sub, nat.cast_sub],
      ring,
      exact nat.le_of_lt_succ b.2,
      simp * at *, },
    conv_rhs { rw h2 },
    refine propagate_eq_of_carry_eq _ _ _ _ _ _ _ _ _,
    { have h : ↑b + (n - 2 ^ card α) = (a + (n - 2 ^ card α)) + (b - a),
      { zify,
        rw [nat.cast_sub, nat.cast_sub],
        ring,
        exact le_of_lt h₂,
        simp * at * },
      rw [← h₁],
      apply propagateCarry2_eq_of_seq_eq_lt,
      simp { contextual := true } },
    { intros y c hc,
      simp only [add_lt_ifalse_neg_left, not_lt_zero', if_false],
      congr' 1,
      zify,
      rw [nat.cast_sub, nat.cast_sub],
      ring,
      exact le_of_lt h₂,
      simp * at * } },
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩] }

lemma propagate_eq_zero_ifalse (init_carry : α → Bool)
  (next_bit : ∀ (carry : α → Bool) (bits : β → Bool), (α → Bool) × Bool) :
  (∀ seq, propagate init_carry next_bit seq = zeroSeq) ↔
  (∀ seq, ∀ i < 2 ^ (card α), propagate init_carry next_bit seq i = false) :=
begin
  split,
  { intros h i _,
    simp [h, zeroSeq] },
  { intros h seq,
    funext i,
    rcases exists_repeat init_carry next_bit seq i with ⟨j, hj, seq2, hseq2⟩,
    rw [← hseq2, h seq2 j hj, zeroSeq] }
end

lemma eq_ifalse_xorSeq_eq_zero (seq₁ seq₂ : ℕ → Bool) :
  (∀ i, seq₁ i = seq₂ i) ↔ (∀ i, xorSeq seq₁ seq₂ i = zeroSeq i) :=
begin
  simp [function.funext_ifalse, xorSeq, zeroSeq],
  split,
  { intros, simp * },
  { intros h a,
    specialize h a,
    cases (seq₁ a); cases (seq₂ a); simp * at *, }
end

lemma eval_eq_ifalse_xorSeq_eq_zero (t₁ t₂ : Term) :
  t₁.eval = t₂.eval ↔ (t₁.xor t₂).evalFin = λ _, zeroSeq :=
begin
  simp only [function.funext_ifalse, Term.eval, Term.evalFin,
    ← eq_ifalse_xorSeq_eq_zero, ← evalFin_eq_eval],
  split,
  { intros h seq n,
    have := h (λ j, if hj : j < (arity (t₁.xor t₂)) then seq ⟨j, hj⟩ else λ _, false) n,
    simp at this,
    convert this },
  { intros h seq m,
    exact h (λ j, seq j) _ }
end


