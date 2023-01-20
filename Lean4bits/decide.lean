import Lean4bits.lemmas

open Fintype

instance decidableEvalEq (t₁ t₂ : Term) :
    Decidable (t₁.eval = t₂.eval) := by
  let p := termEvalEqPropagate (t₁.xor t₂)
  letI := p.i
  let c := 2 ^ card p.α
  let ar := arity (t₁.xor t₂)
  refine' decidable_of_iff
    (∀ (seq : Fin ar → Fin c → Bool)
      (i : Fin c),
      (t₁.xor t₂).eval
      (λ i j => if hij : i < ar ∧ j < c
        then seq ⟨i, hij.1⟩ ⟨j, hij.2⟩ else false) i = false) _
  rw [eval_eq_iff_xorSeq_eq_zero, p.good, PropagateStruc.eval]
  rw [Function.funext_iff, propagate_eq_zero_iff]
  simp only [← evalFin_eq_eval, p.good]
  constructor
  { intro h seq i hi
    rw [← h (λ i j => seq i j) ⟨i, hi⟩]
    apply propagate_eq_of_seq_eq_le
    intro b j hj
    rw [dif_pos ]
    have := (lt_of_le_of_lt hj hi)
    refine' ⟨b.2, this⟩ }
  { intro h seq i
    rw [PropagateStruc.eval, h]
    exact i.2 }


def decide (t₁ t₂ : Term) : Bool :=
  t₁.eval = t₂.eval
