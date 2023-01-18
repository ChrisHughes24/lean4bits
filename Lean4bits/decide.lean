import lemmas

open fintype

instance decidable_eval_eq (t₁ t₂ : term) :
  decidable (t₁.eval = t₂.eval) :=
begin
  let p := term_eval_eq_propagate (t₁.xor t₂),
  letI := p.i,
  let c := 2 ^ card p.α,
  let ar := arity (t₁.xor t₂),
  refine decidable_of_iff
    (∀ (seq : fin ar → fin c → bool)
      (i : fin c),
      (t₁.xor t₂).eval
      (λ i j, if hij : i < ar ∧ j < c
        then seq ⟨i, hij.1⟩ ⟨j, hij.2⟩ else ff) i = ff) _,
  rw [eval_eq_iff_xor_seq_eq_zero, p.good, propagate_struc.eval],
  rw [function.funext_iff, propagate_eq_zero_iff],
  simp only [← eval_fin_eq_eval, p.good],
  split,
  { intros h seq i hi,
    rw ← h (λ i j, seq i j) ⟨i, hi⟩,
    apply propagate_eq_of_seq_eq_le,
    intros b j hj,
    simp [lt_of_le_of_lt hj hi] },
  { intros h seq i,
    rw [propagate_struc.eval, h],
    exact i.2 }
end

def decide (t₁ t₂ : term) : bool :=
t₁.eval = t₂.eval
