namespace reader_t

instance is_monad_state {s : Type _} {m : Type _ → Type _} {ρ: Type _} [monad_state s m]
: monad_state s (reader_t ρ m) :=
{ lift := λ_ f, ⟨λr, monad_state.lift f⟩
}

end reader_t
