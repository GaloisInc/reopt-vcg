import system.io
import .file_writer
import .semantics
import .theories.bv

section quantifiers
variables {α : Sort*} {p q : α → Prop} {b : Prop}

@[simp] theorem exists_imp_distrib : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
⟨λ h x hpx, h ⟨x, hpx⟩, λ h ⟨x, hpx⟩, h x hpx⟩

@[simp] theorem not_exists : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
exists_imp_distrib

end quantifiers

open smt2

/- Generte a proble mtaht asserts a constant x is equal to 3. -/
def generate_problem {m} [is_generator m ] : m unit := do
  let x := symbol.of_string "x",
  declare_const x (BitVec 32),
  assert (all_equal [var x (BitVec 32), bv.decimal (bitvec.of_nat 32 3)]),
  check_sat

/- This actually generates the SMTLIB file. -/
def main : io unit := do
  smt2.file_writer.run "bar.smt2" $ do
    generate_problem

/-
This will either report an error because the problem is not well-formed, or
return the property implied by the program.
-/
def mkprop : except string Prop := semantics.run_and_collect_unsat generate_problem

/- This is a hack to show that mkprop can be evaluated into a simpler proof. -/
example : mkprop = except.ok (¬∃(x : bitvec 32), x = bitvec.of_nat 32 3) :=
begin
  simp only
       [ mkprop
       , semantics.run_and_collect_unsat
       , id
       , generate_problem
       , declare_const
       , is_generator.declare_const
       , semantics.context.initial
       , semantics.declare_fun
       , semantics.register_symbol
       , semantics.context.add_binding
       , smt2.assert, is_generator.assert, semantics.assert
       , all_equal
       , check_sat, is_generator.check_sat, semantics.check_sat
       , semantics.check_sat_assuming
       , semantics.quantify_bindings
       , semantics.quantify_binding
       , pure, has_bind.bind
       , except.return
       , except.bind
       , except.map_poly
       , put
       , pwhen
       , mk_rbmap, mk_rbtree
       , has_mem.mem, rbmap.mem
       , get
       , state_t.pure, modify, state_t.modify, state_t.bind, state_t.get, state_t.put
       , monad_state.lift
       , list.forall_prop
       , list.reverse_core
       , interpretation.bind
       , apply_chainable
       , all_band
       , smt2.var
       , interpretation.lookup_var
       , rbmap.insert, rbtree.insert
       , has_emptyc.emptyc
       , interpretation.empty
       , rbmap.find
       , rbmap.find_entry
       , rbnode.find
       , rbnode.insert
       , rbnode.ins
       , rbnode.get_color
       , rbnode.mk_insert_result
       , rbtree.find
       , cmp_using, rbmap_lt
       , symbol.lt
       , symbol.of_string
       , except.is_ok.value
       , string.to_char_buffer
       , buffer.append_string
       , buffer.nil
       , rbmap.to_value
       , bv.decimal
       , if_false
       , list.map
       , dif_pos
       , band_tt
       , and_true
       , not_exists
       , coe_sort
       , to_bool_iff
       , cast
       ],
  exact rfl,
end
