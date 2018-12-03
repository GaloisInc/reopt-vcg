/-
This defines functionality that could be in data.rbmap
-/
namespace rbnode
universes u
variables {α : Type u}

variable (lt : α → α → Prop)

instance mem.decidable [h : decidable_rel lt] (a : α) (m:rbnode α) : decidable (rbnode.mem lt a m) :=
begin
  induction m,
  { simp [mem], apply_instance },
  { let p := h a m_val,
    let q := h m_val a,
    exact @or.decidable _ _
      m_ih_lchild
      (@or.decidable _ _ (@and.decidable _ _ (@not.decidable _ p) (@not.decidable _ q)) m_ih_rchild),
  },
  { let p := h a m_val,
    let q := h m_val a,
    exact
      @or.decidable _ _
        m_ih_lchild
        (@or.decidable _ _ (@and.decidable _ _ (@not.decidable _ p) (@not.decidable _ q)) m_ih_rchild),
  },
end

end rbnode
