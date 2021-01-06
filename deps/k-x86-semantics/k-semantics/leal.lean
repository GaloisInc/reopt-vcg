def leal : instruction :=
  definst "leal" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      setRegister (lhs.of_reg r32_1) v_3;
      pure ()
     action
