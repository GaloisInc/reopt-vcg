def leaq : instruction :=
  definst "leaq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      setRegister (lhs.of_reg r64_1) v_2;
      pure ()
     action
