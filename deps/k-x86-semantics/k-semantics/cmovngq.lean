def cmovngq : instruction :=
  definst "cmovngq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister zf;
      let v_3 <- getRegister sf;
      let v_4 <- getRegister of;
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 8;
      let v_7 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (bit_or v_2 (notBool_ (eq v_3 v_4))) v_6 v_7);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister zf;
      let v_3 <- getRegister sf;
      let v_4 <- getRegister of;
      let v_5 <- getRegister (lhs.of_reg r64_0);
      let v_6 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (bit_or v_2 (notBool_ (eq v_3 v_4))) v_5 v_6);
      pure ()
     action
