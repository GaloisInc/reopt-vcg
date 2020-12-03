def shlxq : instruction :=
  definst "shlxq" $ do
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 8;
      let v_5 <- getRegister (lhs.of_reg r64_0);
      let (v_6 : expression (bv 64)) <- eval (extract (shl v_4 (bv_and v_5 (expression.bv_nat 64 63))) 0 64);
      setRegister (lhs.of_reg r64_2) v_6;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r64_1);
      let v_4 <- getRegister (lhs.of_reg r64_0);
      let (v_5 : expression (bv 64)) <- eval (extract (shl v_3 (bv_and v_4 (expression.bv_nat 64 63))) 0 64);
      setRegister (lhs.of_reg r64_2) v_5;
      pure ()
     action
