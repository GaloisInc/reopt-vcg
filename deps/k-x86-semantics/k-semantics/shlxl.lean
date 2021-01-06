def shlxl : instruction :=
  definst "shlxl" $ do
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 4;
      let v_5 <- getRegister (lhs.of_reg r32_0);
      let (v_6 : expression (bv 32)) <- eval (extract (shl v_4 (bv_and v_5 (expression.bv_nat 32 31))) 0 32);
      setRegister (lhs.of_reg r32_2) v_6;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_1);
      let v_4 <- getRegister (lhs.of_reg r32_0);
      let (v_5 : expression (bv 32)) <- eval (extract (shl v_3 (bv_and v_4 (expression.bv_nat 32 31))) 0 32);
      setRegister (lhs.of_reg r32_2) v_5;
      pure ()
     action
