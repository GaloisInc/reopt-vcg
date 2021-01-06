def shrx : instruction :=
  definst "shrx" $ do
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 4;
      let v_5 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_2) (lshr v_4 (bv_and v_5 (expression.bv_nat 32 31)));
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_1);
      let v_4 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_2) (lshr v_3 (bv_and v_4 (expression.bv_nat 32 31)));
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 8;
      let v_5 <- eval (concat v_4 (expression.bv_nat 1 0));
      let v_6 <- getRegister (lhs.of_reg r64_0);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 56 64);
      let v_8 <- eval (concat (expression.bv_nat 57 0) (bv_and v_7 (expression.bv_nat 8 63)));
      let (v_9 : expression (bv 64)) <- eval (extract (lshr v_5 v_8) 0 64);
      setRegister (lhs.of_reg r64_2) v_9;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r64_1);
      let v_4 <- eval (concat v_3 (expression.bv_nat 1 0));
      let v_5 <- getRegister (lhs.of_reg r64_0);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_7 <- eval (concat (expression.bv_nat 57 0) (bv_and v_6 (expression.bv_nat 8 63)));
      let (v_8 : expression (bv 64)) <- eval (extract (lshr v_4 v_7) 0 64);
      setRegister (lhs.of_reg r64_2) v_8;
      pure ()
     action
