def mulxl : instruction :=
  definst "mulxl" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- load v_3 4;
      let v_7 <- eval (concat (expression.bv_nat 32 0) v_6);
      let v_8 <- eval (mul v_5 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_8 0 32);
      setRegister (lhs.of_reg r32_2) v_10;
      setRegister (lhs.of_reg r32_1) v_9;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister rdx;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- getRegister (lhs.of_reg r32_0);
      let v_7 <- eval (concat (expression.bv_nat 32 0) v_6);
      let v_8 <- eval (mul v_5 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_8 32 64);
      setRegister (lhs.of_reg r32_1) v_10;
      setRegister (lhs.of_reg r32_2) v_9;
      pure ()
     action
