def mulxq : instruction :=
  definst "mulxq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- eval (concat (expression.bv_nat 64 0) v_3);
      let v_5 <- load v_3 8;
      let v_6 <- eval (concat (expression.bv_nat 64 0) v_5);
      let v_7 <- eval (mul v_4 v_6);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_7 0 64);
      setRegister (lhs.of_reg r64_2) v_9;
      setRegister (lhs.of_reg r64_1) v_8;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister rdx;
      let v_4 <- eval (concat (expression.bv_nat 64 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r64_0);
      let v_6 <- eval (concat (expression.bv_nat 64 0) v_5);
      let v_7 <- eval (mul v_4 v_6);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_7 0 64);
      setRegister (lhs.of_reg r64_2) v_9;
      setRegister (lhs.of_reg r64_1) v_8;
      pure ()
     action
