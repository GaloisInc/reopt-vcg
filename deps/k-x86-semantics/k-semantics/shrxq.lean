def shrxq : instruction :=
  definst "shrxq" $ do
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
