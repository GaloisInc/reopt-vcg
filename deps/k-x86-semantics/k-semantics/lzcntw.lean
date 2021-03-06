def lzcntw : instruction :=
  definst "lzcntw" $ do
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let v_4 <- eval (mux (isBitSet v_3 0) (expression.bv_nat 16 0) (mux (isBitSet v_3 1) (expression.bv_nat 16 1) (mux (isBitSet v_3 2) (expression.bv_nat 16 2) (mux (isBitSet v_3 3) (expression.bv_nat 16 3) (mux (isBitSet v_3 4) (expression.bv_nat 16 4) (mux (isBitSet v_3 5) (expression.bv_nat 16 5) (mux (isBitSet v_3 6) (expression.bv_nat 16 6) (mux (isBitSet v_3 7) (expression.bv_nat 16 7) (mux (isBitSet v_3 8) (expression.bv_nat 16 8) (mux (isBitSet v_3 9) (expression.bv_nat 16 9) (mux (isBitSet v_3 10) (expression.bv_nat 16 10) (mux (isBitSet v_3 11) (expression.bv_nat 16 11) (mux (isBitSet v_3 12) (expression.bv_nat 16 12) (mux (isBitSet v_3 13) (expression.bv_nat 16 13) (mux (isBitSet v_3 14) (expression.bv_nat 16 14) (mux (isBitSet v_3 15) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg r16_1) v_4;
      setRegister af undef;
      setRegister cf (eq v_4 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_4);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_0);
      let v_3 <- eval (mux (isBitSet v_2 0) (expression.bv_nat 16 0) (mux (isBitSet v_2 1) (expression.bv_nat 16 1) (mux (isBitSet v_2 2) (expression.bv_nat 16 2) (mux (isBitSet v_2 3) (expression.bv_nat 16 3) (mux (isBitSet v_2 4) (expression.bv_nat 16 4) (mux (isBitSet v_2 5) (expression.bv_nat 16 5) (mux (isBitSet v_2 6) (expression.bv_nat 16 6) (mux (isBitSet v_2 7) (expression.bv_nat 16 7) (mux (isBitSet v_2 8) (expression.bv_nat 16 8) (mux (isBitSet v_2 9) (expression.bv_nat 16 9) (mux (isBitSet v_2 10) (expression.bv_nat 16 10) (mux (isBitSet v_2 11) (expression.bv_nat 16 11) (mux (isBitSet v_2 12) (expression.bv_nat 16 12) (mux (isBitSet v_2 13) (expression.bv_nat 16 13) (mux (isBitSet v_2 14) (expression.bv_nat 16 14) (mux (isBitSet v_2 15) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg r16_1) v_3;
      setRegister af undef;
      setRegister cf (eq v_3 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_3);
      pure ()
     action
