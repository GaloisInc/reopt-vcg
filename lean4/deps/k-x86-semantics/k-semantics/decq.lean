def decq1 : instruction :=
  definst "decq" $ do
    pattern fun (v_2704 : reg (bv 64)) => do
      v_4448 <- getRegister v_2704;
      v_4449 <- eval (sub v_4448 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2704) v_4449;
      setRegister of (mux (bit_and (eq (extract v_4448 0 1) (expression.bv_nat 1 1)) (eq (extract v_4448 1 64) (expression.bv_nat 63 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4449 56 64));
      setRegister af (mux (eq (extract v_4448 60 64) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4449);
      setRegister sf (extract v_4449 0 1);
      pure ()
    pat_end;
    pattern fun (v_2700 : Mem) => do
      v_10053 <- evaluateAddress v_2700;
      v_10054 <- load v_10053 8;
      v_10055 <- eval (sub v_10054 (expression.bv_nat 64 1));
      store v_10053 v_10055 8;
      setRegister of (mux (bit_and (eq (extract v_10054 0 1) (expression.bv_nat 1 1)) (eq (extract v_10054 1 64) (expression.bv_nat 63 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10055 56 64));
      setRegister af (mux (eq (extract v_10054 60 64) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10055);
      setRegister sf (extract v_10055 0 1);
      pure ()
    pat_end
