def decw1 : instruction :=
  definst "decw" $ do
    pattern fun (v_2699 : reg (bv 16)) => do
      v_4452 <- getRegister v_2699;
      v_4453 <- eval (sub v_4452 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_2699) v_4453;
      setRegister of (mux (bit_and (eq (extract v_4452 0 1) (expression.bv_nat 1 1)) (eq (extract v_4452 1 16) (expression.bv_nat 15 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4453 8 16));
      setRegister af (mux (eq (extract v_4452 12 16) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4453);
      setRegister sf (extract v_4453 0 1);
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) => do
      v_9485 <- evaluateAddress v_2696;
      v_9486 <- load v_9485 2;
      v_9487 <- eval (sub v_9486 (expression.bv_nat 16 1));
      store v_9485 v_9487 2;
      setRegister of (mux (bit_and (eq (extract v_9486 0 1) (expression.bv_nat 1 1)) (eq (extract v_9486 1 16) (expression.bv_nat 15 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9487 8 16));
      setRegister af (mux (eq (extract v_9486 12 16) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9487);
      setRegister sf (extract v_9487 0 1);
      pure ()
    pat_end
