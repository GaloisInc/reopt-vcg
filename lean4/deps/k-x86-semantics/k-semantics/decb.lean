def decb1 : instruction :=
  definst "decb" $ do
    pattern fun (v_2674 : reg (bv 8)) => do
      v_4359 <- getRegister v_2674;
      v_4360 <- eval (sub v_4359 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2674) v_4360;
      setRegister of (mux (bit_and (eq (extract v_4359 0 1) (expression.bv_nat 1 1)) (eq (extract v_4359 1 8) (expression.bv_nat 7 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4360 0 8));
      setRegister af (mux (eq (extract v_4359 4 8) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4360);
      setRegister sf (extract v_4360 0 1);
      pure ()
    pat_end;
    pattern fun (v_2678 : reg (bv 8)) => do
      v_4380 <- getRegister v_2678;
      v_4381 <- eval (sub v_4380 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2678) v_4381;
      setRegister of (mux (bit_and (eq (extract v_4380 0 1) (expression.bv_nat 1 1)) (eq (extract v_4380 1 8) (expression.bv_nat 7 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4381 0 8));
      setRegister zf (zeroFlag v_4381);
      setRegister af (mux (eq (extract v_4380 4 8) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_4381 0 1);
      pure ()
    pat_end;
    pattern fun (v_2671 : Mem) => do
      v_9419 <- evaluateAddress v_2671;
      v_9420 <- load v_9419 1;
      v_9421 <- eval (sub v_9420 (expression.bv_nat 8 1));
      store v_9419 v_9421 1;
      setRegister of (mux (bit_and (eq (extract v_9420 0 1) (expression.bv_nat 1 1)) (eq (extract v_9420 1 8) (expression.bv_nat 7 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9421 0 8));
      setRegister af (mux (eq (extract v_9420 4 8) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9421);
      setRegister sf (extract v_9421 0 1);
      pure ()
    pat_end
