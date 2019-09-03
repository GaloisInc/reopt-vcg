def decq1 : instruction :=
  definst "decq" $ do
    pattern fun (v_2692 : reg (bv 64)) => do
      v_4428 <- getRegister v_2692;
      v_4429 <- eval (sub v_4428 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2692) v_4429;
      setRegister of (mux (bit_and (eq (extract v_4428 0 1) (expression.bv_nat 1 1)) (eq (extract v_4428 1 64) (expression.bv_nat 63 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4429 56 64));
      setRegister af (mux (eq (extract v_4428 60 64) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4429);
      setRegister sf (extract v_4429 0 1);
      pure ()
    pat_end;
    pattern fun (v_2689 : Mem) => do
      v_9463 <- evaluateAddress v_2689;
      v_9464 <- load v_9463 8;
      v_9465 <- eval (sub v_9464 (expression.bv_nat 64 1));
      store v_9463 v_9465 8;
      setRegister of (mux (bit_and (eq (extract v_9464 0 1) (expression.bv_nat 1 1)) (eq (extract v_9464 1 64) (expression.bv_nat 63 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9465 56 64));
      setRegister af (mux (eq (extract v_9464 60 64) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9465);
      setRegister sf (extract v_9465 0 1);
      pure ()
    pat_end
