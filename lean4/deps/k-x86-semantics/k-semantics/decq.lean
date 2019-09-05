def decq1 : instruction :=
  definst "decq" $ do
    pattern fun (v_2756 : reg (bv 64)) => do
      v_4427 <- getRegister v_2756;
      v_4428 <- eval (sub v_4427 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2756) v_4428;
      setRegister af (eq (extract v_4427 60 64) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4427 0) (eq (extract v_4427 1 64) (expression.bv_nat 63 0)));
      setRegister pf (parityFlag (extract v_4428 56 64));
      setRegister sf (isBitSet v_4428 0);
      setRegister zf (zeroFlag v_4428);
      pure ()
    pat_end;
    pattern fun (v_2753 : Mem) => do
      v_9095 <- evaluateAddress v_2753;
      v_9096 <- load v_9095 8;
      v_9097 <- eval (sub v_9096 (expression.bv_nat 64 1));
      store v_9095 v_9097 8;
      setRegister af (eq (extract v_9096 60 64) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9096 0) (eq (extract v_9096 1 64) (expression.bv_nat 63 0)));
      setRegister pf (parityFlag (extract v_9097 56 64));
      setRegister sf (isBitSet v_9097 0);
      setRegister zf (zeroFlag v_9097);
      pure ()
    pat_end
