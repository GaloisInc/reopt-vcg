def decq1 : instruction :=
  definst "decq" $ do
    pattern fun (v_2783 : reg (bv 64)) => do
      v_4448 <- getRegister v_2783;
      v_4449 <- eval (sub v_4448 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2783) v_4449;
      setRegister af (eq (extract v_4448 60 64) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4448 0) (eq (extract v_4448 1 64) (expression.bv_nat 63 0)));
      setRegister pf (parityFlag (extract v_4449 56 64));
      setRegister sf (isBitSet v_4449 0);
      setRegister zf (zeroFlag v_4449);
      pure ()
    pat_end;
    pattern fun (v_2780 : Mem) => do
      v_9105 <- evaluateAddress v_2780;
      v_9106 <- load v_9105 8;
      v_9107 <- eval (sub v_9106 (expression.bv_nat 64 1));
      store v_9105 v_9107 8;
      setRegister af (eq (extract v_9106 60 64) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9106 0) (eq (extract v_9106 1 64) (expression.bv_nat 63 0)));
      setRegister pf (parityFlag (extract v_9107 56 64));
      setRegister sf (isBitSet v_9107 0);
      setRegister zf (zeroFlag v_9107);
      pure ()
    pat_end
