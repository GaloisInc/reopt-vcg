def decb1 : instruction :=
  definst "decb" $ do
    pattern fun (v_2742 : reg (bv 8)) => do
      v_4385 <- getRegister v_2742;
      v_4386 <- eval (sub v_4385 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2742) v_4386;
      setRegister af (eq (extract v_4385 4 8) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4385 0) (eq (extract v_4385 1 8) (expression.bv_nat 7 0)));
      setRegister pf (parityFlag (extract v_4386 0 8));
      setRegister sf (isBitSet v_4386 0);
      setRegister zf (zeroFlag v_4386);
      pure ()
    pat_end;
    pattern fun (v_2735 : Mem) => do
      v_9057 <- evaluateAddress v_2735;
      v_9058 <- load v_9057 1;
      v_9059 <- eval (sub v_9058 (expression.bv_nat 8 1));
      store v_9057 v_9059 1;
      setRegister af (eq (extract v_9058 4 8) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9058 0) (eq (extract v_9058 1 8) (expression.bv_nat 7 0)));
      setRegister pf (parityFlag (extract v_9059 0 8));
      setRegister sf (isBitSet v_9059 0);
      setRegister zf (zeroFlag v_9059);
      pure ()
    pat_end
