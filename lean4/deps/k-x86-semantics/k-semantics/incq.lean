def incq1 : instruction :=
  definst "incq" $ do
    pattern fun (v_3055 : reg (bv 64)) => do
      v_5264 <- getRegister v_3055;
      v_5265 <- eval (add v_5264 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_3055) v_5265;
      setRegister af (eq (extract v_5264 60 64) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_5264 0)) (eq (extract v_5264 1 64) (expression.bv_nat 63 9223372036854775807)));
      setRegister pf (parityFlag (extract v_5265 56 64));
      setRegister sf (isBitSet v_5265 0);
      setRegister zf (zeroFlag v_5265);
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) => do
      v_9183 <- evaluateAddress v_3052;
      v_9184 <- load v_9183 8;
      v_9185 <- eval (add v_9184 (expression.bv_nat 64 1));
      store v_9183 v_9185 8;
      setRegister af (eq (extract v_9184 60 64) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_9184 0)) (eq (extract v_9184 1 64) (expression.bv_nat 63 9223372036854775807)));
      setRegister pf (parityFlag (extract v_9185 56 64));
      setRegister sf (isBitSet v_9185 0);
      setRegister zf (zeroFlag v_9185);
      pure ()
    pat_end
