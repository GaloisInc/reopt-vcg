def blsrl1 : instruction :=
  definst "blsrl" $ do
    pattern fun (v_3004 : reg (bv 32)) (v_3005 : reg (bv 32)) => do
      v_6125 <- getRegister v_3004;
      v_6128 <- eval (sub v_6125 (expression.bv_nat 32 1));
      v_6132 <- eval (bv_and v_6128 v_6125);
      setRegister (lhs.of_reg v_3005) v_6132;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_6132);
      setRegister af undef;
      setRegister sf (bv_and (extract v_6128 0 1) (extract v_6125 0 1));
      setRegister cf (mux (eq v_6125 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2999 : Mem) (v_3000 : reg (bv 32)) => do
      v_9949 <- evaluateAddress v_2999;
      v_9950 <- load v_9949 4;
      v_9953 <- eval (sub v_9950 (expression.bv_nat 32 1));
      v_9957 <- eval (bv_and v_9953 v_9950);
      setRegister (lhs.of_reg v_3000) v_9957;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9957);
      setRegister af undef;
      setRegister sf (bv_and (extract v_9953 0 1) (extract v_9950 0 1));
      setRegister cf (mux (eq v_9950 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
