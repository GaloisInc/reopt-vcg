def blsrq1 : instruction :=
  definst "blsrq" $ do
    pattern fun (v_3090 : reg (bv 64)) (v_3091 : reg (bv 64)) => do
      v_5790 <- getRegister v_3090;
      v_5792 <- eval (bv_and (sub v_5790 (expression.bv_nat 64 1)) v_5790);
      setRegister (lhs.of_reg v_3091) v_5792;
      setRegister af undef;
      setRegister cf (eq v_5790 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5792 0);
      setRegister zf (zeroFlag v_5792);
      pure ()
    pat_end;
    pattern fun (v_3086 : Mem) (v_3087 : reg (bv 64)) => do
      v_9260 <- evaluateAddress v_3086;
      v_9261 <- load v_9260 8;
      v_9263 <- eval (bv_and (sub v_9261 (expression.bv_nat 64 1)) v_9261);
      setRegister (lhs.of_reg v_3087) v_9263;
      setRegister af undef;
      setRegister cf (eq v_9261 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9263 0);
      setRegister zf (zeroFlag v_9263);
      pure ()
    pat_end
