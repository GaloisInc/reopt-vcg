def blsmskq1 : instruction :=
  definst "blsmskq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      v_4 <- eval (bv_xor (sub v_3 (expression.bv_nat 64 1)) v_3);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf (eq v_3 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_4 0);
      setRegister zf bit_zero;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_0;
      v_3 <- eval (bv_xor (sub v_2 (expression.bv_nat 64 1)) v_2);
      setRegister (lhs.of_reg r64_1) v_3;
      setRegister af undef;
      setRegister cf (eq v_2 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_3 0);
      setRegister zf bit_zero;
      pure ()
    pat_end
