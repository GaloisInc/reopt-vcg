def andnq1 : instruction :=
  definst "andnq" $ do
    pattern fun (v_2826 : reg (bv 64)) (v_2827 : reg (bv 64)) (v_2828 : reg (bv 64)) => do
      v_5596 <- getRegister v_2827;
      v_5599 <- getRegister v_2826;
      v_5603 <- eval (bv_and (bv_xor v_5596 (expression.bv_nat 64 18446744073709551615)) v_5599);
      setRegister (lhs.of_reg v_2828) v_5603;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5603);
      setRegister af undef;
      setRegister sf (bv_and (bv_xor (extract v_5596 0 1) (expression.bv_nat 1 1)) (extract v_5599 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 64)) (v_2822 : reg (bv 64)) => do
      v_9676 <- getRegister v_2821;
      v_9679 <- evaluateAddress v_2820;
      v_9680 <- load v_9679 8;
      v_9684 <- eval (bv_and (bv_xor v_9676 (expression.bv_nat 64 18446744073709551615)) v_9680);
      setRegister (lhs.of_reg v_2822) v_9684;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9684);
      setRegister sf (bv_and (bv_xor (extract v_9676 0 1) (expression.bv_nat 1 1)) (extract v_9680 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
