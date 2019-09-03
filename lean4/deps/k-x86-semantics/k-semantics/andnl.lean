def andnl1 : instruction :=
  definst "andnl" $ do
    pattern fun (v_2797 : reg (bv 32)) (v_2798 : reg (bv 32)) (v_2799 : reg (bv 32)) => do
      v_5557 <- getRegister v_2798;
      v_5560 <- getRegister v_2797;
      v_5564 <- eval (bv_and (bv_xor v_5557 (expression.bv_nat 32 4294967295)) v_5560);
      setRegister (lhs.of_reg v_2799) v_5564;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5564);
      setRegister af undef;
      setRegister sf (bv_and (bv_xor (extract v_5557 0 1) (expression.bv_nat 1 1)) (extract v_5560 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2791 : Mem) (v_2792 : reg (bv 32)) (v_2793 : reg (bv 32)) => do
      v_9647 <- getRegister v_2792;
      v_9650 <- evaluateAddress v_2791;
      v_9651 <- load v_9650 4;
      v_9655 <- eval (bv_and (bv_xor v_9647 (expression.bv_nat 32 4294967295)) v_9651);
      setRegister (lhs.of_reg v_2793) v_9655;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9655);
      setRegister af undef;
      setRegister sf (bv_and (bv_xor (extract v_9647 0 1) (expression.bv_nat 1 1)) (extract v_9651 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
