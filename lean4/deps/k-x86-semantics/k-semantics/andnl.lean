def andnl1 : instruction :=
  definst "andnl" $ do
    pattern fun (v_2784 : reg (bv 32)) (v_2785 : reg (bv 32)) (v_2786 : reg (bv 32)) => do
      v_5380 <- getRegister v_2785;
      v_5381 <- eval (extract v_5380 0 1);
      v_5385 <- getRegister v_2784;
      v_5391 <- eval (bv_and (bv_xor v_5380 (mi (bitwidthMInt v_5380) -1)) v_5385);
      setRegister (lhs.of_reg v_2786) v_5391;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_5391);
      setRegister sf (bv_and (bv_xor v_5381 (mi (bitwidthMInt v_5381) -1)) (extract v_5385 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2778 : Mem) (v_2779 : reg (bv 32)) (v_2780 : reg (bv 32)) => do
      v_9339 <- getRegister v_2779;
      v_9340 <- eval (extract v_9339 0 1);
      v_9344 <- evaluateAddress v_2778;
      v_9345 <- load v_9344 4;
      v_9351 <- eval (bv_and (bv_xor v_9339 (mi (bitwidthMInt v_9339) -1)) v_9345);
      setRegister (lhs.of_reg v_2780) v_9351;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9351);
      setRegister af undef;
      setRegister sf (bv_and (bv_xor v_9340 (mi (bitwidthMInt v_9340) -1)) (extract v_9345 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
