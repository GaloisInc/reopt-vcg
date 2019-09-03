def andnq1 : instruction :=
  definst "andnq" $ do
    pattern fun (v_2813 : reg (bv 64)) (v_2814 : reg (bv 64)) (v_2815 : reg (bv 64)) => do
      v_5427 <- getRegister v_2814;
      v_5428 <- eval (extract v_5427 0 1);
      v_5432 <- getRegister v_2813;
      v_5438 <- eval (bv_and (bv_xor v_5427 (mi (bitwidthMInt v_5427) -1)) v_5432);
      setRegister (lhs.of_reg v_2815) v_5438;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5438);
      setRegister af undef;
      setRegister sf (bv_and (bv_xor v_5428 (mi (bitwidthMInt v_5428) -1)) (extract v_5432 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2807 : Mem) (v_2808 : reg (bv 64)) (v_2809 : reg (bv 64)) => do
      v_9376 <- getRegister v_2808;
      v_9377 <- eval (extract v_9376 0 1);
      v_9381 <- evaluateAddress v_2807;
      v_9382 <- load v_9381 8;
      v_9388 <- eval (bv_and (bv_xor v_9376 (mi (bitwidthMInt v_9376) -1)) v_9382);
      setRegister (lhs.of_reg v_2809) v_9388;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9388);
      setRegister sf (bv_and (bv_xor v_9377 (mi (bitwidthMInt v_9377) -1)) (extract v_9382 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
