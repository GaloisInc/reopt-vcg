def andnps1 : instruction :=
  definst "andnps" $ do
    pattern fun (v_2803 : reg (bv 128)) (v_2804 : reg (bv 128)) => do
      v_5415 <- getRegister v_2804;
      v_5419 <- getRegister v_2803;
      setRegister (lhs.of_reg v_2804) (bv_and (bv_xor v_5415 (mi (bitwidthMInt v_5415) -1)) v_5419);
      pure ()
    pat_end;
    pattern fun (v_2798 : Mem) (v_2799 : reg (bv 128)) => do
      v_9368 <- getRegister v_2799;
      v_9372 <- evaluateAddress v_2798;
      v_9373 <- load v_9372 16;
      setRegister (lhs.of_reg v_2799) (bv_and (bv_xor v_9368 (mi (bitwidthMInt v_9368) -1)) v_9373);
      pure ()
    pat_end
