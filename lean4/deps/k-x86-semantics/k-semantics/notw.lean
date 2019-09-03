def notw1 : instruction :=
  definst "notw" $ do
    pattern fun (v_2890 : reg (bv 16)) => do
      v_4536 <- getRegister v_2890;
      setRegister (lhs.of_reg v_2890) (bv_xor v_4536 (mi (bitwidthMInt v_4536) -1));
      pure ()
    pat_end;
    pattern fun (v_2886 : Mem) => do
      v_11156 <- evaluateAddress v_2886;
      v_11157 <- load v_11156 2;
      store v_11156 (bv_xor v_11157 (mi (bitwidthMInt v_11157) -1)) 2;
      pure ()
    pat_end
