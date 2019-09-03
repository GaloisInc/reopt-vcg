def notl1 : instruction :=
  definst "notl" $ do
    pattern fun (v_2876 : reg (bv 32)) => do
      v_4520 <- getRegister v_2876;
      setRegister (lhs.of_reg v_2876) (bv_xor v_4520 (mi (bitwidthMInt v_4520) -1));
      pure ()
    pat_end;
    pattern fun (v_2872 : Mem) => do
      v_11144 <- evaluateAddress v_2872;
      v_11145 <- load v_11144 4;
      store v_11144 (bv_xor v_11145 (mi (bitwidthMInt v_11145) -1)) 4;
      pure ()
    pat_end
