def notq1 : instruction :=
  definst "notq" $ do
    pattern fun (v_2883 : reg (bv 64)) => do
      v_4528 <- getRegister v_2883;
      setRegister (lhs.of_reg v_2883) (bv_xor v_4528 (mi (bitwidthMInt v_4528) -1));
      pure ()
    pat_end;
    pattern fun (v_2879 : Mem) => do
      v_11150 <- evaluateAddress v_2879;
      v_11151 <- load v_11150 8;
      store v_11150 (bv_xor v_11151 (mi (bitwidthMInt v_11151) -1)) 8;
      pure ()
    pat_end
