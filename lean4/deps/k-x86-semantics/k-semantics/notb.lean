def notb1 : instruction :=
  definst "notb" $ do
    pattern fun (v_2865 : reg (bv 8)) => do
      v_4507 <- getRegister v_2865;
      setRegister (lhs.of_reg v_2865) (bv_xor v_4507 (mi (bitwidthMInt v_4507) -1));
      pure ()
    pat_end;
    pattern fun (v_2861 : Mem) => do
      v_11138 <- evaluateAddress v_2861;
      v_11139 <- load v_11138 1;
      store v_11138 (bv_xor v_11139 (mi (bitwidthMInt v_11139) -1)) 1;
      pure ()
    pat_end
