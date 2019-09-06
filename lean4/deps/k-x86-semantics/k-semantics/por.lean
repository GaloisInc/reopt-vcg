def por1 : instruction :=
  definst "por" $ do
    pattern fun (v_2963 : reg (bv 128)) (v_2964 : reg (bv 128)) => do
      v_6473 <- getRegister v_2964;
      v_6474 <- getRegister v_2963;
      setRegister (lhs.of_reg v_2964) (bv_or v_6473 v_6474);
      pure ()
    pat_end;
    pattern fun (v_2959 : Mem) (v_2960 : reg (bv 128)) => do
      v_13156 <- getRegister v_2960;
      v_13157 <- evaluateAddress v_2959;
      v_13158 <- load v_13157 16;
      setRegister (lhs.of_reg v_2960) (bv_or v_13156 v_13158);
      pure ()
    pat_end
