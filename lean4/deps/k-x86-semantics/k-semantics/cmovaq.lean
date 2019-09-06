def cmovaq1 : instruction :=
  definst "cmovaq" $ do
    pattern fun (v_2500 : reg (bv 64)) (v_2501 : reg (bv 64)) => do
      v_4161 <- getRegister cf;
      v_4163 <- getRegister zf;
      v_4166 <- getRegister v_2500;
      v_4167 <- getRegister v_2501;
      setRegister (lhs.of_reg v_2501) (mux (bit_and (notBool_ v_4161) (notBool_ v_4163)) v_4166 v_4167);
      pure ()
    pat_end;
    pattern fun (v_2496 : Mem) (v_2497 : reg (bv 64)) => do
      v_7671 <- getRegister cf;
      v_7673 <- getRegister zf;
      v_7676 <- evaluateAddress v_2496;
      v_7677 <- load v_7676 8;
      v_7678 <- getRegister v_2497;
      setRegister (lhs.of_reg v_2497) (mux (bit_and (notBool_ v_7671) (notBool_ v_7673)) v_7677 v_7678);
      pure ()
    pat_end
