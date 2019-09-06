def cmovneq1 : instruction :=
  definst "cmovneq" $ do
    pattern fun (v_2950 : reg (bv 64)) (v_2951 : reg (bv 64)) => do
      v_4668 <- getRegister zf;
      v_4670 <- getRegister v_2950;
      v_4671 <- getRegister v_2951;
      setRegister (lhs.of_reg v_2951) (mux (notBool_ v_4668) v_4670 v_4671);
      pure ()
    pat_end;
    pattern fun (v_2946 : Mem) (v_2947 : reg (bv 64)) => do
      v_8016 <- getRegister zf;
      v_8018 <- evaluateAddress v_2946;
      v_8019 <- load v_8018 8;
      v_8020 <- getRegister v_2947;
      setRegister (lhs.of_reg v_2947) (mux (notBool_ v_8016) v_8019 v_8020);
      pure ()
    pat_end
