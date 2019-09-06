def cmovnbq1 : instruction :=
  definst "cmovnbq" $ do
    pattern fun (v_2896 : reg (bv 64)) (v_2897 : reg (bv 64)) => do
      v_4608 <- getRegister cf;
      v_4610 <- getRegister v_2896;
      v_4611 <- getRegister v_2897;
      setRegister (lhs.of_reg v_2897) (mux (notBool_ v_4608) v_4610 v_4611);
      pure ()
    pat_end;
    pattern fun (v_2892 : Mem) (v_2893 : reg (bv 64)) => do
      v_7974 <- getRegister cf;
      v_7976 <- evaluateAddress v_2892;
      v_7977 <- load v_7976 8;
      v_7978 <- getRegister v_2893;
      setRegister (lhs.of_reg v_2893) (mux (notBool_ v_7974) v_7977 v_7978);
      pure ()
    pat_end
