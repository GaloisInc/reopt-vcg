def cmovncl1 : instruction :=
  definst "cmovncl" $ do
    pattern fun (v_2917 : reg (bv 32)) (v_2918 : reg (bv 32)) => do
      v_4628 <- getRegister cf;
      v_4630 <- getRegister v_2917;
      v_4631 <- getRegister v_2918;
      setRegister (lhs.of_reg v_2918) (mux (notBool_ v_4628) v_4630 v_4631);
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) (v_2913 : reg (bv 32)) => do
      v_7988 <- getRegister cf;
      v_7990 <- evaluateAddress v_2910;
      v_7991 <- load v_7990 4;
      v_7992 <- getRegister v_2913;
      setRegister (lhs.of_reg v_2913) (mux (notBool_ v_7988) v_7991 v_7992);
      pure ()
    pat_end
