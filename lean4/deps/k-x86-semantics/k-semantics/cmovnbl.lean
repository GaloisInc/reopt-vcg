def cmovnbl1 : instruction :=
  definst "cmovnbl" $ do
    pattern fun (v_2890 : reg (bv 32)) (v_2891 : reg (bv 32)) => do
      v_4598 <- getRegister cf;
      v_4600 <- getRegister v_2890;
      v_4601 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2891) (mux (notBool_ v_4598) v_4600 v_4601);
      pure ()
    pat_end;
    pattern fun (v_2883 : Mem) (v_2886 : reg (bv 32)) => do
      v_7967 <- getRegister cf;
      v_7969 <- evaluateAddress v_2883;
      v_7970 <- load v_7969 4;
      v_7971 <- getRegister v_2886;
      setRegister (lhs.of_reg v_2886) (mux (notBool_ v_7967) v_7970 v_7971);
      pure ()
    pat_end
