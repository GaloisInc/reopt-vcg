def cmovnbw1 : instruction :=
  definst "cmovnbw" $ do
    pattern fun (v_2905 : reg (bv 16)) (v_2906 : reg (bv 16)) => do
      v_4618 <- getRegister cf;
      v_4620 <- getRegister v_2905;
      v_4621 <- getRegister v_2906;
      setRegister (lhs.of_reg v_2906) (mux (notBool_ v_4618) v_4620 v_4621);
      pure ()
    pat_end;
    pattern fun (v_2901 : Mem) (v_2902 : reg (bv 16)) => do
      v_7981 <- getRegister cf;
      v_7983 <- evaluateAddress v_2901;
      v_7984 <- load v_7983 2;
      v_7985 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2902) (mux (notBool_ v_7981) v_7984 v_7985);
      pure ()
    pat_end
