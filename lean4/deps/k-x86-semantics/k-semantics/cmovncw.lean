def cmovncw1 : instruction :=
  definst "cmovncw" $ do
    pattern fun (v_2932 : reg (bv 16)) (v_2933 : reg (bv 16)) => do
      v_4648 <- getRegister cf;
      v_4650 <- getRegister v_2932;
      v_4651 <- getRegister v_2933;
      setRegister (lhs.of_reg v_2933) (mux (notBool_ v_4648) v_4650 v_4651);
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 16)) => do
      v_8002 <- getRegister cf;
      v_8004 <- evaluateAddress v_2928;
      v_8005 <- load v_8004 2;
      v_8006 <- getRegister v_2929;
      setRegister (lhs.of_reg v_2929) (mux (notBool_ v_8002) v_8005 v_8006);
      pure ()
    pat_end
