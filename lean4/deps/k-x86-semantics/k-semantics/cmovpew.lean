def cmovpew1 : instruction :=
  definst "cmovpew" $ do
    pattern fun (v_3253 : reg (bv 16)) (v_3254 : reg (bv 16)) => do
      v_5021 <- getRegister pf;
      v_5022 <- getRegister v_3253;
      v_5023 <- getRegister v_3254;
      setRegister (lhs.of_reg v_3254) (mux v_5021 v_5022 v_5023);
      pure ()
    pat_end;
    pattern fun (v_3249 : Mem) (v_3250 : reg (bv 16)) => do
      v_8264 <- getRegister pf;
      v_8265 <- evaluateAddress v_3249;
      v_8266 <- load v_8265 2;
      v_8267 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3250) (mux v_8264 v_8266 v_8267);
      pure ()
    pat_end
