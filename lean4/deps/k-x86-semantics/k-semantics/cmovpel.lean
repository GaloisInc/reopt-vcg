def cmovpel1 : instruction :=
  definst "cmovpel" $ do
    pattern fun (v_3238 : reg (bv 32)) (v_3239 : reg (bv 32)) => do
      v_5003 <- getRegister pf;
      v_5004 <- getRegister v_3238;
      v_5005 <- getRegister v_3239;
      setRegister (lhs.of_reg v_3239) (mux v_5003 v_5004 v_5005);
      pure ()
    pat_end;
    pattern fun (v_3231 : Mem) (v_3234 : reg (bv 32)) => do
      v_8252 <- getRegister pf;
      v_8253 <- evaluateAddress v_3231;
      v_8254 <- load v_8253 4;
      v_8255 <- getRegister v_3234;
      setRegister (lhs.of_reg v_3234) (mux v_8252 v_8254 v_8255);
      pure ()
    pat_end
