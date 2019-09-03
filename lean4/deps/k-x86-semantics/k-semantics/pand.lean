def pand1 : instruction :=
  definst "pand" $ do
    pattern fun (v_3206 : reg (bv 128)) (v_3207 : reg (bv 128)) => do
      v_6393 <- getRegister v_3207;
      v_6394 <- getRegister v_3206;
      setRegister (lhs.of_reg v_3207) (bv_and v_6393 v_6394);
      pure ()
    pat_end;
    pattern fun (v_3202 : Mem) (v_3203 : reg (bv 128)) => do
      v_10449 <- getRegister v_3203;
      v_10450 <- evaluateAddress v_3202;
      v_10451 <- load v_10450 16;
      setRegister (lhs.of_reg v_3203) (bv_and v_10449 v_10451);
      pure ()
    pat_end
