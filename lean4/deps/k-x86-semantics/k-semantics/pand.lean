def pand1 : instruction :=
  definst "pand" $ do
    pattern fun (v_3282 : reg (bv 128)) (v_3283 : reg (bv 128)) => do
      v_6308 <- getRegister v_3283;
      v_6309 <- getRegister v_3282;
      setRegister (lhs.of_reg v_3283) (bv_and v_6308 v_6309);
      pure ()
    pat_end;
    pattern fun (v_3278 : Mem) (v_3279 : reg (bv 128)) => do
      v_10215 <- getRegister v_3279;
      v_10216 <- evaluateAddress v_3278;
      v_10217 <- load v_10216 16;
      setRegister (lhs.of_reg v_3279) (bv_and v_10215 v_10217);
      pure ()
    pat_end
