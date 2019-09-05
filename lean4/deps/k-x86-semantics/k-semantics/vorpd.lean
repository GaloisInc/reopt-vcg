def vorpd1 : instruction :=
  definst "vorpd" $ do
    pattern fun (v_3194 : Mem) (v_3195 : reg (bv 128)) (v_3196 : reg (bv 128)) => do
      v_10446 <- getRegister v_3195;
      v_10447 <- evaluateAddress v_3194;
      v_10448 <- load v_10447 16;
      setRegister (lhs.of_reg v_3196) (bv_or v_10446 v_10448);
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 256)) (v_3207 : reg (bv 256)) => do
      v_10451 <- getRegister v_3206;
      v_10452 <- evaluateAddress v_3205;
      v_10453 <- load v_10452 32;
      setRegister (lhs.of_reg v_3207) (bv_or v_10451 v_10453);
      pure ()
    pat_end
