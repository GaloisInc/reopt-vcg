def vxorpd1 : instruction :=
  definst "vxorpd" $ do
    pattern fun (v_3309 : Mem) (v_3310 : reg (bv 128)) (v_3311 : reg (bv 128)) => do
      v_13519 <- getRegister v_3310;
      v_13520 <- evaluateAddress v_3309;
      v_13521 <- load v_13520 16;
      setRegister (lhs.of_reg v_3311) (bv_xor v_13519 v_13521);
      pure ()
    pat_end;
    pattern fun (v_3320 : Mem) (v_3321 : reg (bv 256)) (v_3322 : reg (bv 256)) => do
      v_13524 <- getRegister v_3321;
      v_13525 <- evaluateAddress v_3320;
      v_13526 <- load v_13525 32;
      setRegister (lhs.of_reg v_3322) (bv_xor v_13524 v_13526);
      pure ()
    pat_end
