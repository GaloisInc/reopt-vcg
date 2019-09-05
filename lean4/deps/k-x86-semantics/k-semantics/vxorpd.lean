def vxorpd1 : instruction :=
  definst "vxorpd" $ do
    pattern fun (v_3282 : Mem) (v_3283 : reg (bv 128)) (v_3284 : reg (bv 128)) => do
      v_13492 <- getRegister v_3283;
      v_13493 <- evaluateAddress v_3282;
      v_13494 <- load v_13493 16;
      setRegister (lhs.of_reg v_3284) (bv_xor v_13492 v_13494);
      pure ()
    pat_end;
    pattern fun (v_3293 : Mem) (v_3294 : reg (bv 256)) (v_3295 : reg (bv 256)) => do
      v_13497 <- getRegister v_3294;
      v_13498 <- evaluateAddress v_3293;
      v_13499 <- load v_13498 32;
      setRegister (lhs.of_reg v_3295) (bv_xor v_13497 v_13499);
      pure ()
    pat_end
