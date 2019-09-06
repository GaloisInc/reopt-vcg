def xorpd1 : instruction :=
  definst "xorpd" $ do
    pattern fun (v_3444 : reg (bv 128)) (v_3445 : reg (bv 128)) => do
      v_8054 <- getRegister v_3445;
      v_8055 <- getRegister v_3444;
      setRegister (lhs.of_reg v_3445) (bv_xor v_8054 v_8055);
      pure ()
    pat_end;
    pattern fun (v_3439 : Mem) (v_3440 : reg (bv 128)) => do
      v_13589 <- getRegister v_3440;
      v_13590 <- evaluateAddress v_3439;
      v_13591 <- load v_13590 16;
      setRegister (lhs.of_reg v_3440) (bv_xor v_13589 v_13591);
      pure ()
    pat_end
