def vorpd1 : instruction :=
  definst "vorpd" $ do
    pattern fun (v_3130 : Mem) (v_3131 : reg (bv 128)) (v_3132 : reg (bv 128)) => do
      v_10580 <- getRegister v_3131;
      v_10581 <- evaluateAddress v_3130;
      v_10582 <- load v_10581 16;
      setRegister (lhs.of_reg v_3132) (bv_or v_10580 v_10582);
      pure ()
    pat_end;
    pattern fun (v_3141 : Mem) (v_3142 : reg (bv 256)) (v_3143 : reg (bv 256)) => do
      v_10585 <- getRegister v_3142;
      v_10586 <- evaluateAddress v_3141;
      v_10587 <- load v_10586 32;
      setRegister (lhs.of_reg v_3143) (bv_or v_10585 v_10587);
      pure ()
    pat_end
