def vorpd1 : instruction :=
  definst "vorpd" $ do
    pattern fun (v_3143 : Mem) (v_3144 : reg (bv 128)) (v_3145 : reg (bv 128)) => do
      v_11625 <- getRegister v_3144;
      v_11626 <- evaluateAddress v_3143;
      v_11627 <- load v_11626 16;
      setRegister (lhs.of_reg v_3145) (bv_or v_11625 v_11627);
      pure ()
    pat_end;
    pattern fun (v_3154 : Mem) (v_3155 : reg (bv 256)) (v_3156 : reg (bv 256)) => do
      v_11630 <- getRegister v_3155;
      v_11631 <- evaluateAddress v_3154;
      v_11632 <- load v_11631 32;
      setRegister (lhs.of_reg v_3156) (bv_or v_11630 v_11632);
      pure ()
    pat_end
