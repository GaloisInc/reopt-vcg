def pand1 : instruction :=
  definst "pand" $ do
    pattern fun (v_3194 : reg (bv 128)) (v_3195 : reg (bv 128)) => do
      v_6411 <- getRegister v_3195;
      v_6412 <- getRegister v_3194;
      setRegister (lhs.of_reg v_3195) (bv_and v_6411 v_6412);
      pure ()
    pat_end;
    pattern fun (v_3189 : Mem) (v_3190 : reg (bv 128)) => do
      v_10479 <- getRegister v_3190;
      v_10480 <- evaluateAddress v_3189;
      v_10481 <- load v_10480 16;
      setRegister (lhs.of_reg v_3190) (bv_and v_10479 v_10481);
      pure ()
    pat_end
