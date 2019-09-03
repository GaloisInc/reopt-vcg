def shrxl1 : instruction :=
  definst "shrxl" $ do
    pattern fun (v_3004 : reg (bv 32)) (v_3005 : reg (bv 32)) (v_3006 : reg (bv 32)) => do
      v_6630 <- getRegister v_3005;
      v_6631 <- getRegister v_3004;
      setRegister (lhs.of_reg v_3006) (lshr v_6630 (uvalueMInt (bv_and v_6631 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_2994 : reg (bv 32)) (v_2993 : Mem) (v_2995 : reg (bv 32)) => do
      v_10170 <- evaluateAddress v_2993;
      v_10171 <- load v_10170 4;
      v_10172 <- getRegister v_2994;
      setRegister (lhs.of_reg v_2995) (lshr v_10171 (uvalueMInt (bv_and v_10172 (expression.bv_nat 32 31))));
      pure ()
    pat_end
