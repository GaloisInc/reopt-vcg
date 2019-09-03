def shrxl1 : instruction :=
  definst "shrxl" $ do
    pattern fun (v_3017 : reg (bv 32)) (v_3018 : reg (bv 32)) (v_3019 : reg (bv 32)) => do
      v_6626 <- getRegister v_3018;
      v_6627 <- getRegister v_3017;
      setRegister (lhs.of_reg v_3019) (lshr v_6626 (uvalueMInt (bv_and v_6627 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3007 : reg (bv 32)) (v_3006 : Mem) (v_3008 : reg (bv 32)) => do
      v_10192 <- evaluateAddress v_3006;
      v_10193 <- load v_10192 4;
      v_10194 <- getRegister v_3007;
      setRegister (lhs.of_reg v_3008) (lshr v_10193 (uvalueMInt (bv_and v_10194 (expression.bv_nat 32 31))));
      pure ()
    pat_end
