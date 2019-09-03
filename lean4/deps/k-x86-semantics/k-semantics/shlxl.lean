def shlxl1 : instruction :=
  definst "shlxl" $ do
    pattern fun (v_2830 : reg (bv 32)) (v_2831 : reg (bv 32)) (v_2832 : reg (bv 32)) => do
      v_5452 <- getRegister v_2831;
      v_5453 <- getRegister v_2830;
      setRegister (lhs.of_reg v_2832) (extract (shl v_5452 (uvalueMInt (bv_and v_5453 (expression.bv_nat 32 31)))) 0 (bitwidthMInt v_5452));
      pure ()
    pat_end;
    pattern fun (v_2820 : reg (bv 32)) (v_2819 : Mem) (v_2821 : reg (bv 32)) => do
      v_10078 <- evaluateAddress v_2819;
      v_10079 <- load v_10078 4;
      v_10080 <- getRegister v_2820;
      setRegister (lhs.of_reg v_2821) (extract (shl v_10079 (uvalueMInt (bv_and v_10080 (expression.bv_nat 32 31)))) 0 (bitwidthMInt v_10079));
      pure ()
    pat_end
