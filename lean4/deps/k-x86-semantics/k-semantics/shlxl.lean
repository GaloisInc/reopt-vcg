def shlxl1 : instruction :=
  definst "shlxl" $ do
    pattern fun (v_2843 : reg (bv 32)) (v_2844 : reg (bv 32)) (v_2845 : reg (bv 32)) => do
      v_5450 <- getRegister v_2844;
      v_5451 <- getRegister v_2843;
      setRegister (lhs.of_reg v_2845) (extract (shl v_5450 (uvalueMInt (bv_and v_5451 (expression.bv_nat 32 31)))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2833 : reg (bv 32)) (v_2832 : Mem) (v_2834 : reg (bv 32)) => do
      v_10102 <- evaluateAddress v_2832;
      v_10103 <- load v_10102 4;
      v_10104 <- getRegister v_2833;
      setRegister (lhs.of_reg v_2834) (extract (shl v_10103 (uvalueMInt (bv_and v_10104 (expression.bv_nat 32 31)))) 0 32);
      pure ()
    pat_end
