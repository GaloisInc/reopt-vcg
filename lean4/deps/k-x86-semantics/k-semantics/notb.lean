def notb1 : instruction :=
  definst "notb" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      store v_1 (bv_xor v_2 (expression.bv_nat 8 255)) 1;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister rh_0;
      setRegister (lhs.of_reg rh_0) (bv_xor v_1 (expression.bv_nat 8 255));
      pure ()
    pat_end
