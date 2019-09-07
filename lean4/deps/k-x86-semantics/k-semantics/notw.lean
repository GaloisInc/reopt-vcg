def notw1 : instruction :=
  definst "notw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      store v_1 (bv_xor v_2 (expression.bv_nat 16 65535)) 2;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister r16_0;
      setRegister (lhs.of_reg r16_0) (bv_xor v_1 (expression.bv_nat 16 65535));
      pure ()
    pat_end
