def notq : instruction :=
  definst "notq" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 8;
      store v_1 (bv_xor v_2 (expression.bv_nat 64 18446744073709551615)) 8;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg r64_0) (bv_xor v_1 (expression.bv_nat 64 18446744073709551615));
      pure ()
    pat_end
