def shlxq : instruction :=
  definst "shlxq" $ do
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 8;
      v_5 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg r64_2) (extract (shl v_4 (bv_and v_5 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg r64_2) (extract (shl v_3 (bv_and v_4 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end
