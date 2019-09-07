def shrxq1 : instruction :=
  definst "shrxq" $ do
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 8;
      v_5 <- getRegister r64_0;
      setRegister (lhs.of_reg r64_2) (extract (lshr (concat v_4 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_5 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister r64_1;
      v_4 <- getRegister r64_0;
      setRegister (lhs.of_reg r64_2) (extract (lshr (concat v_3 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_4 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end
