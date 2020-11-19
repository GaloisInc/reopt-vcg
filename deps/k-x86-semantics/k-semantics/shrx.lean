def shrx : instruction :=
  definst "shrx" $ do
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 4;
      v_5 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_2) (lshr v_4 (bv_and v_5 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg r32_1);
      v_4 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_2) (lshr v_3 (bv_and v_4 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 8;
      v_5 <- getRegister (lhs.of_reg r64_0);
      (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_7 : expression (bv 64)) <- eval (extract (lshr (concat v_4 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and v_6 (expression.bv_nat 8 63)))) 0 64);
      setRegister (lhs.of_reg r64_2) v_7;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- getRegister (lhs.of_reg r64_0);
      (v_5 : expression (bv 8)) <- eval (extract v_4 56 64);
      (v_6 : expression (bv 64)) <- eval (extract (lshr (concat v_3 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and v_5 (expression.bv_nat 8 63)))) 0 64);
      setRegister (lhs.of_reg r64_2) v_6;
      pure ()
    pat_end
