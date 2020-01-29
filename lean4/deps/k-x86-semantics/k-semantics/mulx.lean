def mulx : instruction :=
  definst "mulx" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_0;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- load v_3 4;
      v_6 <- eval (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_6 0 32);
      setRegister (lhs.of_reg r32_2) v_8;
      setRegister (lhs.of_reg r32_1) v_7;
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (mul (concat (expression.bv_nat 64 0) v_3) (concat (expression.bv_nat 64 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 64)) <- eval (extract v_5 0 64);
      setRegister (lhs.of_reg r64_2) v_7;
      setRegister (lhs.of_reg r64_1) v_6;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister rdx;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- getRegister (lhs.of_reg r32_0);
      v_6 <- eval (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_6 32 64);
      setRegister (lhs.of_reg r32_1) v_8;
      setRegister (lhs.of_reg r32_2) v_7;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister rdx;
      v_4 <- getRegister (lhs.of_reg r64_0);
      v_5 <- eval (mul (concat (expression.bv_nat 64 0) v_3) (concat (expression.bv_nat 64 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 64)) <- eval (extract v_5 0 64);
      setRegister (lhs.of_reg r64_2) v_7;
      setRegister (lhs.of_reg r64_1) v_6;
      pure ()
    pat_end
