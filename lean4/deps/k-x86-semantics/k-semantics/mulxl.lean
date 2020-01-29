def mulxl : instruction :=
  definst "mulxl" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_0;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- load v_3 4;
      v_6 <- eval (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_6 32 64);
      setRegister (lhs.of_reg r32_1) v_8;
      setRegister (lhs.of_reg r32_2) v_7;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister rdx;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- getRegister (lhs.of_reg r32_0);
      v_6 <- eval (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_6 0 32);
      setRegister (lhs.of_reg r32_2) v_8;
      setRegister (lhs.of_reg r32_1) v_7;
      pure ()
    pat_end
