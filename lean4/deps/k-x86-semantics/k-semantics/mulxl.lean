def mulxl : instruction :=
  definst "mulxl" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      v_5 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_3 32 64)) (concat (expression.bv_nat 32 0) v_4));
      setRegister (lhs.of_reg r32_1) (extract v_5 32 64);
      setRegister (lhs.of_reg r32_2) (extract v_5 0 32);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister rdx;
      v_4 <- getRegister (lhs.of_reg r32_0);
      v_5 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_3 32 64)) (concat (expression.bv_nat 32 0) v_4));
      setRegister (lhs.of_reg r32_1) (extract v_5 32 64);
      setRegister (lhs.of_reg r32_2) (extract v_5 0 32);
      pure ()
    pat_end
