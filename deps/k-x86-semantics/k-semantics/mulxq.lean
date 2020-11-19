def mulxq : instruction :=
  definst "mulxq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (mul (concat (expression.bv_nat 64 0) v_3) (concat (expression.bv_nat 64 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      setRegister (lhs.of_reg r64_1) v_7;
      setRegister (lhs.of_reg r64_2) v_6;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister rdx;
      v_4 <- getRegister (lhs.of_reg r64_0);
      v_5 <- eval (mul (concat (expression.bv_nat 64 0) v_3) (concat (expression.bv_nat 64 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      setRegister (lhs.of_reg r64_1) v_7;
      setRegister (lhs.of_reg r64_2) v_6;
      pure ()
    pat_end
