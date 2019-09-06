def mulxl1 : instruction :=
  definst "mulxl" $ do
    pattern fun (v_2877 : reg (bv 32)) (v_2878 : reg (bv 32)) (v_2879 : reg (bv 32)) => do
      v_4388 <- getRegister rdx;
      v_4391 <- getRegister v_2877;
      v_4393 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_4388 32 64)) (concat (expression.bv_nat 32 0) v_4391));
      setRegister (lhs.of_reg v_2879) (extract v_4393 0 32);
      setRegister (lhs.of_reg v_2878) (extract v_4393 32 64);
      pure ()
    pat_end;
    pattern fun (v_2867 : Mem) (v_2868 : reg (bv 32)) (v_2869 : reg (bv 32)) => do
      v_8936 <- evaluateAddress v_2867;
      v_8939 <- load v_8936 4;
      v_8941 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_8936 32 64)) (concat (expression.bv_nat 32 0) v_8939));
      setRegister (lhs.of_reg v_2869) (extract v_8941 0 32);
      setRegister (lhs.of_reg v_2868) (extract v_8941 32 64);
      pure ()
    pat_end
