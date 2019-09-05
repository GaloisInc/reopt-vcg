def mulxl1 : instruction :=
  definst "mulxl" $ do
    pattern fun (v_2852 : reg (bv 32)) (v_2853 : reg (bv 32)) (v_2854 : reg (bv 32)) => do
      v_4361 <- getRegister rdx;
      v_4364 <- getRegister v_2852;
      v_4366 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_4361 32 64)) (concat (expression.bv_nat 32 0) v_4364));
      setRegister (lhs.of_reg v_2853) (extract v_4366 32 64);
      setRegister (lhs.of_reg v_2854) (extract v_4366 0 32);
      pure ()
    pat_end;
    pattern fun (v_2841 : Mem) (v_2842 : reg (bv 32)) (v_2843 : reg (bv 32)) => do
      v_8909 <- evaluateAddress v_2841;
      v_8912 <- load v_8909 4;
      v_8914 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_8909 32 64)) (concat (expression.bv_nat 32 0) v_8912));
      setRegister (lhs.of_reg v_2843) (extract v_8914 0 32);
      setRegister (lhs.of_reg v_2842) (extract v_8914 32 64);
      pure ()
    pat_end
