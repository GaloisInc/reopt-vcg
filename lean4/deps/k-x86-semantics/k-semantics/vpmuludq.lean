def vpmuludq1 : instruction :=
  definst "vpmuludq" $ do
    pattern fun (v_2952 : reg (bv 128)) (v_2953 : reg (bv 128)) (v_2954 : reg (bv 128)) => do
      v_6858 <- getRegister v_2953;
      v_6861 <- getRegister v_2952;
      setRegister (lhs.of_reg v_2954) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6858 32 64)) (concat (expression.bv_nat 32 0) (extract v_6861 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_6858 96 128)) (concat (expression.bv_nat 32 0) (extract v_6861 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2964 : reg (bv 256)) (v_2965 : reg (bv 256)) (v_2966 : reg (bv 256)) => do
      v_6877 <- getRegister v_2965;
      v_6880 <- getRegister v_2964;
      setRegister (lhs.of_reg v_2966) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6877 32 64)) (concat (expression.bv_nat 32 0) (extract v_6880 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6877 96 128)) (concat (expression.bv_nat 32 0) (extract v_6880 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6877 160 192)) (concat (expression.bv_nat 32 0) (extract v_6880 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_6877 224 256)) (concat (expression.bv_nat 32 0) (extract v_6880 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_2946 : Mem) (v_2947 : reg (bv 128)) (v_2948 : reg (bv 128)) => do
      v_13424 <- getRegister v_2947;
      v_13427 <- evaluateAddress v_2946;
      v_13428 <- load v_13427 16;
      setRegister (lhs.of_reg v_2948) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13424 32 64)) (concat (expression.bv_nat 32 0) (extract v_13428 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_13424 96 128)) (concat (expression.bv_nat 32 0) (extract v_13428 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2957 : Mem) (v_2959 : reg (bv 256)) (v_2960 : reg (bv 256)) => do
      v_13439 <- getRegister v_2959;
      v_13442 <- evaluateAddress v_2957;
      v_13443 <- load v_13442 32;
      setRegister (lhs.of_reg v_2960) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13439 32 64)) (concat (expression.bv_nat 32 0) (extract v_13443 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13439 96 128)) (concat (expression.bv_nat 32 0) (extract v_13443 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13439 160 192)) (concat (expression.bv_nat 32 0) (extract v_13443 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_13439 224 256)) (concat (expression.bv_nat 32 0) (extract v_13443 224 256))))));
      pure ()
    pat_end
