def vpmuludq1 : instruction :=
  definst "vpmuludq" $ do
    pattern fun (v_3032 : reg (bv 128)) (v_3033 : reg (bv 128)) (v_3034 : reg (bv 128)) => do
      v_6936 <- getRegister v_3033;
      v_6939 <- getRegister v_3032;
      setRegister (lhs.of_reg v_3034) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6936 32 64)) (concat (expression.bv_nat 32 0) (extract v_6939 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_6936 96 128)) (concat (expression.bv_nat 32 0) (extract v_6939 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3043 : reg (bv 256)) (v_3044 : reg (bv 256)) (v_3045 : reg (bv 256)) => do
      v_6955 <- getRegister v_3044;
      v_6958 <- getRegister v_3043;
      setRegister (lhs.of_reg v_3045) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6955 32 64)) (concat (expression.bv_nat 32 0) (extract v_6958 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6955 96 128)) (concat (expression.bv_nat 32 0) (extract v_6958 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6955 160 192)) (concat (expression.bv_nat 32 0) (extract v_6958 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_6955 224 256)) (concat (expression.bv_nat 32 0) (extract v_6958 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_3026 : Mem) (v_3027 : reg (bv 128)) (v_3028 : reg (bv 128)) => do
      v_13246 <- getRegister v_3027;
      v_13249 <- evaluateAddress v_3026;
      v_13250 <- load v_13249 16;
      setRegister (lhs.of_reg v_3028) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13246 32 64)) (concat (expression.bv_nat 32 0) (extract v_13250 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_13246 96 128)) (concat (expression.bv_nat 32 0) (extract v_13250 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3037 : Mem) (v_3038 : reg (bv 256)) (v_3039 : reg (bv 256)) => do
      v_13261 <- getRegister v_3038;
      v_13264 <- evaluateAddress v_3037;
      v_13265 <- load v_13264 32;
      setRegister (lhs.of_reg v_3039) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13261 32 64)) (concat (expression.bv_nat 32 0) (extract v_13265 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13261 96 128)) (concat (expression.bv_nat 32 0) (extract v_13265 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13261 160 192)) (concat (expression.bv_nat 32 0) (extract v_13265 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_13261 224 256)) (concat (expression.bv_nat 32 0) (extract v_13265 224 256))))));
      pure ()
    pat_end
