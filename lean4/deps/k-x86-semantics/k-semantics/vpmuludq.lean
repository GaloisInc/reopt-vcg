def vpmuludq1 : instruction :=
  definst "vpmuludq" $ do
    pattern fun (v_2940 : reg (bv 128)) (v_2941 : reg (bv 128)) (v_2942 : reg (bv 128)) => do
      v_7091 <- getRegister v_2941;
      v_7094 <- getRegister v_2940;
      setRegister (lhs.of_reg v_2942) (concat (mul (concat (expression.bv_nat 32 0) (extract v_7091 32 64)) (concat (expression.bv_nat 32 0) (extract v_7094 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_7091 96 128)) (concat (expression.bv_nat 32 0) (extract v_7094 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2951 : reg (bv 256)) (v_2952 : reg (bv 256)) (v_2953 : reg (bv 256)) => do
      v_7110 <- getRegister v_2952;
      v_7113 <- getRegister v_2951;
      setRegister (lhs.of_reg v_2953) (concat (mul (concat (expression.bv_nat 32 0) (extract v_7110 32 64)) (concat (expression.bv_nat 32 0) (extract v_7113 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_7110 96 128)) (concat (expression.bv_nat 32 0) (extract v_7113 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_7110 160 192)) (concat (expression.bv_nat 32 0) (extract v_7113 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_7110 224 256)) (concat (expression.bv_nat 32 0) (extract v_7113 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) => do
      v_14148 <- getRegister v_2935;
      v_14151 <- evaluateAddress v_2937;
      v_14152 <- load v_14151 16;
      setRegister (lhs.of_reg v_2936) (concat (mul (concat (expression.bv_nat 32 0) (extract v_14148 32 64)) (concat (expression.bv_nat 32 0) (extract v_14152 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_14148 96 128)) (concat (expression.bv_nat 32 0) (extract v_14152 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2946 : Mem) (v_2947 : reg (bv 256)) (v_2948 : reg (bv 256)) => do
      v_14163 <- getRegister v_2947;
      v_14166 <- evaluateAddress v_2946;
      v_14167 <- load v_14166 32;
      setRegister (lhs.of_reg v_2948) (concat (mul (concat (expression.bv_nat 32 0) (extract v_14163 32 64)) (concat (expression.bv_nat 32 0) (extract v_14167 32 64))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_14163 96 128)) (concat (expression.bv_nat 32 0) (extract v_14167 96 128))) (concat (mul (concat (expression.bv_nat 32 0) (extract v_14163 160 192)) (concat (expression.bv_nat 32 0) (extract v_14167 160 192))) (mul (concat (expression.bv_nat 32 0) (extract v_14163 224 256)) (concat (expression.bv_nat 32 0) (extract v_14167 224 256))))));
      pure ()
    pat_end
