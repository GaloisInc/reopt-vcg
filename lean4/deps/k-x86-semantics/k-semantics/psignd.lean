def psignd1 : instruction :=
  definst "psignd" $ do
    pattern fun (v_3032 : reg (bv 128)) (v_3033 : reg (bv 128)) => do
      v_7442 <- getRegister v_3032;
      v_7443 <- eval (extract v_7442 0 32);
      v_7445 <- getRegister v_3033;
      v_7446 <- eval (extract v_7445 0 32);
      v_7452 <- eval (extract v_7442 32 64);
      v_7454 <- eval (extract v_7445 32 64);
      v_7460 <- eval (extract v_7442 64 96);
      v_7462 <- eval (extract v_7445 64 96);
      v_7468 <- eval (extract v_7442 96 128);
      v_7470 <- eval (extract v_7445 96 128);
      setRegister (lhs.of_reg v_3033) (concat (mux (sgt v_7443 (expression.bv_nat 32 0)) v_7446 (mux (eq v_7443 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7446 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7452 (expression.bv_nat 32 0)) v_7454 (mux (eq v_7452 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7454 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7460 (expression.bv_nat 32 0)) v_7462 (mux (eq v_7460 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7462 (expression.bv_nat 32 4294967295))))) (mux (sgt v_7468 (expression.bv_nat 32 0)) v_7470 (mux (eq v_7468 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7470 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end;
    pattern fun (v_3028 : Mem) (v_3029 : reg (bv 128)) => do
      v_14101 <- evaluateAddress v_3028;
      v_14102 <- load v_14101 16;
      v_14103 <- eval (extract v_14102 0 32);
      v_14105 <- getRegister v_3029;
      v_14106 <- eval (extract v_14105 0 32);
      v_14112 <- eval (extract v_14102 32 64);
      v_14114 <- eval (extract v_14105 32 64);
      v_14120 <- eval (extract v_14102 64 96);
      v_14122 <- eval (extract v_14105 64 96);
      v_14128 <- eval (extract v_14102 96 128);
      v_14130 <- eval (extract v_14105 96 128);
      setRegister (lhs.of_reg v_3029) (concat (mux (sgt v_14103 (expression.bv_nat 32 0)) v_14106 (mux (eq v_14103 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14106 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14112 (expression.bv_nat 32 0)) v_14114 (mux (eq v_14112 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14114 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14120 (expression.bv_nat 32 0)) v_14122 (mux (eq v_14120 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14122 (expression.bv_nat 32 4294967295))))) (mux (sgt v_14128 (expression.bv_nat 32 0)) v_14130 (mux (eq v_14128 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14130 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end
