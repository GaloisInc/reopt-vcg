def vpsignd1 : instruction :=
  definst "vpsignd" $ do
    pattern fun (v_3029 : reg (bv 128)) (v_3030 : reg (bv 128)) (v_3031 : reg (bv 128)) => do
      v_7481 <- getRegister v_3029;
      v_7482 <- eval (extract v_7481 0 32);
      v_7484 <- getRegister v_3030;
      v_7485 <- eval (extract v_7484 0 32);
      v_7491 <- eval (extract v_7481 32 64);
      v_7493 <- eval (extract v_7484 32 64);
      v_7499 <- eval (extract v_7481 64 96);
      v_7501 <- eval (extract v_7484 64 96);
      v_7507 <- eval (extract v_7481 96 128);
      v_7509 <- eval (extract v_7484 96 128);
      setRegister (lhs.of_reg v_3031) (concat (mux (sgt v_7482 (expression.bv_nat 32 0)) v_7485 (mux (eq v_7482 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7485 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7491 (expression.bv_nat 32 0)) v_7493 (mux (eq v_7491 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7493 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7499 (expression.bv_nat 32 0)) v_7501 (mux (eq v_7499 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7501 (expression.bv_nat 32 4294967295))))) (mux (sgt v_7507 (expression.bv_nat 32 0)) v_7509 (mux (eq v_7507 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7509 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end;
    pattern fun (v_3023 : Mem) (v_3024 : reg (bv 128)) (v_3025 : reg (bv 128)) => do
      v_14019 <- evaluateAddress v_3023;
      v_14020 <- load v_14019 16;
      v_14021 <- eval (extract v_14020 0 32);
      v_14023 <- getRegister v_3024;
      v_14024 <- eval (extract v_14023 0 32);
      v_14030 <- eval (extract v_14020 32 64);
      v_14032 <- eval (extract v_14023 32 64);
      v_14038 <- eval (extract v_14020 64 96);
      v_14040 <- eval (extract v_14023 64 96);
      v_14046 <- eval (extract v_14020 96 128);
      v_14048 <- eval (extract v_14023 96 128);
      setRegister (lhs.of_reg v_3025) (concat (mux (sgt v_14021 (expression.bv_nat 32 0)) v_14024 (mux (eq v_14021 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14024 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14030 (expression.bv_nat 32 0)) v_14032 (mux (eq v_14030 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14032 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14038 (expression.bv_nat 32 0)) v_14040 (mux (eq v_14038 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14040 (expression.bv_nat 32 4294967295))))) (mux (sgt v_14046 (expression.bv_nat 32 0)) v_14048 (mux (eq v_14046 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14048 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end
