def psignd1 : instruction :=
  definst "psignd" $ do
    pattern fun (v_2955 : reg (bv 128)) (v_2956 : reg (bv 128)) => do
      v_7412 <- getRegister v_2955;
      v_7413 <- eval (extract v_7412 0 32);
      v_7415 <- getRegister v_2956;
      v_7416 <- eval (extract v_7415 0 32);
      v_7422 <- eval (extract v_7412 32 64);
      v_7424 <- eval (extract v_7415 32 64);
      v_7430 <- eval (extract v_7412 64 96);
      v_7432 <- eval (extract v_7415 64 96);
      v_7438 <- eval (extract v_7412 96 128);
      v_7440 <- eval (extract v_7415 96 128);
      setRegister (lhs.of_reg v_2956) (concat (mux (sgt v_7413 (expression.bv_nat 32 0)) v_7416 (mux (eq v_7413 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7416 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7422 (expression.bv_nat 32 0)) v_7424 (mux (eq v_7422 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7424 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7430 (expression.bv_nat 32 0)) v_7432 (mux (eq v_7430 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7432 (expression.bv_nat 32 4294967295))))) (mux (sgt v_7438 (expression.bv_nat 32 0)) v_7440 (mux (eq v_7438 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7440 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end;
    pattern fun (v_2951 : Mem) (v_2952 : reg (bv 128)) => do
      v_14295 <- evaluateAddress v_2951;
      v_14296 <- load v_14295 16;
      v_14297 <- eval (extract v_14296 0 32);
      v_14299 <- getRegister v_2952;
      v_14300 <- eval (extract v_14299 0 32);
      v_14306 <- eval (extract v_14296 32 64);
      v_14308 <- eval (extract v_14299 32 64);
      v_14314 <- eval (extract v_14296 64 96);
      v_14316 <- eval (extract v_14299 64 96);
      v_14322 <- eval (extract v_14296 96 128);
      v_14324 <- eval (extract v_14299 96 128);
      setRegister (lhs.of_reg v_2952) (concat (mux (sgt v_14297 (expression.bv_nat 32 0)) v_14300 (mux (eq v_14297 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14300 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14306 (expression.bv_nat 32 0)) v_14308 (mux (eq v_14306 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14308 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_14314 (expression.bv_nat 32 0)) v_14316 (mux (eq v_14314 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14316 (expression.bv_nat 32 4294967295))))) (mux (sgt v_14322 (expression.bv_nat 32 0)) v_14324 (mux (eq v_14322 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14324 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end
