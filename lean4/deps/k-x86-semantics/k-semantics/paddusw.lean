def paddusw1 : instruction :=
  definst "paddusw" $ do
    pattern fun (v_3165 : reg (bv 128)) (v_3166 : reg (bv 128)) => do
      v_6270 <- getRegister v_3166;
      v_6273 <- getRegister v_3165;
      v_6276 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 0 16)) (concat (expression.bv_nat 1 0) (extract v_6273 0 16)));
      v_6285 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 16 32)) (concat (expression.bv_nat 1 0) (extract v_6273 16 32)));
      v_6294 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 32 48)) (concat (expression.bv_nat 1 0) (extract v_6273 32 48)));
      v_6303 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 48 64)) (concat (expression.bv_nat 1 0) (extract v_6273 48 64)));
      v_6312 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 64 80)) (concat (expression.bv_nat 1 0) (extract v_6273 64 80)));
      v_6321 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 80 96)) (concat (expression.bv_nat 1 0) (extract v_6273 80 96)));
      v_6330 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 96 112)) (concat (expression.bv_nat 1 0) (extract v_6273 96 112)));
      v_6339 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6270 112 128)) (concat (expression.bv_nat 1 0) (extract v_6273 112 128)));
      setRegister (lhs.of_reg v_3166) (concat (mux (eq (extract v_6276 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6276 1 17)) (concat (mux (eq (extract v_6285 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6285 1 17)) (concat (mux (eq (extract v_6294 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6294 1 17)) (concat (mux (eq (extract v_6303 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6303 1 17)) (concat (mux (eq (extract v_6312 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6312 1 17)) (concat (mux (eq (extract v_6321 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6321 1 17)) (concat (mux (eq (extract v_6330 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6330 1 17)) (mux (eq (extract v_6339 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6339 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_3160 : Mem) (v_3161 : reg (bv 128)) => do
      v_10348 <- getRegister v_3161;
      v_10351 <- evaluateAddress v_3160;
      v_10352 <- load v_10351 16;
      v_10355 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 0 16)) (concat (expression.bv_nat 1 0) (extract v_10352 0 16)));
      v_10364 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 16 32)) (concat (expression.bv_nat 1 0) (extract v_10352 16 32)));
      v_10373 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 32 48)) (concat (expression.bv_nat 1 0) (extract v_10352 32 48)));
      v_10382 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 48 64)) (concat (expression.bv_nat 1 0) (extract v_10352 48 64)));
      v_10391 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 64 80)) (concat (expression.bv_nat 1 0) (extract v_10352 64 80)));
      v_10400 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 80 96)) (concat (expression.bv_nat 1 0) (extract v_10352 80 96)));
      v_10409 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 96 112)) (concat (expression.bv_nat 1 0) (extract v_10352 96 112)));
      v_10418 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10348 112 128)) (concat (expression.bv_nat 1 0) (extract v_10352 112 128)));
      setRegister (lhs.of_reg v_3161) (concat (mux (eq (extract v_10355 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10355 1 17)) (concat (mux (eq (extract v_10364 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10364 1 17)) (concat (mux (eq (extract v_10373 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10373 1 17)) (concat (mux (eq (extract v_10382 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10382 1 17)) (concat (mux (eq (extract v_10391 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10391 1 17)) (concat (mux (eq (extract v_10400 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10400 1 17)) (concat (mux (eq (extract v_10409 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10409 1 17)) (mux (eq (extract v_10418 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10418 1 17)))))))));
      pure ()
    pat_end
