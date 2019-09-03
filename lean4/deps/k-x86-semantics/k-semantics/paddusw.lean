def paddusw1 : instruction :=
  definst "paddusw" $ do
    pattern fun (v_3177 : reg (bv 128)) (v_3178 : reg (bv 128)) => do
      v_6253 <- getRegister v_3178;
      v_6256 <- getRegister v_3177;
      v_6259 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 0 16)) (concat (expression.bv_nat 1 0) (extract v_6256 0 16)));
      v_6268 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 16 32)) (concat (expression.bv_nat 1 0) (extract v_6256 16 32)));
      v_6277 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 32 48)) (concat (expression.bv_nat 1 0) (extract v_6256 32 48)));
      v_6286 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 48 64)) (concat (expression.bv_nat 1 0) (extract v_6256 48 64)));
      v_6295 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 64 80)) (concat (expression.bv_nat 1 0) (extract v_6256 64 80)));
      v_6304 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 80 96)) (concat (expression.bv_nat 1 0) (extract v_6256 80 96)));
      v_6313 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 96 112)) (concat (expression.bv_nat 1 0) (extract v_6256 96 112)));
      v_6322 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6253 112 128)) (concat (expression.bv_nat 1 0) (extract v_6256 112 128)));
      setRegister (lhs.of_reg v_3178) (concat (mux (eq (extract v_6259 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6259 1 17)) (concat (mux (eq (extract v_6268 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6268 1 17)) (concat (mux (eq (extract v_6277 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6277 1 17)) (concat (mux (eq (extract v_6286 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6286 1 17)) (concat (mux (eq (extract v_6295 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6295 1 17)) (concat (mux (eq (extract v_6304 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6304 1 17)) (concat (mux (eq (extract v_6313 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6313 1 17)) (mux (eq (extract v_6322 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_6322 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_3173 : Mem) (v_3174 : reg (bv 128)) => do
      v_10319 <- getRegister v_3174;
      v_10322 <- evaluateAddress v_3173;
      v_10323 <- load v_10322 16;
      v_10326 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 0 16)) (concat (expression.bv_nat 1 0) (extract v_10323 0 16)));
      v_10335 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 16 32)) (concat (expression.bv_nat 1 0) (extract v_10323 16 32)));
      v_10344 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 32 48)) (concat (expression.bv_nat 1 0) (extract v_10323 32 48)));
      v_10353 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 48 64)) (concat (expression.bv_nat 1 0) (extract v_10323 48 64)));
      v_10362 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 64 80)) (concat (expression.bv_nat 1 0) (extract v_10323 64 80)));
      v_10371 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 80 96)) (concat (expression.bv_nat 1 0) (extract v_10323 80 96)));
      v_10380 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 96 112)) (concat (expression.bv_nat 1 0) (extract v_10323 96 112)));
      v_10389 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10319 112 128)) (concat (expression.bv_nat 1 0) (extract v_10323 112 128)));
      setRegister (lhs.of_reg v_3174) (concat (mux (eq (extract v_10326 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10326 1 17)) (concat (mux (eq (extract v_10335 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10335 1 17)) (concat (mux (eq (extract v_10344 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10344 1 17)) (concat (mux (eq (extract v_10353 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10353 1 17)) (concat (mux (eq (extract v_10362 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10362 1 17)) (concat (mux (eq (extract v_10371 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10371 1 17)) (concat (mux (eq (extract v_10380 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10380 1 17)) (mux (eq (extract v_10389 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_10389 1 17)))))))));
      pure ()
    pat_end
