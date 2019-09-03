def psignw1 : instruction :=
  definst "psignw" $ do
    pattern fun (v_2964 : reg (bv 128)) (v_2965 : reg (bv 128)) => do
      v_7454 <- getRegister v_2964;
      v_7455 <- eval (extract v_7454 0 16);
      v_7457 <- getRegister v_2965;
      v_7458 <- eval (extract v_7457 0 16);
      v_7464 <- eval (extract v_7454 16 32);
      v_7466 <- eval (extract v_7457 16 32);
      v_7472 <- eval (extract v_7454 32 48);
      v_7474 <- eval (extract v_7457 32 48);
      v_7480 <- eval (extract v_7454 48 64);
      v_7482 <- eval (extract v_7457 48 64);
      v_7488 <- eval (extract v_7454 64 80);
      v_7490 <- eval (extract v_7457 64 80);
      v_7496 <- eval (extract v_7454 80 96);
      v_7498 <- eval (extract v_7457 80 96);
      v_7504 <- eval (extract v_7454 96 112);
      v_7506 <- eval (extract v_7457 96 112);
      v_7512 <- eval (extract v_7454 112 128);
      v_7514 <- eval (extract v_7457 112 128);
      setRegister (lhs.of_reg v_2965) (concat (mux (sgt v_7455 (expression.bv_nat 16 0)) v_7458 (mux (eq v_7455 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7458 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7464 (expression.bv_nat 16 0)) v_7466 (mux (eq v_7464 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7466 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7472 (expression.bv_nat 16 0)) v_7474 (mux (eq v_7472 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7474 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7480 (expression.bv_nat 16 0)) v_7482 (mux (eq v_7480 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7482 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7488 (expression.bv_nat 16 0)) v_7490 (mux (eq v_7488 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7490 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7496 (expression.bv_nat 16 0)) v_7498 (mux (eq v_7496 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7498 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7504 (expression.bv_nat 16 0)) v_7506 (mux (eq v_7504 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7506 (expression.bv_nat 16 65535))))) (mux (sgt v_7512 (expression.bv_nat 16 0)) v_7514 (mux (eq v_7512 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7514 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2960 : Mem) (v_2961 : reg (bv 128)) => do
      v_14334 <- evaluateAddress v_2960;
      v_14335 <- load v_14334 16;
      v_14336 <- eval (extract v_14335 0 16);
      v_14338 <- getRegister v_2961;
      v_14339 <- eval (extract v_14338 0 16);
      v_14345 <- eval (extract v_14335 16 32);
      v_14347 <- eval (extract v_14338 16 32);
      v_14353 <- eval (extract v_14335 32 48);
      v_14355 <- eval (extract v_14338 32 48);
      v_14361 <- eval (extract v_14335 48 64);
      v_14363 <- eval (extract v_14338 48 64);
      v_14369 <- eval (extract v_14335 64 80);
      v_14371 <- eval (extract v_14338 64 80);
      v_14377 <- eval (extract v_14335 80 96);
      v_14379 <- eval (extract v_14338 80 96);
      v_14385 <- eval (extract v_14335 96 112);
      v_14387 <- eval (extract v_14338 96 112);
      v_14393 <- eval (extract v_14335 112 128);
      v_14395 <- eval (extract v_14338 112 128);
      setRegister (lhs.of_reg v_2961) (concat (mux (sgt v_14336 (expression.bv_nat 16 0)) v_14339 (mux (eq v_14336 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14339 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14345 (expression.bv_nat 16 0)) v_14347 (mux (eq v_14345 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14347 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14353 (expression.bv_nat 16 0)) v_14355 (mux (eq v_14353 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14355 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14361 (expression.bv_nat 16 0)) v_14363 (mux (eq v_14361 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14363 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14369 (expression.bv_nat 16 0)) v_14371 (mux (eq v_14369 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14371 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14377 (expression.bv_nat 16 0)) v_14379 (mux (eq v_14377 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14379 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14385 (expression.bv_nat 16 0)) v_14387 (mux (eq v_14385 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14387 (expression.bv_nat 16 65535))))) (mux (sgt v_14393 (expression.bv_nat 16 0)) v_14395 (mux (eq v_14393 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14395 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end
