def vperm2f1281 : instruction :=
  definst "vperm2f128" $ do
    pattern fun (v_2934 : imm int) (v_2938 : reg (bv 256)) (v_2939 : reg (bv 256)) (v_2940 : reg (bv 256)) => do
      v_8272 <- eval (handleImmediateWithSignExtend v_2934 8 8);
      v_8275 <- eval (extract v_8272 2 4);
      v_8277 <- getRegister v_2939;
      v_8278 <- eval (extract v_8277 128 256);
      v_8280 <- eval (extract v_8277 0 128);
      v_8282 <- getRegister v_2938;
      v_8283 <- eval (extract v_8282 128 256);
      v_8284 <- eval (extract v_8282 0 128);
      v_8291 <- eval (extract v_8272 6 8);
      setRegister (lhs.of_reg v_2940) (concat (mux (eq (extract v_8272 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8275 (expression.bv_nat 2 0)) v_8278 (mux (eq v_8275 (expression.bv_nat 2 1)) v_8280 (mux (eq v_8275 (expression.bv_nat 2 2)) v_8283 v_8284)))) (mux (eq (extract v_8272 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8291 (expression.bv_nat 2 0)) v_8278 (mux (eq v_8291 (expression.bv_nat 2 1)) v_8280 (mux (eq v_8291 (expression.bv_nat 2 2)) v_8283 v_8284)))));
      pure ()
    pat_end;
    pattern fun (v_2928 : imm int) (v_2931 : Mem) (v_2932 : reg (bv 256)) (v_2933 : reg (bv 256)) => do
      v_17443 <- eval (handleImmediateWithSignExtend v_2928 8 8);
      v_17446 <- eval (extract v_17443 2 4);
      v_17448 <- getRegister v_2932;
      v_17449 <- eval (extract v_17448 128 256);
      v_17451 <- eval (extract v_17448 0 128);
      v_17453 <- evaluateAddress v_2931;
      v_17454 <- load v_17453 32;
      v_17455 <- eval (extract v_17454 128 256);
      v_17456 <- eval (extract v_17454 0 128);
      v_17463 <- eval (extract v_17443 6 8);
      setRegister (lhs.of_reg v_2933) (concat (mux (eq (extract v_17443 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_17446 (expression.bv_nat 2 0)) v_17449 (mux (eq v_17446 (expression.bv_nat 2 1)) v_17451 (mux (eq v_17446 (expression.bv_nat 2 2)) v_17455 v_17456)))) (mux (eq (extract v_17443 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_17463 (expression.bv_nat 2 0)) v_17449 (mux (eq v_17463 (expression.bv_nat 2 1)) v_17451 (mux (eq v_17463 (expression.bv_nat 2 2)) v_17455 v_17456)))));
      pure ()
    pat_end
