def vperm2i1281 : instruction :=
  definst "vperm2i128" $ do
    pattern fun (v_2947 : imm int) (v_2951 : reg (bv 256)) (v_2952 : reg (bv 256)) (v_2953 : reg (bv 256)) => do
      v_8307 <- eval (handleImmediateWithSignExtend v_2947 8 8);
      v_8310 <- eval (extract v_8307 2 4);
      v_8312 <- getRegister v_2952;
      v_8313 <- eval (extract v_8312 128 256);
      v_8315 <- eval (extract v_8312 0 128);
      v_8317 <- getRegister v_2951;
      v_8318 <- eval (extract v_8317 128 256);
      v_8319 <- eval (extract v_8317 0 128);
      v_8326 <- eval (extract v_8307 6 8);
      setRegister (lhs.of_reg v_2953) (concat (mux (eq (extract v_8307 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8310 (expression.bv_nat 2 0)) v_8313 (mux (eq v_8310 (expression.bv_nat 2 1)) v_8315 (mux (eq v_8310 (expression.bv_nat 2 2)) v_8318 v_8319)))) (mux (eq (extract v_8307 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8326 (expression.bv_nat 2 0)) v_8313 (mux (eq v_8326 (expression.bv_nat 2 1)) v_8315 (mux (eq v_8326 (expression.bv_nat 2 2)) v_8318 v_8319)))));
      pure ()
    pat_end;
    pattern fun (v_2941 : imm int) (v_2944 : Mem) (v_2945 : reg (bv 256)) (v_2946 : reg (bv 256)) => do
      v_17473 <- eval (handleImmediateWithSignExtend v_2941 8 8);
      v_17476 <- eval (extract v_17473 2 4);
      v_17478 <- getRegister v_2945;
      v_17479 <- eval (extract v_17478 128 256);
      v_17481 <- eval (extract v_17478 0 128);
      v_17483 <- evaluateAddress v_2944;
      v_17484 <- load v_17483 32;
      v_17485 <- eval (extract v_17484 128 256);
      v_17486 <- eval (extract v_17484 0 128);
      v_17493 <- eval (extract v_17473 6 8);
      setRegister (lhs.of_reg v_2946) (concat (mux (eq (extract v_17473 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_17476 (expression.bv_nat 2 0)) v_17479 (mux (eq v_17476 (expression.bv_nat 2 1)) v_17481 (mux (eq v_17476 (expression.bv_nat 2 2)) v_17485 v_17486)))) (mux (eq (extract v_17473 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_17493 (expression.bv_nat 2 0)) v_17479 (mux (eq v_17493 (expression.bv_nat 2 1)) v_17481 (mux (eq v_17493 (expression.bv_nat 2 2)) v_17485 v_17486)))));
      pure ()
    pat_end
