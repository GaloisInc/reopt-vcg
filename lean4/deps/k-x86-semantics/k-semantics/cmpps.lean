def cmpps1 : instruction :=
  definst "cmpps" $ do
    pattern fun (v_3408 : imm int) (v_3409 : reg (bv 128)) (v_3410 : reg (bv 128)) => do
      v_5635 <- getRegister v_3410;
      v_5637 <- getRegister v_3409;
      v_5639 <- eval (handleImmediateWithSignExtend v_3408 8 8);
      setRegister (lhs.of_reg v_3410) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5635 0 32) (extract v_5637 0 32) v_5639) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5635 32 64) (extract v_5637 32 64) v_5639) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5635 64 96) (extract v_5637 64 96) v_5639) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5635 96 128) (extract v_5637 96 128) v_5639) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3404 : imm int) (v_3403 : Mem) (v_3405 : reg (bv 128)) => do
      v_8934 <- getRegister v_3405;
      v_8936 <- evaluateAddress v_3403;
      v_8937 <- load v_8936 16;
      v_8939 <- eval (handleImmediateWithSignExtend v_3404 8 8);
      setRegister (lhs.of_reg v_3405) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8934 0 32) (extract v_8937 0 32) v_8939) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8934 32 64) (extract v_8937 32 64) v_8939) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8934 64 96) (extract v_8937 64 96) v_8939) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8934 96 128) (extract v_8937 96 128) v_8939) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
