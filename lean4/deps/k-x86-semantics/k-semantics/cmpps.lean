def cmpps1 : instruction :=
  definst "cmpps" $ do
    pattern fun (v_3486 : imm int) (v_3487 : reg (bv 128)) (v_3488 : reg (bv 128)) => do
      v_5528 <- getRegister v_3488;
      v_5530 <- getRegister v_3487;
      v_5532 <- eval (handleImmediateWithSignExtend v_3486 8 8);
      setRegister (lhs.of_reg v_3488) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5528 0 32) (extract v_5530 0 32) v_5532) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5528 32 64) (extract v_5530 32 64) v_5532) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5528 64 96) (extract v_5530 64 96) v_5532) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5528 96 128) (extract v_5530 96 128) v_5532) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3481 : imm int) (v_3482 : Mem) (v_3483 : reg (bv 128)) => do
      v_8623 <- getRegister v_3483;
      v_8625 <- evaluateAddress v_3482;
      v_8626 <- load v_8625 16;
      v_8628 <- eval (handleImmediateWithSignExtend v_3481 8 8);
      setRegister (lhs.of_reg v_3483) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8623 0 32) (extract v_8626 0 32) v_8628) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8623 32 64) (extract v_8626 32 64) v_8628) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8623 64 96) (extract v_8626 64 96) v_8628) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8623 96 128) (extract v_8626 96 128) v_8628) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
