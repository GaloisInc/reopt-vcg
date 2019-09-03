def cmpps1 : instruction :=
  definst "cmpps" $ do
    pattern fun (v_3396 : imm int) (v_3398 : reg (bv 128)) (v_3399 : reg (bv 128)) => do
      v_5662 <- getRegister v_3399;
      v_5664 <- getRegister v_3398;
      v_5666 <- eval (handleImmediateWithSignExtend v_3396 8 8);
      setRegister (lhs.of_reg v_3399) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5662 0 32) (extract v_5664 0 32) v_5666) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5662 32 64) (extract v_5664 32 64) v_5666) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5662 64 96) (extract v_5664 64 96) v_5666) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5662 96 128) (extract v_5664 96 128) v_5666) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3391 : imm int) (v_3392 : Mem) (v_3393 : reg (bv 128)) => do
      v_8993 <- getRegister v_3393;
      v_8995 <- evaluateAddress v_3392;
      v_8996 <- load v_8995 16;
      v_8998 <- eval (handleImmediateWithSignExtend v_3391 8 8);
      setRegister (lhs.of_reg v_3393) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8993 0 32) (extract v_8996 0 32) v_8998) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8993 32 64) (extract v_8996 32 64) v_8998) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8993 64 96) (extract v_8996 64 96) v_8998) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8993 96 128) (extract v_8996 96 128) v_8998) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
