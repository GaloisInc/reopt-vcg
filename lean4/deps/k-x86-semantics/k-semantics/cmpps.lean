def cmpps1 : instruction :=
  definst "cmpps" $ do
    pattern fun (v_3459 : imm int) (v_3460 : reg (bv 128)) (v_3461 : reg (bv 128)) => do
      v_5648 <- getRegister v_3461;
      v_5650 <- getRegister v_3460;
      v_5652 <- eval (handleImmediateWithSignExtend v_3459 8 8);
      setRegister (lhs.of_reg v_3461) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5648 0 32) (extract v_5650 0 32) v_5652) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5648 32 64) (extract v_5650 32 64) v_5652) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5648 64 96) (extract v_5650 64 96) v_5652) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5648 96 128) (extract v_5650 96 128) v_5652) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3454 : imm int) (v_3455 : Mem) (v_3456 : reg (bv 128)) => do
      v_8915 <- getRegister v_3456;
      v_8917 <- evaluateAddress v_3455;
      v_8918 <- load v_8917 16;
      v_8920 <- eval (handleImmediateWithSignExtend v_3454 8 8);
      setRegister (lhs.of_reg v_3456) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8915 0 32) (extract v_8918 0 32) v_8920) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8915 32 64) (extract v_8918 32 64) v_8920) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8915 64 96) (extract v_8918 64 96) v_8920) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_8915 96 128) (extract v_8918 96 128) v_8920) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
