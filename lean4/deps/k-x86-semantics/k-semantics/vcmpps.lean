def vcmpps1 : instruction :=
  definst "vcmpps" $ do
    pattern fun (v_2997 : imm int) (v_2999 : reg (bv 128)) (v_3000 : reg (bv 128)) (v_3001 : reg (bv 128)) => do
      v_5550 <- getRegister v_3000;
      v_5552 <- getRegister v_2999;
      v_5554 <- eval (handleImmediateWithSignExtend v_2997 8 8);
      setRegister (lhs.of_reg v_3001) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5550 0 32) (extract v_5552 0 32) v_5554) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5550 32 64) (extract v_5552 32 64) v_5554) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5550 64 96) (extract v_5552 64 96) v_5554) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5550 96 128) (extract v_5552 96 128) v_5554) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3010 : imm int) (v_3011 : reg (bv 256)) (v_3012 : reg (bv 256)) (v_3013 : reg (bv 256)) => do
      v_5583 <- getRegister v_3012;
      v_5585 <- getRegister v_3011;
      v_5587 <- eval (handleImmediateWithSignExtend v_3010 8 8);
      setRegister (lhs.of_reg v_3013) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 0 32) (extract v_5585 0 32) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 32 64) (extract v_5585 32 64) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 64 96) (extract v_5585 64 96) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 96 128) (extract v_5585 96 128) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 128 160) (extract v_5585 128 160) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 160 192) (extract v_5585 160 192) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 192 224) (extract v_5585 192 224) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5583 224 256) (extract v_5585 224 256) v_5587) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2991 : imm int) (v_2992 : Mem) (v_2993 : reg (bv 128)) (v_2994 : reg (bv 128)) => do
      v_9722 <- getRegister v_2993;
      v_9724 <- evaluateAddress v_2992;
      v_9725 <- load v_9724 16;
      v_9727 <- eval (handleImmediateWithSignExtend v_2991 8 8);
      setRegister (lhs.of_reg v_2994) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9722 0 32) (extract v_9725 0 32) v_9727) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9722 32 64) (extract v_9725 32 64) v_9727) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9722 64 96) (extract v_9725 64 96) v_9727) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9722 96 128) (extract v_9725 96 128) v_9727) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3004 : imm int) (v_3005 : Mem) (v_3006 : reg (bv 256)) (v_3007 : reg (bv 256)) => do
      v_9750 <- getRegister v_3006;
      v_9752 <- evaluateAddress v_3005;
      v_9753 <- load v_9752 32;
      v_9755 <- eval (handleImmediateWithSignExtend v_3004 8 8);
      setRegister (lhs.of_reg v_3007) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 0 32) (extract v_9753 0 32) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 32 64) (extract v_9753 32 64) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 64 96) (extract v_9753 64 96) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 96 128) (extract v_9753 96 128) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 128 160) (extract v_9753 128 160) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 160 192) (extract v_9753 160 192) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 192 224) (extract v_9753 192 224) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9750 224 256) (extract v_9753 224 256) v_9755) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
