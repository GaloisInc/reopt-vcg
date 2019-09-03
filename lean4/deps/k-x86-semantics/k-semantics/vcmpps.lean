def vcmpps1 : instruction :=
  definst "vcmpps" $ do
    pattern fun (v_2944 : imm int) (v_2948 : reg (bv 128)) (v_2949 : reg (bv 128)) (v_2950 : reg (bv 128)) => do
      v_6081 <- getRegister v_2949;
      v_6083 <- getRegister v_2948;
      v_6085 <- eval (handleImmediateWithSignExtend v_2944 8 8);
      setRegister (lhs.of_reg v_2950) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6081 0 32) (extract v_6083 0 32) v_6085) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6081 32 64) (extract v_6083 32 64) v_6085) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6081 64 96) (extract v_6083 64 96) v_6085) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6081 96 128) (extract v_6083 96 128) v_6085) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2957 : imm int) (v_2958 : reg (bv 256)) (v_2959 : reg (bv 256)) (v_2960 : reg (bv 256)) => do
      v_6114 <- getRegister v_2959;
      v_6116 <- getRegister v_2958;
      v_6118 <- eval (handleImmediateWithSignExtend v_2957 8 8);
      setRegister (lhs.of_reg v_2960) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 0 32) (extract v_6116 0 32) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 32 64) (extract v_6116 32 64) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 64 96) (extract v_6116 64 96) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 96 128) (extract v_6116 96 128) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 128 160) (extract v_6116 128 160) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 160 192) (extract v_6116 160 192) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 192 224) (extract v_6116 192 224) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6114 224 256) (extract v_6116 224 256) v_6118) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2939 : imm int) (v_2938 : Mem) (v_2942 : reg (bv 128)) (v_2943 : reg (bv 128)) => do
      v_11496 <- getRegister v_2942;
      v_11498 <- evaluateAddress v_2938;
      v_11499 <- load v_11498 16;
      v_11501 <- eval (handleImmediateWithSignExtend v_2939 8 8);
      setRegister (lhs.of_reg v_2943) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11496 0 32) (extract v_11499 0 32) v_11501) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11496 32 64) (extract v_11499 32 64) v_11501) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11496 64 96) (extract v_11499 64 96) v_11501) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11496 96 128) (extract v_11499 96 128) v_11501) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2952 : imm int) (v_2951 : Mem) (v_2953 : reg (bv 256)) (v_2954 : reg (bv 256)) => do
      v_11524 <- getRegister v_2953;
      v_11526 <- evaluateAddress v_2951;
      v_11527 <- load v_11526 32;
      v_11529 <- eval (handleImmediateWithSignExtend v_2952 8 8);
      setRegister (lhs.of_reg v_2954) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 0 32) (extract v_11527 0 32) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 32 64) (extract v_11527 32 64) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 64 96) (extract v_11527 64 96) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 96 128) (extract v_11527 96 128) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 128 160) (extract v_11527 128 160) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 160 192) (extract v_11527 160 192) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 192 224) (extract v_11527 192 224) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11524 224 256) (extract v_11527 224 256) v_11529) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
