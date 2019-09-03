def vcmpps1 : instruction :=
  definst "vcmpps" $ do
    pattern fun (v_2931 : imm int) (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) (v_2937 : reg (bv 128)) => do
      v_5622 <- getRegister v_2936;
      v_5624 <- getRegister v_2935;
      v_5626 <- eval (handleImmediateWithSignExtend v_2931 8 8);
      setRegister (lhs.of_reg v_2937) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5622 0 32) (extract v_5624 0 32) v_5626) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5622 32 64) (extract v_5624 32 64) v_5626) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5622 64 96) (extract v_5624 64 96) v_5626) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5622 96 128) (extract v_5624 96 128) v_5626) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2944 : imm int) (v_2946 : reg (bv 256)) (v_2947 : reg (bv 256)) (v_2948 : reg (bv 256)) => do
      v_5655 <- getRegister v_2947;
      v_5657 <- getRegister v_2946;
      v_5659 <- eval (handleImmediateWithSignExtend v_2944 8 8);
      setRegister (lhs.of_reg v_2948) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 0 32) (extract v_5657 0 32) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 32 64) (extract v_5657 32 64) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 64 96) (extract v_5657 64 96) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 96 128) (extract v_5657 96 128) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 128 160) (extract v_5657 128 160) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 160 192) (extract v_5657 160 192) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 192 224) (extract v_5657 192 224) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5655 224 256) (extract v_5657 224 256) v_5659) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2926 : imm int) (v_2925 : Mem) (v_2929 : reg (bv 128)) (v_2930 : reg (bv 128)) => do
      v_9954 <- getRegister v_2929;
      v_9956 <- evaluateAddress v_2925;
      v_9957 <- load v_9956 16;
      v_9959 <- eval (handleImmediateWithSignExtend v_2926 8 8);
      setRegister (lhs.of_reg v_2930) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9954 0 32) (extract v_9957 0 32) v_9959) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9954 32 64) (extract v_9957 32 64) v_9959) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9954 64 96) (extract v_9957 64 96) v_9959) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9954 96 128) (extract v_9957 96 128) v_9959) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2939 : imm int) (v_2938 : Mem) (v_2940 : reg (bv 256)) (v_2941 : reg (bv 256)) => do
      v_9982 <- getRegister v_2940;
      v_9984 <- evaluateAddress v_2938;
      v_9985 <- load v_9984 32;
      v_9987 <- eval (handleImmediateWithSignExtend v_2939 8 8);
      setRegister (lhs.of_reg v_2941) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 0 32) (extract v_9985 0 32) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 32 64) (extract v_9985 32 64) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 64 96) (extract v_9985 64 96) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 96 128) (extract v_9985 96 128) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 128 160) (extract v_9985 128 160) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 160 192) (extract v_9985 160 192) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 192 224) (extract v_9985 192 224) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9982 224 256) (extract v_9985 224 256) v_9987) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
