def vcmpss1 : instruction :=
  definst "vcmpss" $ do
    pattern fun (v_2970 : imm int) (v_2974 : reg (bv 128)) (v_2975 : reg (bv 128)) (v_2976 : reg (bv 128)) => do
      v_5729 <- getRegister v_2975;
      v_5732 <- getRegister v_2974;
      setRegister (lhs.of_reg v_2976) (concat (extract v_5729 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5729 96 128) (extract v_5732 96 128) (handleImmediateWithSignExtend v_2970 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2965 : imm int) (v_2964 : Mem) (v_2968 : reg (bv 128)) (v_2969 : reg (bv 128)) => do
      v_10045 <- getRegister v_2968;
      v_10048 <- evaluateAddress v_2964;
      v_10049 <- load v_10048 4;
      setRegister (lhs.of_reg v_2969) (concat (extract v_10045 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_10045 96 128) v_10049 (handleImmediateWithSignExtend v_2965 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end
