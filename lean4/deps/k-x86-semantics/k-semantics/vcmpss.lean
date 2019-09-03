def vcmpss1 : instruction :=
  definst "vcmpss" $ do
    pattern fun (v_2983 : imm int) (v_2987 : reg (bv 128)) (v_2988 : reg (bv 128)) (v_2989 : reg (bv 128)) => do
      v_6188 <- getRegister v_2988;
      v_6191 <- getRegister v_2987;
      setRegister (lhs.of_reg v_2989) (concat (extract v_6188 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_6188 96 128) (extract v_6191 96 128) (handleImmediateWithSignExtend v_2983 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2978 : imm int) (v_2977 : Mem) (v_2981 : reg (bv 128)) (v_2982 : reg (bv 128)) => do
      v_11587 <- getRegister v_2981;
      v_11590 <- evaluateAddress v_2977;
      v_11591 <- load v_11590 4;
      setRegister (lhs.of_reg v_2982) (concat (extract v_11587 0 96) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_11587 96 128) v_11591 (handleImmediateWithSignExtend v_2978 8 8)) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)));
      pure ()
    pat_end
