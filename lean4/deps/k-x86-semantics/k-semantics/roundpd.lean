def roundpd : instruction :=
  definst "roundpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 16;
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_4 0 64) v_5) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_4 64 128) v_5));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_3 0 64) v_4) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_3 64 128) v_4));
      pure ()
    pat_end
