def roundps1 : instruction :=
  definst "roundps" $ do
    pattern fun (v_2884 : imm int) (v_2886 : reg (bv 128)) (v_2887 : reg (bv 128)) => do
      v_5510 <- getRegister v_2886;
      v_5512 <- eval (handleImmediateWithSignExtend v_2884 8 8);
      setRegister (lhs.of_reg v_2887) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5510 0 32) v_5512) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5510 32 64) v_5512) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5510 64 96) v_5512) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5510 96 128) v_5512))));
      pure ()
    pat_end;
    pattern fun (v_2879 : imm int) (v_2880 : Mem) (v_2881 : reg (bv 128)) => do
      v_11268 <- evaluateAddress v_2880;
      v_11269 <- load v_11268 16;
      v_11271 <- eval (handleImmediateWithSignExtend v_2879 8 8);
      setRegister (lhs.of_reg v_2881) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_11269 0 32) v_11271) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_11269 32 64) v_11271) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_11269 64 96) v_11271) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_11269 96 128) v_11271))));
      pure ()
    pat_end
