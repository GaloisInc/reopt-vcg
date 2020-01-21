def vcvtps2dq : instruction :=
  definst "vcvtps2dq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 96 128)))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      setRegister (lhs.of_reg ymm_1) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_3 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 96 128)))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg ymm_1) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_2 224 256)))))))));
      pure ()
    pat_end
