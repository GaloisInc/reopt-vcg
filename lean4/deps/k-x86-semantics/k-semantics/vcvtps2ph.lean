def vcvtps2ph : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_6 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      store v_3 (concat (fp_bitcast_to_bv (Float2Half v_5 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_7 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_8 v_6) 16) (fp_bitcast_to_bv (Float2Half v_9 v_6) 16)))) 8;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      setRegister (lhs.of_reg xmm_2) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (Float2Half v_4 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_6 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_7 v_5) 16) (fp_bitcast_to_bv (Float2Half v_8 v_5) 16)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg ymm_1);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_6 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 128 160));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 160 192));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 192 224));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 224 256));
      store v_3 (concat (fp_bitcast_to_bv (Float2Half v_5 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_7 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_8 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_9 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_10 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_11 v_6) 16) (concat (fp_bitcast_to_bv (Float2Half v_12 v_6) 16) (fp_bitcast_to_bv (Float2Half v_13 v_6) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 128 160));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 160 192));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 192 224));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 224 256));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (Float2Half v_4 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_6 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_7 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_8 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_9 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_10 v_5) 16) (concat (fp_bitcast_to_bv (Float2Half v_11 v_5) 16) (fp_bitcast_to_bv (Float2Half v_12 v_5) 16))))))));
      pure ()
    pat_end
